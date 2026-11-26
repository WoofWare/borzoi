//! Parser for MSBuild `.fsproj` files, narrowly scoped to extracting the
//! source-file compile order an F# project would feed to the compiler.
//!
//! See `docs/completed/fsproj-parser-plan.md` for design rationale. This module
//! implements phases 1–3: a two-pass evaluation (properties finalise
//! before any item evaluates, matching MSBuild's pass ordering) that
//! pulls out
//! `<Compile>` / `<CompileBefore>` / `<CompileAfter>` items, applies
//! F#'s `CompileOrder` metadata ordering, evaluates
//! `<PropertyGroup>` writes with `$(Name)` substitution, and gates
//! every condition-bearing construct on the subset of `Condition`
//! syntax described in plan D5 (string equality with `==` / `!=`,
//! `And` / `Or`, parens, `true` / `false`, plus `$(...)` substitution
//! inside string literals). It does NOT expand globs, does NOT follow
//! `<Import>`, does NOT model property functions
//! (`$([Type]::Method(...))`), and does NOT resolve item-list or
//! metadata references. Anything we'd need one of those for emits a
//! [`Diagnostic`] and sets [`ParsedProject::is_partial`].

// `document`'s self-reference is `self_cell`'s; nothing here needs its own.
#![forbid(unsafe_code)]

mod condition;
mod cost;
mod diagnostic;
pub mod document;
mod dotnet_io;
mod evaluator;
pub mod fsc;
mod glob;
pub mod glob_resolver;
mod imports;
pub mod observed;
mod project_file;
mod properties;
mod sdk_resolver;
mod target_frameworks;

#[cfg(feature = "test-support")]
pub mod test_support;

pub use diagnostic::{
    CompileConditionReason, CompileConditionUncertainty, CompileItemUncertaintyCause,
    CompileItemUncertaintyCauseKind, DefineConstantsUncertaintyCause,
    DefineConstantsUncertaintyCauseKind, Diagnostic, DiagnosticKind, DiagnosticOrigin,
    ImplicitImportKind, ImportFailReason, LoadTimeError, PackageReferenceUncertaintyCause,
    PackageReferenceUncertaintyCauseKind, Rejection, RejectionCause, RejectionCertainty,
    StructuralCompileItemUncertainty, StructuralPackageReferenceUncertainty, UnloadableImport,
};
pub use evaluator::property_reads::{InexactUnset, PropertyRead, PropertyReads};
pub use glob::{GlobDecline, SpecFragment, Unmodelled};
pub use imports::detect_implicit_imports;
/// Escape text that entered from *outside* MSBuild's escaped-value domain — a
/// filesystem path, a computed toolset seed — so that seeding it as a property
/// value (which the evaluator unescapes on use) round-trips to the literal.
/// MSBuild does exactly this when it seeds its toolset paths. A host that
/// derives a computed property (e.g. `MSBuildUserExtensionsPath`) and hands it
/// to [`parse_fsproj_with_imports`] through the `environment` map must escape it
/// this way, or a `%`/`;`/`(` in the path would be mis-decoded.
pub use project_file::{ProjectFile, ProjectFileError};
pub use properties::escaping::escape;
pub use properties::trust::UntrustedCause;
pub use sdk_resolver::global_json::{
    GlobalJson, GlobalJsonError, GlobalJsonSettings, GlobalJsonWorkloads, SdkPathEntry,
    UndecidedGlobalJson, find_global_json, parse_global_json,
};
pub use sdk_resolver::version_spec::{RollForward, VersionSpec};
pub use sdk_resolver::{
    SdkResolveError, SdkVersion, locate_dotnet_sdk, nuget_package_version, resolve_sdk,
    running_sdk_dir, workloads,
};
pub use target_frameworks::target_frameworks;

/// MSBuild's boolean vocabulary (`ConversionUtilities.TryConvertStringToBool`):
/// `true`/`on`/`yes` and `false`/`off`/`no`, each optionally negated with a
/// leading `!`, all case-insensitive — anything else (including `"0"`/`"1"`
/// and whitespace-padded spellings; the conversion does not trim) is `None`.
///
/// This is the comparison the SDK's P2P protocol applies to
/// `ReferenceOutputAssembly`: the common targets admit a reference's output
/// onto `ReferencePath` only under `'%(ReferenceOutputAssembly)'=='true'`,
/// and MSBuild `==` coerces both sides through this vocabulary before
/// falling back to string equality. Probed (dotnet 10.0.301, 2026-07-10,
/// prebuilt target, entry edge): `on`/`yes`/`!false`/`TRUE` keep the DLL on
/// `ReferencePath`; `0`/`1`/`off`/`no`/`" true "`/`" false "` remove it.
pub fn msbuild_boolean(value: &str) -> Option<bool> {
    condition::parse_msbuild_bool(value)
}

use borzoi_verdict::Verdict;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::error::Error;
use std::fmt;
use std::ops::Range;
use std::path::{Path, PathBuf};

/// The on-disk files an MSBuild SDK contributes to a project: the
/// `Sdk.props` MSBuild imports before the project body, the
/// `Sdk.targets` it imports after, and the directory those two live in
/// (used to resolve custom entry points like `Sdk.Web.props`). Returned
/// from an SDK resolver supplied to [`parse_fsproj_with_imports`].
///
/// `props` and `targets` are required: real .NET SDKs
/// (`Microsoft.NET.Sdk`, the Web/Worker variants, …) all ship both,
/// and a custom SDK that doesn't can point one at an empty
/// `<Project/>` stub.
///
/// `root` is the directory the walker resolves
/// `<Import Sdk="X" Project="Sdk.Web.props"/>`-style custom entry
/// points against (only `Project` values other than the two well-known
/// stems hit this path; `Sdk.props` / `Sdk.targets` always use the
/// explicit fields). By convention `root` is the directory containing
/// both well-known files, but the contract is just "the SDK's
/// import-root for custom entry points" — a resolver is free to point
/// it elsewhere as long as the relative paths in the importing fsproj
/// make sense against it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SdkPaths {
    pub root: PathBuf,
    pub props: PathBuf,
    pub targets: PathBuf,
}

/// What an SDK identifier resolved to. Mirrors MSBuild's own resolver
/// contract, where an SDK resolver returns a *list* of paths and
/// `<Import Project="P" Sdk="S"/>` imports `P` relative to each.
///
/// Ordinary on-disk SDKs are [`SdkResolution::Single`]: exactly one
/// root, with the two well-known entry points the `<Project Sdk="…">`
/// shorthand needs. Resolver-backed locator SDKs — today the workload
/// locators `Microsoft.NET.SDK.WorkloadManifestTargetsLocator` /
/// `Microsoft.NET.SDK.WorkloadAutoImportPropsLocator` — are
/// [`SdkResolution::Roots`]: zero or more roots, in import order, each
/// of which the import's `Project` is resolved against (zero roots
/// means the import cleanly contributes nothing, exactly as MSBuild
/// treats an empty workload-resolver result). `Roots` carries no
/// `Sdk.props`/`Sdk.targets` entry points, so it cannot back the
/// `<Project Sdk="…">` shorthand — the walker degrades if a project
/// tries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SdkResolution {
    /// An ordinary SDK: one root plus its canonical entry points.
    Single(SdkPaths),
    /// A locator-style SDK: `Project` resolves against each root in
    /// order; empty means "nothing to import" (not an error).
    Roots(Vec<PathBuf>),
}

impl From<SdkPaths> for SdkResolution {
    fn from(paths: SdkPaths) -> Self {
        SdkResolution::Single(paths)
    }
}

/// Resolver function the caller hands [`parse_fsproj_with_imports`] to
/// turn an SDK identifier (e.g. `"Microsoft.NET.Sdk"`) into its on-disk
/// [`SdkResolution`]. The walker dispatches on the [`SdkResolveError`]
/// variant:
///
/// - `Err(SdkResolveError::NotFound)` →
///   [`DiagnosticKind::SdkNotFound`]: the user named an SDK that
///   isn't installed (or whose well-known files aren't where we
///   expected). Remediation: install it / check the spelling.
/// - `Err(SdkResolveError::VersionNotSatisfied { .. })` →
///   [`DiagnosticKind::SdkVersionNotSatisfied`]: the SDK exists but
///   the version constraint from `global.json` (or an MSBuild
///   `Sdk="Name/Version"` pin) admits none of the installed
///   versions. Remediation: install a matching version, or relax
///   the constraint.
/// - `Err(SdkResolveError::UnsupportedLayout { .. })` →
///   [`DiagnosticKind::SdkResolutionUnsupported`]: the SDK is a
///   resolver-backed locator whose on-disk state is outside the
///   layout envelope we can resolve exactly (workload sets, install
///   state, ambiguous manifest versions, …). Remediation: none —
///   this is the deliberate "degrade, don't guess" path.
///
/// In all error cases the walker walks the body without the SDK's files, so
/// it reaches none of the SDK's `Directory.Build.*` import points, and
/// `is_partial` flips.
///
/// Locating SDKs requires knowing `$DOTNET_ROOT` (or running MSBuild's
/// own SDK resolver), which is policy the parser stays out of — see
/// the gospel "dependency rejection" principle. The shell decides
/// where SDKs come from; the parser only consumes the result.
///
/// The resolver is handed the evaluation's [`observed::Observer`], and must
/// make every file-system query through it (the crate's own resolvers, such
/// as [`resolve_sdk`], take it as an argument), so that the queries land in
/// [`ParsedProject::read_set`].
pub type SdkResolver<'r> =
    dyn Fn(&str, &observed::Observer) -> Result<SdkResolution, SdkResolveError> + 'r;

/// A request to expand one `<Compile>` / `<ProjectReference>` element's
/// file set, handed to a caller-supplied [`GlobResolver`].
///
/// The evaluator routes an element through the resolver when its
/// `Include` (after `$(...)` expansion) contains an MSBuild wildcard
/// (`*`, `?`, `**`) or when it carries an `Exclude` attribute. Item-list
/// (`@(...)`) and metadata (`%(...)`) references are *not* the resolver's
/// concern: the evaluator diagnoses and strips them before building the
/// request, so `include` and `excludes` only ever contain literal or
/// wildcard path fragments.
///
/// Both lists are already split, and still escaped ([`SpecFragment`]): the
/// split and each fragment's glob-or-literal classification are MSBuild's,
/// made on escaped text, and the resolver decodes each fragment only at its
/// own point of use. So an escaped `%3b` never splits a fragment and an
/// escaped `%2a` never becomes a wildcard in a literal one.
pub struct GlobRequest<'a> {
    /// The entry project's directory — the base every relative fragment
    /// resolves against (MSBuild resolves item includes relative to
    /// `$(MSBuildProjectDirectory)`, even inside imported files). Always
    /// absolute: the directory of the entry [`ProjectFile`]'s full path.
    pub base_dir: &'a Path,
    /// The surviving `Include` fragments in document order,
    /// `$(...)`-expanded, with `@()`/`%()` references removed. May name
    /// files that do not exist (MSBuild passes literal includes through
    /// regardless); the resolver decides.
    pub include: &'a [SpecFragment],
    /// The `Exclude` fragments, `$(...)`-expanded, in document order. Empty
    /// when the element has no `Exclude`. Applies to literal and wildcard
    /// includes alike, though not identically: see
    /// [`SpecFragment::excludes_from_globs`].
    pub excludes: &'a [SpecFragment],
    /// The evaluation's observer, through which the resolver makes every
    /// file-system query (see [`SdkResolver`]).
    pub observer: &'a observed::Observer,
}

/// Resolver function the caller hands [`parse_fsproj_with_imports`] to
/// expand globbing / excluding item elements into concrete files.
///
/// Returns the final, ordered list of absolute paths to splice as items
/// — each already joined onto [`GlobRequest::base_dir`], with excludes
/// applied and ordering finalised (F# compile order is load-bearing, so
/// the resolver owns the order, and it must be MSBuild's). An empty result
/// means the element contributed no files; the evaluator emits no
/// diagnostic for that (MSBuild is silent when a glob matches nothing).
/// A [`GlobDecline`] means the resolver cannot reproduce MSBuild's list:
/// the evaluator records [`DiagnosticKind::GlobDeclined`] and marks the
/// item set uncertain rather than splice a guess.
///
/// Expanding globs requires touching the filesystem (and matching
/// MSBuild's `FileMatcher` semantics), which is policy the parser stays
/// out of — see the gospel "dependency rejection" principle. The
/// filesystem-backed implementation is [`glob_resolver::resolve`]; the
/// evaluator still only ever sees it as this parameter. When the caller
/// supplies no resolver, a wildcard `Include` surfaces as
/// [`DiagnosticKind::UnsupportedGlob`] and an `Exclude` as
/// [`DiagnosticKind::UnsupportedItemOperation`] (the phase-8 behaviour).
pub type GlobResolver<'r> = dyn Fn(&GlobRequest<'_>) -> Result<Vec<PathBuf>, GlobDecline> + 'r;

/// Which item element produced a [`ResolvedItem`]. This is provenance, not
/// the whole ordering model: F#'s effective source order also considers
/// `CompileOrder` metadata on `<Compile>` items. `ProjectReference` lives on
/// its own bucket at [`ParsedProject::project_references`] and is *not* mixed
/// into `items` (it represents an inter-project dependency, not a Compile
/// input).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ItemKind {
    Compile,
    CompileBefore,
    CompileAfter,
    ProjectReference,
}

/// The resolution of one string-valued item metadatum (attribute plus child
/// elements, last applicable write wins).
///
/// The distinction between [`ItemMetadataValue::Known`] and
/// [`ItemMetadataValue::Unknown`] is load-bearing for consumers that make
/// *decisions* on metadata (the LSP's compile-closure walk): a write whose
/// applicability or value this evaluator cannot pin down (an unsupported
/// `Condition`, a `$(...)` expansion issue, an `@(...)`/`%(...)` reference)
/// may well take effect in the real build, so treating it as "absent" would
/// let the walk keep an edge MSBuild drops. `Unknown` forces the consumer to
/// choose a conservative reading instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ItemMetadataValue {
    /// Every potentially-applicable write evaluated cleanly; this is the
    /// effective value. `None` means unset, written empty, or cleared —
    /// MSBuild's `%()` reads `""` for all three.
    Known(Option<String>),
    /// The last potentially-applicable write could not be evaluated, so the
    /// real build's effective value is unknowable here. (A later write that
    /// evaluates cleanly overwrites whatever the unevaluable one did, so it
    /// restores `Known`.)
    Unknown,
}

impl ItemMetadataValue {
    /// Shorthand for `Known(Some(value))` — the shape almost every test
    /// expectation takes.
    pub fn known(value: impl Into<String>) -> Self {
        ItemMetadataValue::Known(Some(value.into()))
    }

    /// The known-absent resolution (`Known(None)`).
    pub const ABSENT: ItemMetadataValue = ItemMetadataValue::Known(None);
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedItem {
    pub kind: ItemKind,
    /// `Include` value joined onto the project directory, as MSBuild's
    /// `FullPath` metadatum gives it: backslashes in the original attribute
    /// read as forward slashes, then `.` segments dropped, runs of
    /// separators collapsed and each `..` taking the segment before it,
    /// lexically (no filesystem touch, so no symlink is resolved). A
    /// trailing separator is kept. That is the rule on a Unix host; on
    /// Windows, whose `GetFullPath` this crate does not model, the joined
    /// path is kept as it is.
    pub include: PathBuf,
    /// `ReferenceOutputAssembly` metadata (attribute or child element),
    /// `$(...)`-expanded, kept raw. Only populated for
    /// [`ItemKind::ProjectReference`] items — MSBuild treats a (trimmed,
    /// case-insensitive) `false` as "build dependency only": the target is
    /// built but its output never reaches the compiler's reference path.
    pub reference_output_assembly: ItemMetadataValue,
    /// `ExcludeAssets` metadata (attribute or child element),
    /// `$(...)`-expanded, kept raw (a `;`-separated asset-kind list, as on
    /// [`PackageReference`]). Only populated for
    /// [`ItemKind::ProjectReference`] items — a list containing `compile`
    /// (or `all`) excludes the reference from the consumer's compile
    /// references.
    pub exclude_assets: ItemMetadataValue,
    /// `IncludeAssets` metadata, same shape and population rules as
    /// [`ResolvedItem::exclude_assets`]. Known-absent means MSBuild's
    /// default of `all`; a list *not* covering `compile` stops the compile
    /// assets from flowing through the reference (the direct output still
    /// lands on the owner's own `ReferencePath`).
    pub include_assets: ItemMetadataValue,
    /// `PrivateAssets` metadata, same shape and population rules as
    /// [`ResolvedItem::exclude_assets`]. A list covering `compile` keeps the
    /// referenced project consumable by *this* project but stops it flowing
    /// to this project's own consumers. (MSBuild's default,
    /// `contentfiles;analyzers;build`, does not cover `compile`.)
    pub private_assets: ItemMetadataValue,
    /// `true` when a [`ItemKind::ProjectReference`] element carries P2P
    /// metadata this evaluator recognises as *significant but unmodelled* —
    /// `BuildReference`, `Targets`, `SetConfiguration`/`SetPlatform`/
    /// `SetTargetFramework`, `AdditionalProperties`, `UndefineProperties`,
    /// `GlobalPropertiesToRemove`, `SkipGetTargetFrameworkProperties` — via
    /// an attribute or an applicable child element. Probed (dotnet 10):
    /// `BuildReference="false"` and `Targets="Clean"` remove the target from
    /// `ReferencePath` outright, and the `Set*`/property-list names change
    /// which build of the target the real compiler sees, so a
    /// reference-semantics consumer must not treat the edge as a normal
    /// compile reference. Unrecognized metadata names are inert in the P2P
    /// protocol (probed) and do not set this. Always `false` on non-
    /// `ProjectReference` items.
    pub unmodelled_reference_metadata: bool,
    /// Byte span of the originating XML element in the project source.
    pub span: Range<usize>,
}

/// Whether a [`PackageReference`] targets packages via `Include` (declaring
/// a dependency) or `Update` (adjusting metadata — chiefly the version — of
/// a dependency declared elsewhere, the shape Central Package Management
/// uses). The distinction drives capture-time merging: an `Update` is folded
/// onto every *prior* `Include` of the same id (see
/// [`ParsedProject::package_references`]), so a captured [`PackageReference`]
/// exposed on a [`ParsedProject`] is always [`PackageRefOp::Include`] — the
/// `Update` variant only exists during evaluation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PackageRefOp {
    Include,
    Update,
}

/// A captured `<PackageReference>` item. The version and asset-control fields
/// are evaluated strings (after `$(...)` substitution); this crate does not
/// parse versions or interpret asset lists, which is the NuGet resolver's job
/// (`borzoi-nuget`). In the exact inline Central Package Management
/// subset this evaluator can prove, `version` is the effective version after
/// applying `VersionOverride` / matching `PackageVersion`. Otherwise it is the
/// raw local `Version` metadata and `package_references_uncertain` remains set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageReference {
    /// Always [`PackageRefOp::Include`] on a [`ParsedProject`]: matching
    /// `Update` items are folded into the `Include` they modify during
    /// evaluation and never surface as standalone references.
    pub op: PackageRefOp,
    /// The package id — the `Include` value, after `$(…)` expansion and
    /// `;`-splitting (a single element per id).
    pub id: String,
    /// Effective package version when known; otherwise the local `Version`
    /// metadata (attribute or child element), `$(...)`-expanded, or `None`.
    pub version: Option<String>,
    /// `VersionOverride` metadata — under CPM, overrides the central
    /// version for this id. Raw evaluated string.
    pub version_override: Option<String>,
    /// `IncludeAssets` / `ExcludeAssets` / `PrivateAssets` metadata, kept as
    /// opaque evaluated strings (asset-list semantics are the resolver's).
    pub include_assets: Option<String>,
    pub exclude_assets: Option<String>,
    pub private_assets: Option<String>,
    /// Byte span of the originating XML element in the entry project source.
    pub span: Range<usize>,
}

/// A captured `<PackageVersion>` item from Central Package Management. The
/// version is raw evaluated metadata; parsing NuGet version ranges is left to
/// `borzoi-nuget`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageVersion {
    /// The package id from `Include`, after `$(...)` expansion and
    /// `;`-splitting.
    pub id: String,
    /// `Version` metadata (attribute or child element), `$(...)`-expanded.
    pub version: Option<String>,
    /// Byte span of the originating XML element in the entry project source.
    pub span: Range<usize>,
}

/// A captured `<GlobalPackageReference>` item from Central Package Management.
/// It contributes a package reference implicitly; the NuGet resolver decides
/// how to fold it into the effective dependency set.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobalPackageReference {
    /// The package id from `Include`, after `$(...)` expansion and
    /// `;`-splitting.
    pub id: String,
    /// Raw evaluated package metadata.
    pub version: Option<String>,
    pub version_override: Option<String>,
    pub include_assets: Option<String>,
    pub exclude_assets: Option<String>,
    pub private_assets: Option<String>,
    /// Byte span of the originating XML element in the entry project source.
    pub span: Range<usize>,
}

/// A captured `<FrameworkReference>` item (e.g.
/// `Microsoft.AspNetCore.App`). Only the name is modelled — a framework
/// reference resolves to a shared-framework/targeting pack, not a NuGet
/// package.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrameworkReference {
    /// The `Include` value, after `$(…)` expansion and `;`-splitting.
    pub name: String,
    /// Byte span of the originating XML element in the entry project source.
    pub span: Range<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParsedProject {
    /// Compile items in compile order:
    /// `[Compile CompileOrder=CompileFirst…, CompileBefore…, Compile
    /// CompileOrder=CompileBefore…, Compile…, Compile CompileOrder=CompileAfter…,
    /// CompileAfter…, Compile CompileOrder=CompileLast…]`. Within each
    /// effective category, document order is preserved. `ProjectReference`
    /// items are *not* in this list — they live on
    /// [`Self::project_references`].
    pub items: Vec<ResolvedItem>,
    /// `<ProjectReference Include="...">` items in document order.
    /// Each `include` is the path to a referenced project file (csproj,
    /// fsproj, etc.), resolved against the entry project's directory
    /// the same way `<Compile>` includes are.
    pub(crate) project_references: Vec<ResolvedItem>,
    /// `true` if [`Self::project_references`] may diverge from MSBuild's
    /// evaluated item list. Consumers deriving *reference semantics* from
    /// the list — the LSP's compile-closure walk — must not trust it when
    /// set. The causes, each verified against `dotnet build`/`dotnet
    /// msbuild` probes:
    ///
    /// - A `<ProjectReference Update="…">` that may run, or a `Remove="…"`
    ///   that may run and that we could not apply exactly (an `Update` is not
    ///   modelled, so earlier `Include`s stand un-mutated in the list). A
    ///   `Remove` is applied when its spec resolves to identities we know —
    ///   literal paths, and the items of `@(Type)` / `@(Type->Exists())` over a
    ///   list known exactly — and each comparison lies in the domain where we
    ///   reproduce MSBuild's path matching (`evaluator::item_spec`). "May run"
    ///   includes a mutation behind a condition we could not evaluate — on the
    ///   element itself, on its enclosing `<ItemGroup>`, or an undecided
    ///   `<Choose>`/`<When>` chain — since the real build may execute it (a
    ///   probed `Update` writing `ReferenceOutputAssembly=false`, or a
    ///   `Remove`, really does strip the reference from `ReferencePath`).
    /// - A gate decided only by an *unpinned* property (one written under a
    ///   condition we couldn't evaluate) or an SDK-tainted read — or an
    ///   `Include` or `Exclude` **value** expanded from one, or from a name
    ///   the walk holds no value of and cannot show undefined (a write it
    ///   refused to compute), whether the walk keeps the item or drops it
    ///   (the captured path may hold a different target, or none, in the
    ///   real build, and a dropped one is an item MSBuild has): the real build may
    ///   take the other branch, running a skipped mutation or dropping a
    ///   captured `Include` (a phantom edge). A cleanly-decided gate over
    ///   undefined-but-never-written properties is trusted: under the
    ///   environment model (`extra_properties` ARE the environment) those
    ///   are genuinely unset. (Untrusted reads in *metadata* gates or
    ///   values degrade that item's metadata to
    ///   [`ItemMetadataValue::Unknown`] instead of flipping this flag.)
    /// - An `<ItemDefinitionGroup>` declaring `<ProjectReference>` metadata
    ///   defaults: probed, the default lands on every ProjectReference item
    ///   (regardless of document order) and e.g. a
    ///   `ReferenceOutputAssembly=false` default empties `ReferencePath`,
    ///   while the captured items still read as full references.
    /// - Content the walk did not enter ([`Self::hidden_content`]): an
    ///   `<Import>` it could not follow (unresolved or failed) or whose gate it
    ///   could not decide, in an SDK file as in a user's. The file may carry
    ///   any of the above, import a user file that does, or import a file a
    ///   later import names again, which MSBuild then skips as a duplicate. And
    ///   an `<Import>` whose gate an untrusted value decided, wherever it is.
    ///
    /// Deliberately out of contract: `<Target>`-time item mutation. This
    /// field describes the *evaluated* (static) item list; whether a target
    /// runs is a build-graph question no static evaluator can settle, and
    /// the same boundary already applies to Compile items from targets.
    ///
    /// A corresponding diagnostic ([`DiagnosticKind::UnsupportedItemOperation`],
    /// [`DiagnosticKind::UnsupportedCondition`],
    /// [`DiagnosticKind::UnresolvedImport`], …) is emitted alongside.
    pub(crate) project_references_uncertain: bool,
    /// The effective `<PackageReference>` dependency set in document order,
    /// after collapsing `Update` items onto the `Include` they modify: each
    /// `<PackageReference Update="X" …>` overwrites the matching (case-
    /// insensitive) metadata of every `Include="X"` declared *before* it, and
    /// a lone `Update` matching no prior `Include` is dropped — mirroring
    /// MSBuild's evaluated item view. Every entry is therefore
    /// [`PackageRefOp::Include`]. The direct dependencies the NuGet resolver
    /// folds over; when [`Self::package_references_uncertain`] is set this list
    /// may not faithfully reflect the project's package set — the resolver
    /// should decline rather than resolve a possibly-wrong closure.
    pub package_references: Vec<PackageReference>,
    /// `<PackageVersion>` items in document order. These are central package
    /// versions, not direct dependencies on their own.
    pub package_versions: Vec<PackageVersion>,
    /// `<GlobalPackageReference>` items in document order.
    pub global_package_references: Vec<GlobalPackageReference>,
    /// `<FrameworkReference>` items in document order.
    pub framework_references: Vec<FrameworkReference>,
    /// Project-defined properties, i.e. names assigned by
    /// `<PropertyGroup>` elements after `$(...)` expansion. Reserved
    /// MSBuild well-known properties and caller-supplied
    /// `extra_properties` are deliberately *excluded* from this map so
    /// callers can distinguish project-side state from inputs they
    /// already know about. Both are still consulted during substitution.
    ///
    /// **Trust-blind:** it holds the walk's values whether or not they are
    /// the real build's, and a name missing from it may be one the project
    /// wrote and the walk could not compute. A consumer that decides
    /// anything on a property reads [`Self::property`] instead.
    pub properties: HashMap<String, String>,
    /// F# preprocessor symbols from the evaluated `$(DefineConstants)`,
    /// parsed as a `;`-separated list with whitespace trimmed and empty
    /// segments dropped. Order and duplicates from the source value are
    /// preserved — callers wanting set semantics (e.g. feeding the
    /// preprocessor) can collect into a `HashSet`.
    ///
    /// Unlike [`Self::properties`] this *does* incorporate
    /// `extra_properties` (MSBuild global properties — e.g. when the
    /// caller passes `DefineConstants=DEBUG` to model `-p:DefineConstants=DEBUG`),
    /// so the list reflects the effective evaluated value rather than
    /// only what the project file itself wrote. Property-name lookup is
    /// case-insensitive (MSBuild semantics); individual segment casings
    /// are preserved (F# preprocessor symbols are case-sensitive).
    pub(crate) define_constants: Vec<String>,
    /// The declared target frameworks, in document order: `<TargetFrameworks>`
    /// split into entries, else `<TargetFramework>` as a single entry, else
    /// empty. Read it through [`target_frameworks()`](fn@target_frameworks), which is the supported
    /// accessor.
    ///
    /// Computed by the evaluator rather than derived from [`Self::properties`],
    /// because the split is on the **escaped** value: `net8.0%3bnet9.0` is one
    /// (bogus) framework whose name contains a semicolon, not two
    /// (oracle-pinned 2026-07-12), and `properties` has already been unescaped
    /// for its consumers.
    pub target_frameworks: Vec<String>,
    /// The evaluated `$(LangVersion)` (the project's `<LangVersion>`), trimmed,
    /// or `None` when unset/empty. Raw text — `"8.0"`, `"latest"`, `"preview"`,
    /// `"11"`, etc. — left for the consumer to resolve (e.g. the LSP maps it via
    /// `borzoi_cst::language_version::LanguageVersion::from_lang_version_text`).
    /// Sourced from the same merged `lookup` as [`Self::define_constants`], so it
    /// reflects globals/`extra_properties`, not only what the project file wrote.
    pub lang_version: Option<String>,
    /// [`Self::lang_version`] as the build holds it, untrimmed: the value the
    /// `Fsc` task hands the compiler. `None` when unset or empty.
    pub lang_version_untrimmed: Option<String>,
    /// The evaluated `$(OtherFlags)`, from the same merged lookup (globals and
    /// the environment included), untrimmed; `None` when unset or empty. The
    /// `Fsc` task appends it to the compiler's arguments.
    pub other_flags: Option<String>,
    /// The evaluated output-file base name — MSBuild writes
    /// `$(TargetName)$(TargetExt)`, and `TargetName` defaults to
    /// `$(AssemblyName)` (probed, dotnet 10.0.301, 2026-07-10:
    /// `<AssemblyName>Identity</AssemblyName><TargetName>FileName</TargetName>`
    /// produces `FileName.dll`; a padded `<AssemblyName> Padded </AssemblyName>`
    /// produces ` Padded .dll`, so the value is reported **verbatim**, never
    /// trimmed). Carries trust semantics like reference metadata, because a
    /// consumer locating an output DLL by this name fabricates when the name
    /// is wrong:
    ///
    /// - [`ItemMetadataValue::Known`]`(Some(name))`: the effective
    ///   `TargetName` (or, unset, `AssemblyName`), and the deciding
    ///   property's provenance was trustworthy under the environment model.
    /// - [`ItemMetadataValue::Known`]`(None)`: neither set (or set to empty)
    ///   — MSBuild's default applies (`$(MSBuildProjectName)`, the
    ///   project-file stem).
    /// - [`ItemMetadataValue::Unknown`]: the deciding value leans on an
    ///   *unpinned* property (written under a gate we couldn't evaluate) or
    ///   an SDK-package-tainted read, still contains unexpanded `$(...)`, or
    ///   is whitespace-only (a degenerate spelling MSBuild honours in the
    ///   filename but whose default gate `'$(TargetName)' == ''` does NOT
    ///   fire for) — the real build's name may differ; decline rather than
    ///   guess.
    ///
    /// Sourced from the merged `lookup` (same as [`Self::lang_version`]), so a
    /// caller-supplied global participates.
    pub target_name: ItemMetadataValue,
    /// What a read of each property name sees at the end of the evaluation,
    /// and whether it is the real build's answer: a trusted value, a name
    /// undefined in the real build too, a name the real build may define (a
    /// refused write, the environment, the toolset, content the walk could
    /// not see), or a value the walk holds and may have wrong. Globals and
    /// reserved names included. Read it through [`Self::property`].
    pub property_reads: PropertyReads,
    /// What the documents the walk entered from outside the entry .NET SDK
    /// define, read off their text whatever the conditions around it say.
    /// Workload manifests are not among them.
    pub foreign_definitions: ForeignDefinitions,
    /// The same, for the workload manifests the walk entered: files of the
    /// .NET install (under its `sdk-manifests`) outside the SDK's version
    /// directory, reached as SDK content, which every SDK project imports.
    pub workload_definitions: ForeignDefinitions,
    /// Files inside the entry SDK's version directory that a file outside it
    /// imported directly, other than an SDK's `Sdk.props`/`Sdk.targets`: the
    /// SDK's own content in an arrangement it did not choose (a project
    /// importing `$(MSBuildToolsPath)/Microsoft.CSharp.targets`, say).
    pub sdk_files_imported_from_outside: BTreeSet<PathBuf>,
    /// For each property the compiled-name derivation admits
    /// ([`crate::fsc`]), the first write of it made in a document outside the
    /// entry .NET SDK's version directory and its workload manifests (the
    /// entry project, `Directory.Build.*`, user imports, package build files)
    /// whose value is outside the name's grammar, keyed by the lowercased
    /// name: that value, or `None` when the walk is not certain what the write
    /// stored (a gate it could not decide, a value it refused or could not
    /// compute). A write under a gate that decided against it is not one. The
    /// SDK may copy a value between two writes, so a name's final value is not
    /// all it held; this is every value it held from outside the install.
    pub foreign_write_failures: BTreeMap<String, Option<String>>,
    /// The workload manifests the evaluation loaded from outside the entry
    /// SDK's install, by canonical location: the user's own, which the
    /// resolver reads behind the install's `userlocal` marker. They are
    /// entered as SDK content ([`Self::workload_definitions`]), not checked as
    /// a document outside the install is.
    pub workload_manifests_outside_install: BTreeSet<PathBuf>,
    /// The files of the entry .NET SDK's version directory the evaluation
    /// imported, each by its canonical path relative to that directory
    /// (`Sdks/Microsoft.NET.Sdk/targets/Microsoft.NET.Sdk.targets`), however
    /// the import spelled it (through a link into the install, say).
    pub imported_sdk_files: BTreeSet<PathBuf>,
    /// Every workload manifest file the evaluation read, by its path under
    /// the install's `sdk-manifests` (feature band, manifest, its version,
    /// file), `/`-separated.
    pub workload_manifest_files: BTreeSet<String>,
    /// The response file MSBuild's command line reads for the project, whose
    /// switches (a `-p:` global, say) the evaluation did not see.
    pub auto_response_file: AutoResponseFile,
    /// Why the walk did not see all of the build's content (an import it could
    /// not follow, or one whose gate it could not decide), or `None` when it
    /// entered everything the build imports. Content it did not see may define
    /// anything, so [`Self::foreign_definitions`] is complete only when this is
    /// `None`: [`Self::items_uncertain`] is `true` whenever it is `Some`, and
    /// [`Self::project_references()`] and [`Self::define_constants()`] are
    /// unknown.
    pub hidden_content: Option<UntrustedCause>,
    /// Why MSBuild rejects the whole project, or may, or `None` when nothing
    /// the walk passed could make it: the first construct the walk claims
    /// MSBuild rejects ([`RejectionCertainty::Certain`]), else the first that
    /// may ([`RejectionCertainty::Possible`]). MSBuild's rejection is total: the build has
    /// no value for any property, and no item. So the walk publishes nothing
    /// as the build's once this is `Some`, whatever it bound before or after
    /// the construct: every [`Self::property`] read is inexact
    /// ([`UntrustedCause::Rejected`], [`InexactUnset::Rejected`]),
    /// [`Self::items_uncertain`] and
    /// [`Self::package_references_uncertain`] are set,
    /// [`Self::define_constants()`] and [`Self::project_references()`] are
    /// unknown (each axis naming a
    /// [`DiagnosticKind::Rejected`] or [`DiagnosticKind::MayBeRejected`] cause
    /// where the axis records causes),
    /// [`Self::target_name`] is unknown and [`Self::hidden_content`] is
    /// `Some`. The trust-blind fields ([`Self::properties`],
    /// [`Self::target_frameworks`], [`Self::lang_version`],
    /// [`Self::other_flags`], …) keep the walk's values as best guesses, for a
    /// consumer that already serves one; a consumer committing to one checks
    /// this, or reads the value through [`Self::property`].
    ///
    /// The evaluation is still `Ok`: its [`Self::read_set`] says when it
    /// changes, and its diagnostics say why.
    ///
    /// The constructs:
    ///
    /// - an `<Import>` whose condition the walk could not decide, whose path
    ///   names no file MSBuild can load: missing, a directory, a dangling link,
    ///   malformed XML, empty, or one the walk could not compute (#820). A
    ///   condition that requires the file (`Exists` of the `Project` text, as a
    ///   conjunct) excuses a path naming nothing at all. The `Directory.Build.*`
    ///   import points' fallback is one of these;
    /// - an `<Import>` the walk took whose path names no file MSBuild can load:
    ///   it failed to load (missing, a dangling link, malformed XML), the path
    ///   is empty or absent, or the walk could not compute it (#845);
    /// - a `Condition` MSBuild throws on (#783): a syntax error, or an ill-typed
    ///   operand on the path MSBuild evaluates, where MSBuild evaluates the
    ///   condition or may: an item's whatever its group holds, an `Include`
    ///   item's metadata whatever the item holds, never one under a false
    ///   `<PropertyGroup>`, `<ImportGroup>` or `<ItemDefinitionGroup>`, an
    ///   unchosen `<When>` or a `<Target>`.
    ///
    /// A construct is [`RejectionCertainty::Certain`] where MSBuild reaches it
    /// for certain: the walk hid nothing before it, and every gate and import
    /// path on the way to it was decided from certain values. Of the imports,
    /// only one taken whose path names a missing file (a dangling link
    /// included) or is empty is claimed, its path named from certain values; of
    /// the conditions, a syntax error, or an ill-typed one reading only certain
    /// values. Every other is [`RejectionCertainty::Possible`].
    ///
    /// Not among them, each a doubt the walk cannot resolve from what it saw:
    /// an import in content the walk did not see, or one a value that content
    /// may have rewritten steers (a doubt that is only the walk's opacity is
    /// that content's, as for every reader but the import points and the
    /// Compile items, #792); one whose condition requires its file while its
    /// path is one the walk could not compute, which may name a dangling link
    /// MSBuild's `Exists` accepts; an SDK the walk's resolver cannot resolve,
    /// which MSBuild's may; every import the pure [`parse_fsproj`] meets,
    /// since it reads no file; and a condition the walk calls unmodelled,
    /// which MSBuild may evaluate or reject. The import-graph and property-table
    /// differentials grade the rest against MSBuild, and hold every certain
    /// rejection to MSBuild's.
    pub rejection: Option<Rejection>,
    pub diagnostics: Vec<Diagnostic>,
    /// `true` if any diagnostic was emitted — i.e. the result may diverge
    /// from what MSBuild itself would produce, including in ways that don't
    /// affect the Compile item set (a skipped `<Target>`, an undefined
    /// property in an imported SDK target, a property function we don't model).
    /// For "can I trust the *Compile order*?" — the question a consumer folding
    /// over `items` for name resolution actually asks — use the narrower
    /// [`Self::items_uncertain`].
    pub is_partial: bool,
    /// `true` if the resolved [`Self::items`] set may diverge from MSBuild *in
    /// which source files it contains* — the correctness-relevant subset of
    /// [`Self::is_partial`]. Set when a `<Compile>`/`<CompileBefore>`/
    /// `<CompileAfter>` item or its `<ItemGroup>` couldn't be included/excluded
    /// faithfully: an unmodeled or undefined-property condition gating one
    /// ([`Self::compile_condition_uncertainties`]), an ignored source-set item
    /// operation (`Remove`/`Exclude`; metadata-only `Update` is harmless unless
    /// it changes `CompileOrder`), an
    /// unexpanded glob or item/metadata reference in an `Include`, a
    /// `<Choose>` we could not decide with a Compile item in a still-possible
    /// branch, or a failed import / unresolved SDK that could contribute items.
    ///
    /// Unlike [`Self::is_partial`], it stays `false` for divergences that
    /// cannot change the Compile set — the common case for real SDK projects,
    /// whose imported targets always emit harmless property/`<Target>`
    /// diagnostics. A consumer that needs a trustworthy Compile order (and
    /// otherwise falls back to per-file handling) should gate on this, not
    /// `is_partial`.
    ///
    /// **SDK provenance.** Inside the entry SDK's own installation tree, a
    /// Compile operation whose own gate is a clean false — it runs in no build —
    /// is tolerated, and so is its group's gate: the SDK's default-item
    /// machinery is full of those, gated on properties we cannot always pin. An
    /// SDK Compile operation that *can* run is honoured exactly like a
    /// user-authored one, because it can decide which sources compile: the
    /// default `**/*.fs` glob runs whenever `EnableDefaultCompileItems` ends up
    /// `true`, and puts its files in front of the project's own list. So is one
    /// in a branch of a `<Choose>` the walk could not decide.
    ///
    /// **Hidden content.** Content the walk did not enter is never tolerated,
    /// in an SDK file or anywhere: an import it could not follow, or whose gate
    /// it could not decide, may hold a Compile item, import a user file that
    /// does (#821), or import a file a later import names again, which MSBuild
    /// then skips as a duplicate (#819). So this is `true` whenever
    /// [`Self::hidden_content`] is `Some`.
    ///
    /// **Known gaps** (deliberately *not* flagged; each is an "under-resolve,
    /// possibly wrong in a rare contrived case" rather than a common hazard):
    /// - A user property defined from an undefined reference (so it evaluates to
    ///   `""`) and then consumed by a `<Compile Include="$(That)/X.fs">`: the
    ///   include resolves to a wrong path with no diagnostic at the include
    ///   site (the undefinedness was upstream). Closing this needs taint
    ///   tracking we don't do.
    /// - A `<Target>` that mutates `@(Compile)` (adds/removes items at build
    ///   time) is *deliberately* not flagged. We never run targets, so a
    ///   target-added source is invisible — but this is the common, intended
    ///   pattern for *generated* sources (the SDK's `AssemblyInfo`, Nerdbank
    ///   GitVersioning's `ThisAssembly`, source generators). Flagging would
    ///   disable resolution for every such project; instead we under-resolve
    ///   the generated file and keep the hand-written ones working.
    pub items_uncertain: bool,
    /// The specific Compile items/groups whose inclusion couldn't be
    /// determined from their `Condition` — the explainable subset of why
    /// [`Self::items_uncertain`] is set. Empty unless a Compile-gating
    /// condition was undefined-property-laden or unmodeled. See
    /// [`CompileConditionUncertainty`].
    pub compile_condition_uncertainties: Vec<CompileConditionUncertainty>,
    /// Concrete events that made [`Self::items_uncertain`] true. This is the
    /// diagnostic/debug channel for corpus runners and LSP fallbacks: unlike the
    /// broad [`Self::diagnostics`] list, every entry here is causally tied to
    /// Compile item uncertainty.
    pub compile_item_uncertainties: Vec<CompileItemUncertaintyCause>,
    /// `true` if the resolved package/framework dependency inputs
    /// ([`Self::package_references`], [`Self::package_versions`],
    /// [`Self::global_package_references`], [`Self::framework_references`])
    /// may diverge from MSBuild in *which dependencies it contains, or their
    /// versions/metadata*. A consumer building the dependency closure should
    /// decline and fall back when this is set. The captured references are
    /// still returned — only their trustworthiness is in question.
    ///
    /// Set when a package-affecting item (`<PackageReference>`,
    /// `<PackageVersion>`, `<GlobalPackageReference>`, `<FrameworkReference>`)
    /// or its `<ItemGroup>` couldn't be resolved faithfully: an unmodeled or
    /// undefined-property condition gating one, an ignored `Remove`, an
    /// unexpanded/wildcarded `Include`, an unexpanded item/metadata reference
    /// in metadata, an `Exclude`/item-definition default we can't reduce, or a
    /// dropped structural container (`<Import>`/SDK/`<Choose>`) that could carry
    /// references.
    ///
    /// Unlike [`Self::items_uncertain`], SDK-tree dependency risks are **not**
    /// tolerated: the SDK is exactly where implicit dependency references live
    /// (`Microsoft.NETCore.App`, implicit `FSharp.Core`). Followed SDK files
    /// are evaluated through the same package-reference machinery as user
    /// files — every property (SDK files included) finalises before any item
    /// evaluates, so a cleanly-evaluated SDK dependency item is captured
    /// exactly and does *not* set this flag. What does: an unresolvable SDK
    /// (structural), and any SDK construct the walker genuinely cannot pin
    /// down — a condition or property write leaning on an undefined property,
    /// an unsupported expression, a dropped import — each adding its own
    /// concrete cause below.
    pub package_references_uncertain: bool,
    /// Concrete events that made [`Self::package_references_uncertain`] true.
    /// This is the diagnostic/debug channel for corpus runners and LSP
    /// fallbacks: unlike the broad [`Self::diagnostics`] list, every entry here
    /// is causally tied to package/framework-reference uncertainty.
    pub package_reference_uncertainties: Vec<PackageReferenceUncertaintyCause>,
    /// `true` if the evaluated [`Self::define_constants`] may diverge from
    /// MSBuild, for one of two reasons:
    ///
    /// - a *user-authored* `<DefineConstants>` write (or the `<PropertyGroup>`
    ///   condition gating one) relied on a property we couldn't resolve (e.g. a
    ///   `'$(TargetFramework)' == …`-conditioned define in a multi-targeted
    ///   project);
    /// - the walk passed content it did not enter ([`Self::hidden_content`]),
    ///   in an SDK file as in a user's. That content may write
    ///   `DefineConstants` or import a user file that does, and no later read
    ///   need see the write: it may be the last, and the
    ///   `$(DefineConstants);FOO` append reads its own name without doubting
    ///   the set (#843, #862). So this is `true` whenever `hidden_content` is
    ///   `Some`, as [`Self::items_uncertain`] is.
    ///
    /// The preprocessor-symbol analogue of [`Self::items_uncertain`]: a
    /// consumer that folds files under these `#if` symbols (cross-file name
    /// resolution) should refuse and fall back when this is set, since the
    /// wrong branches would otherwise be taken.
    ///
    /// Uncertainty in a write *inside the SDK's own files* that the walk
    /// entered is tolerated — we already don't model the framework defines
    /// (`NET6_0`, …) the SDK injects in targets, so our `define_constants` is a
    /// consistent (if framework-define-free) view rather than a
    /// per-branch-corrupt one. A `$(DefineConstants)` append's own read is
    /// that view too: undefined in it, unless the walk has hidden content
    /// that may have written it.
    ///
    /// **Accepted limitation — SDK-supplied defines are not modelled.** Because
    /// we never run SDK targets, the standard SDK F# defines (`DEBUG`/`TRACE`,
    /// set via `Choose`/property-function syntax in `Microsoft.FSharp.NetSdk.props`
    /// / the FSharp targets shim, and the per-TFM `NET6_0`/`NETCOREAPP…` family)
    /// are absent and **not** flagged here. This is the same incompleteness the
    /// single-file resolution path already has — `#if DEBUG`/`#if NET6_0` resolve
    /// to the branch taken when those symbols are *undefined*. Modelling them
    /// would require replicating the SDK's per-config/per-TFM implicit-define
    /// logic; flagging them would force single-file fallback for **every** SDK
    /// project (they all set these), defeating cross-file resolution. We
    /// deliberately accept the bounded divergence instead — it is consistent
    /// across single-file and cross-file resolution. Only *user-authored*
    /// define uncertainty (an unevaluable condition, an unsupported/`@()`/`%()`
    /// value reference) and hidden content are flagged.
    pub(crate) define_constants_uncertain: bool,
    /// Concrete events that made [`Self::define_constants_uncertain`] true —
    /// the define-axis twin of [`Self::compile_item_uncertainties`], and the
    /// only channel that can say *why* the `#if` symbol set is untrusted.
    ///
    /// The flag is raised at exactly two sites (a diagnostic pushed while in
    /// define context, and the walk's first latch of hidden content), each of
    /// which pushes here at the same moment, so
    /// `define_constants_uncertain == !define_constants_uncertainties.is_empty()`
    /// holds by construction; `define_uncertainty_and_its_causes_agree` pins it.
    pub(crate) define_constants_uncertainties: Vec<DefineConstantsUncertaintyCause>,
    /// The [`SdkPaths::root`] of the entry project's **own** SDK — its
    /// `<Project Sdk="X">` shorthand or the equivalent promoted explicit form
    /// (`<Import Sdk="X" Project="Sdk.props"/>` as the first body element).
    /// `None` when the entry declares no SDK of its own.
    ///
    /// Deliberately narrow: an SDK-less entry may still pull an SDK in via a
    /// nested `<Import>` or a `Directory.Build.{props,targets}` helper, but
    /// *which* of those establishes the framework is subtle and
    /// order-dependent, so this stays `None` rather than guess — the consumer
    /// should fall back to its own default-root discovery there.
    ///
    /// This is the SDK *import directory*, not the .NET install root; a
    /// consumer that wants the install (for `packs/` etc.) recovers it from
    /// this path's known layout.
    pub resolved_sdk_root: Option<PathBuf>,
    /// Lowercased property names the document opted out of global protection
    /// with `<Project TreatAsLocalProperty="…">` — the union across the entry
    /// document and every file the walk imported.
    ///
    /// A global property is read-only to the document unless its name appears
    /// here; listing it lets a project write win over the caller's value. The
    /// set is recorded whether or not *this* evaluation supplied such a global,
    /// because the question it answers is "could this document overwrite a
    /// global of that name?", which is a property of the document rather than
    /// of one caller's inputs.
    ///
    /// Reserved well-known names are never actually unprotected (MSBuild
    /// documents `TreatAsLocalProperty` as applying to globals only), but a
    /// reserved name *listed* by the document still appears here — this reports
    /// what the document asked for, not what the evaluator granted.
    ///
    /// **Raw text, not expanded.** MSBuild expands `$(…)` in the attribute and
    /// honours the result (probed, dotnet 10.0.301: `TreatAsLocalProperty="$(L)"`
    /// with `L=TargetFramework` lets a body write beat the global). We do not,
    /// here or in the protection the evaluator applies, so a computed attribute
    /// arrives as e.g. `$(l)` and unprotects nothing. A consumer asking "may the
    /// document overwrite my global?" must therefore treat an entry containing
    /// `$(` as a possible yes — absence of the name it cares about proves the
    /// name is absent from the *literal* list, not from the expanded one.
    ///
    /// The consumer this exists for is a caller that supplies a global and then
    /// needs to know whether the evaluation it got back was really conducted
    /// under it: the LSP seeds `TargetFramework` to obtain an inner build, and a
    /// document that can overwrite that seed does not yield one
    /// (`lsp::tfm_policy`). Reading the evaluated property table cannot answer
    /// that — an override whose *value* the evaluator refuses (`@(Items)`,
    /// `%(Meta)`) leaves no entry at all, so absence there proves nothing.
    pub locally_overridable_properties: BTreeSet<String>,
    /// Every file-system query the evaluation made, with its answer: the
    /// files it read, the paths it probed (those that were absent included),
    /// the directories it listed and the paths it canonicalised, through the
    /// caller's [`SdkResolver`] and [`GlobResolver`] as well as its own walk
    /// (see [`observed`]). While every answer stands
    /// ([`observed::ReadSet::first_stale`] is `None`), evaluating the same
    /// source with the same arguments gives this same `ParsedProject`.
    /// Empty from [`parse_fsproj`], which touches no file.
    pub read_set: observed::ReadSet,
    /// How many file-system calls of each kind the evaluation made, repeats
    /// included.
    pub read_counts: observed::ReadCounts,
}

/// Whether MSBuild's command line (`dotnet msbuild`, `dotnet build`) reads a
/// response file for a project: a `MSBuild.rsp` beside it, or the first
/// `Directory.Build.rsp` in the project's directory or an ancestor, whose
/// lines it takes as further switches unless handed `-noAutoResponse`. An evaluation does not read it, so its switches
/// are invisible to one.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub enum AutoResponseFile {
    /// The evaluation asked no file system (a pure parse), or resolved no
    /// SDK whose MSBuild would build the project.
    #[default]
    Unread,
    /// Neither MSBuild's directory nor any from the project's up holds one.
    Absent,
    /// This one.
    Present(PathBuf),
}

/// The names the documents of an evaluation define from outside the entry
/// .NET SDK (the `…/sdk/<version>` directory its `Sdk` resolved into, or every
/// document when it resolved none): the entry project, `Directory.Build.*`,
/// user imports, package build files, and anything else reached outside that
/// directory. Each name, lowercased and as written, maps to the files that
/// define it.
///
/// Read off each document's text, not off the walk: a definition counts
/// whether its condition held, failed, or could not be decided, and whether or
/// not the evaluation runs it (a `<Target>` body runs at build time). So a name
/// no query here matches is defined by no file the walk entered outside the
/// SDK, which, with [`ParsedProject::hidden_content`] `None`, is every such
/// file the build imports. Ask through the query methods, which also match a
/// name the build computes (`PropertyName="$(Name)"`) to every query.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ForeignDefinitions {
    /// Properties: every element directly inside a `<PropertyGroup>`,
    /// wherever the group sits, and every task `<Output PropertyName="…">`.
    pub properties: BTreeMap<String, BTreeSet<PathBuf>>,
    /// The subset of [`Self::properties`] written inside a `<Target>`, which
    /// the build runs after evaluation.
    pub build_time_properties: BTreeMap<String, BTreeSet<PathBuf>>,
    /// `<Target Name="…">` definitions.
    pub targets: BTreeMap<String, BTreeSet<PathBuf>>,
    /// `<UsingTask TaskName="…">` registrations, possibly namespace-qualified.
    pub tasks: BTreeMap<String, BTreeSet<PathBuf>>,
    /// `<Project DefaultTargets="…">` and `<Project InitialTargets="…">`, by
    /// attribute (lowercased): which targets a build runs.
    pub target_selections: BTreeMap<String, BTreeSet<PathBuf>>,
    /// Item types: every element directly inside an `<ItemGroup>`, wherever
    /// the group sits, and every task `<Output ItemName="…">`.
    pub items: BTreeMap<String, BTreeSet<PathBuf>>,
    /// Item types given metadata defaults: every element directly inside an
    /// `<ItemDefinitionGroup>`. A definition creates no item (`@(X)` of a type
    /// only defined is empty), so it is kept apart from [`Self::items`].
    pub item_definitions: BTreeMap<String, BTreeSet<PathBuf>>,
    /// Item metadata names: every element directly inside one of the item or
    /// item definition elements, and every attribute on one but the item
    /// operations, their modifiers, its condition and its label.
    pub item_metadata: BTreeMap<String, BTreeSet<PathBuf>>,
    /// The documents holding an element with a `Condition` attribute.
    pub conditioned: BTreeSet<PathBuf>,
    /// The documents holding an expansion (`$(`, `@(` or `%(`) in an
    /// attribute or an element's text (its text nodes joined, as MSBuild
    /// joins them around a comment), or text the scan cannot read.
    pub expanding: BTreeSet<PathBuf>,
    /// The documents holding a condition or an expansion in an element of a
    /// shape NuGet's restore does not write into `obj/*.nuget.g.props` and
    /// `.targets` (`BuildAssetsUtils`): a group of the root conditioned on
    /// `ExcludeRestorePackageImports`, `TargetFramework` and `Language`; a
    /// property of one conditioned on itself being empty, its text literal or
    /// `$(MSBuildThisFileDirectory)` and a literal; an item or `Import` of one
    /// on a literal or `$(NuGetPackageRoot)` and a literal, conditioned on
    /// that path existing; literal metadata.
    pub unlike_nuget: BTreeSet<PathBuf>,
    /// The documents holding an item operation (`Include`, `Exclude`,
    /// `Remove`, `Update`) with a wildcard (`*`, `?`) in it: an item a glob
    /// matched keeps the glob's spelling of its directory as its identity
    /// (`@sub/../Args*.fs` matches `@sub/../Args.fs`), which the walk's
    /// resolved path does not.
    pub globbing: BTreeSet<PathBuf>,
}

/// Whether `text` may hold an expansion: `$(`, `@(` or `%(` once every
/// whitespace character is taken out. MSBuild drops a whitespace-only text
/// node between two comments before it joins the text around them
/// (`Test$<!--a--> <!--b-->(X)` expands `X`), so whitespace cannot be read
/// as separating the two; taking all of it out covers every such reading,
/// and reads `$ (` as an expansion, which only declines more.
fn expands(text: &str) -> bool {
    let text: String = text.chars().filter(|c| !c.is_whitespace()).collect();
    text.contains("$(") || text.contains("@(") || text.contains("%(")
}

/// The text of `node`'s text children, joined (MSBuild reads an element's
/// text across the comments in it as one), or `None` when one of them is text
/// [`document::text`] cannot read.
fn joined_text(node: roxmltree::Node<'_, '_>) -> Option<String> {
    let mut text = String::new();
    for child in node.children().filter(roxmltree::Node::is_text) {
        text.push_str(&document::text(child)?);
    }
    Some(text)
}

/// Whether `node`, an element holding a condition or an expansion, is one
/// of the shapes NuGet's restore writes into `obj/*.nuget.g.props` and
/// `.targets` (`BuildAssetsUtils`, NuGet.Client):
///
/// - a `PropertyGroup`, `ItemGroup` or `ImportGroup` of the root whose
///   condition is a conjunction (` AND `) of `'$(ExcludeRestorePackageImports)'
///   != 'true'`, `'$(TargetFramework)' == ''`, `'$(TargetFramework)' == 'x'`,
///   `'$(Language)' == 'x'` and `'$(Language)' != 'x'`, `x` literal;
/// - a property of such a group conditioned `'$(Name)' == ''` on its own
///   name, its text literal or `$(MSBuildThisFileDirectory)` and a literal;
///   each condition compared with only its ends trimmed, as NuGet pads them,
///   so a quoted path's spaces are the path's;
/// - an item of such a group, or an `Import` of one, whose `Include` or
///   `Project` is a literal or `$(NuGetPackageRoot)` and a literal, with no
///   condition or `Exists('…')` of that same text; its metadata literal.
///
/// A literal holds no expansion. Every other element with a condition or an
/// expansion is not NuGet's, which [`ForeignDefinitions::unlike_nuget`]
/// records.
fn nuget_shaped(node: roxmltree::Node<'_, '_>) -> bool {
    // As MSBuild reads them: a literal tab or line break kept, where
    // `roxmltree` turns it into a space.
    let attribute = |name: &str| {
        node.attributes()
            .find(|a| a.name().eq_ignore_ascii_case(name))
            .and_then(|a| document::attribute(node, a.name()))
    };
    let tag = node.tag_name().name();
    let parent = node.parent_element();
    let parent_tag = parent.map(|p| p.tag_name().name()).unwrap_or_default();
    let is_root = |n: Option<roxmltree::Node<'_, '_>>| {
        n.is_some_and(|n| n.tag_name().name() == "Project" && n.parent_element().is_none())
    };
    let literal = |text: &str| !expands(text);
    let only = |allowed: &[&str]| {
        node.attributes()
            .all(|a| allowed.iter().any(|n| a.name().eq_ignore_ascii_case(n)))
    };
    let quoted = |atom: &str, prefix: &str, suffix: &str| {
        atom.strip_prefix(prefix)
            .and_then(|rest| rest.strip_suffix(suffix))
            .is_some_and(|value| literal(value) && !value.contains('\''))
    };
    let group_atom = |atom: &str| {
        atom == "'$(ExcludeRestorePackageImports)' != 'true'"
            || atom == "'$(TargetFramework)' == ''"
            || quoted(atom, "'$(TargetFramework)' == '", "'")
            || quoted(atom, "'$(Language)' == '", "'")
            || quoted(atom, "'$(Language)' != '", "'")
    };
    let rooted_literal = |text: &str, root: &str| literal(text.strip_prefix(root).unwrap_or(text));
    // One `Exists` of one quoted literal: a path holding a quote could close
    // the literal and add another call (`a') Or Exists('b`).
    let exists_of = |condition: Option<&str>, path: &str| {
        !path.contains('\'') && condition.is_none_or(|c| c.trim() == format!("Exists('{path}')"))
    };
    let group = ["PropertyGroup", "ItemGroup", "ImportGroup"];
    if group.contains(&tag) && is_root(parent) {
        return only(&["Condition"])
            && attribute("Condition").is_some_and(|c| c.trim().split(" AND ").all(group_atom));
    }
    if !(group.contains(&parent_tag) && is_root(parent.and_then(|p| p.parent_element()))) {
        // Item metadata: a child of an item of such a group, literal.
        let item_of_group = parent.is_some_and(|item| {
            item.parent_element()
                .is_some_and(|g| g.tag_name().name() == "ItemGroup" && is_root(g.parent_element()))
        });
        return item_of_group
            && node.attributes().next().is_none()
            && joined_text(node).is_some_and(|t| literal(&t));
    }
    match parent_tag {
        "PropertyGroup" => {
            only(&["Condition"])
                && attribute("Condition").is_some_and(|c| c.trim() == format!("'$({tag})' == ''"))
                && joined_text(node)
                    .is_some_and(|t| rooted_literal(&t, "$(MSBuildThisFileDirectory)"))
        }
        "ItemGroup" | "ImportGroup" => {
            let (operation, expected) = if parent_tag == "ItemGroup" {
                ("Include", tag != "Import")
            } else {
                ("Project", tag == "Import")
            };
            expected
                && only(&[operation, "Condition"])
                && attribute(operation).is_some_and(|path| {
                    rooted_literal(&path, "$(NuGetPackageRoot)")
                        && exists_of(attribute("Condition").as_deref(), &path)
                })
                && joined_text(node).is_some_and(|t| t.trim().is_empty())
        }
        _ => false,
    }
}

/// The attributes of an item element that are not metadata: its operations,
/// their modifiers, its condition and its label (lowercased).
const ITEM_ATTRIBUTES: &[&str] = &[
    "include",
    "exclude",
    "remove",
    "update",
    "condition",
    "label",
    "keepmetadata",
    "removemetadata",
    "keepduplicates",
    "matchonmetadata",
    "matchonmetadataoptions",
];

/// Whether a recorded name may stand for a name other than its spelling: one
/// the build computes (`$(…)`, `@(…)`, `%(…)`), or one carrying an escape
/// (`%56`), which MSBuild decodes. Either may be any name.
fn computed_name(name: &str) -> bool {
    name.contains("$(") || name.contains("@(") || name.contains('%')
}

impl ForeignDefinitions {
    /// Whether a document outside the SDK may define property `name`.
    pub fn defines_property(&self, name: &str) -> bool {
        Self::matches(&self.properties, name, |key, name| key == name)
    }

    /// Whether a document outside the SDK may define a property whose
    /// lowercased name satisfies `matches`.
    pub fn defines_property_where(&self, matches: impl Fn(&str) -> bool) -> bool {
        self.properties
            .keys()
            .any(|key| matches(key) || computed_name(key))
    }

    /// Whether a document outside the SDK defines any target, registers any
    /// task, or selects the targets a build runs: code the build runs, or the
    /// choice of it, which may do anything.
    pub fn defines_build_code(&self) -> bool {
        !self.targets.is_empty() || !self.tasks.is_empty() || !self.target_selections.is_empty()
    }

    /// Whether a document outside the SDK may write property `name` at build
    /// time, from a target.
    pub fn writes_property_at_build_time(&self, name: &str) -> bool {
        Self::matches(&self.build_time_properties, name, |key, name| key == name)
    }

    /// Whether a document outside the SDK writes property `name` from a target,
    /// spelling it out (case aside). Unlike
    /// [`Self::writes_property_at_build_time`], a computed or escaped name
    /// does not count: this is what a document names, not all it may write.
    pub fn names_property_at_build_time(&self, name: &str) -> bool {
        self.build_time_properties
            .contains_key(&name.to_ascii_lowercase())
    }

    /// Whether a document outside the SDK defines an item of type `name`,
    /// spelling it out (case aside). Unlike [`Self::defines_item`], a computed
    /// or escaped name does not count.
    pub fn names_item(&self, name: &str) -> bool {
        self.items.contains_key(&name.to_ascii_lowercase())
    }

    /// Whether a document outside the SDK may define an item of type `name`.
    pub fn defines_item(&self, name: &str) -> bool {
        Self::matches(&self.items, name, |key, name| key == name)
    }

    /// Whether a document outside the SDK may define item metadata `name`.
    pub fn defines_metadata(&self, name: &str) -> bool {
        Self::matches(&self.item_metadata, name, |key, name| key == name)
    }

    /// Whether a document outside the SDK may define target `name`.
    pub fn defines_target(&self, name: &str) -> bool {
        Self::matches(&self.targets, name, |key, name| key == name)
    }

    /// Whether a document outside the SDK may register a task that an
    /// invocation `<name>` runs: one registered as `name` or under any
    /// namespace (`Namespace.name`), as MSBuild matches a short task name.
    pub fn defines_task(&self, name: &str) -> bool {
        Self::matches(&self.tasks, name, |key, name| {
            key == name
                || key
                    .strip_suffix(name)
                    .is_some_and(|namespace| namespace.ends_with('.'))
        })
    }

    fn matches(
        table: &BTreeMap<String, BTreeSet<PathBuf>>,
        name: &str,
        same: impl Fn(&str, &str) -> bool,
    ) -> bool {
        let name = name.to_ascii_lowercase();
        table
            .keys()
            .any(|key| same(key, &name) || computed_name(key))
    }

    /// Record every definition in the document rooted at `root`, read from
    /// `file`.
    pub(crate) fn record_document(&mut self, root: roxmltree::Node<'_, '_>, file: &Path) {
        // Preorder, on an explicit stack carrying whether the node sits inside
        // a `<Target>`, so the pass is linear in the document however deep it
        // nests.
        let mut stack = vec![(root, false)];
        while let Some((node, in_target)) = stack.pop() {
            let tag = node.tag_name().name();
            // MSBuild does not read inside it.
            if tag.eq_ignore_ascii_case("ProjectExtensions") {
                continue;
            }
            let is_target = tag.eq_ignore_ascii_case("Target");
            stack.extend(
                node.children()
                    .filter(roxmltree::Node::is_element)
                    .map(|child| (child, in_target || is_target))
                    .collect::<Vec<_>>()
                    .into_iter()
                    .rev(),
            );
            self.record_element(node, in_target, file);
        }
    }

    fn record_element(&mut self, node: roxmltree::Node<'_, '_>, in_target: bool, file: &Path) {
        let conditioned = node
            .attributes()
            .any(|a| a.name().eq_ignore_ascii_case("Condition"));
        if conditioned {
            self.conditioned.insert(file.to_path_buf());
        }
        let expanding = node.attributes().any(|a| expands(a.value()))
            || joined_text(node).is_none_or(|text| expands(&text));
        if expanding {
            self.expanding.insert(file.to_path_buf());
        }
        if (conditioned || expanding) && !nuget_shaped(node) {
            self.unlike_nuget.insert(file.to_path_buf());
        }
        let tag = node.tag_name().name();
        let attribute = |name: &str| {
            node.attributes()
                .find(|a| a.name().eq_ignore_ascii_case(name))
                .map(|a| a.value())
        };
        if tag.eq_ignore_ascii_case("Project") && node.parent_element().is_none() {
            for selection in ["DefaultTargets", "InitialTargets"] {
                if attribute(selection).is_some_and(|v| !v.trim().is_empty()) {
                    self.target_selections
                        .entry(selection.to_ascii_lowercase())
                        .or_default()
                        .insert(file.to_path_buf());
                }
            }
            return;
        }
        let in_group = |group: &str| {
            node.parent_element()
                .is_some_and(|p| p.tag_name().name().eq_ignore_ascii_case(group))
        };
        let in_property_group = in_group("PropertyGroup");
        let in_definition_group = in_group("ItemDefinitionGroup");
        let in_item_group = in_group("ItemGroup") || in_definition_group;
        // An item element's children are its metadata, and so are its
        // attributes beyond the item operations.
        let is_metadata = node.parent_element().is_some_and(|item| {
            item.parent_element().is_some_and(|group| {
                let group = group.tag_name().name();
                group.eq_ignore_ascii_case("ItemGroup")
                    || group.eq_ignore_ascii_case("ItemDefinitionGroup")
            })
        });
        if is_metadata {
            self.item_metadata
                .entry(tag.to_ascii_lowercase())
                .or_default()
                .insert(file.to_path_buf());
            return;
        }
        if in_item_group {
            if ["include", "exclude", "remove", "update"]
                .iter()
                .any(|op| attribute(op).is_some_and(|value| value.contains(['*', '?'])))
            {
                self.globbing.insert(file.to_path_buf());
            }
            for attribute in node.attributes() {
                let name = attribute.name().to_ascii_lowercase();
                if !ITEM_ATTRIBUTES.contains(&name.as_str()) {
                    self.item_metadata
                        .entry(name)
                        .or_default()
                        .insert(file.to_path_buf());
                }
            }
        }
        // In an item group an `Output` element is an item type, not a task's
        // output.
        let output = tag.eq_ignore_ascii_case("Output") && !in_item_group;
        let output_property = if output {
            attribute("PropertyName")
        } else {
            None
        };
        let (table, name) = if in_property_group {
            (&mut self.properties, Some(tag))
        } else if output_property.is_some() {
            (&mut self.properties, output_property)
        } else if output {
            (&mut self.items, attribute("ItemName"))
        } else if in_definition_group {
            (&mut self.item_definitions, Some(tag))
        } else if in_item_group {
            (&mut self.items, Some(tag))
        } else if tag.eq_ignore_ascii_case("Target") {
            (&mut self.targets, attribute("Name"))
        } else if tag.eq_ignore_ascii_case("UsingTask") {
            (&mut self.tasks, attribute("TaskName"))
        } else {
            return;
        };
        let Some(name) = name.map(str::trim).filter(|n| !n.is_empty()) else {
            return;
        };
        let name = name.to_ascii_lowercase();
        let property = in_property_group || output_property.is_some();
        table
            .entry(name.clone())
            .or_default()
            .insert(file.to_path_buf());
        if property && in_target {
            self.build_time_properties
                .entry(name)
                .or_default()
                .insert(file.to_path_buf());
        }
    }
}

/// Why the walk does not commit to its `<ProjectReference>` list
/// ([`ParsedProject::project_references`]): the conditions
/// `ParsedProject::project_references_uncertain` documents. The walk records
/// no cause on this axis; its diagnostics say what it met.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProjectReferencesUnknown;

/// The walk's own values for what [`ParsedProject`] publishes as verdicts,
/// whether or not the build holds them: its best guess, for a consumer that
/// serves one and says so.
///
/// A consumer deciding anything on these reads the verdicts instead
/// ([`ParsedProject::define_constants`], [`ParsedProject::project_references`]).
#[derive(Debug, Clone, Copy)]
pub struct BestGuess<'a> {
    /// The `DefineConstants` list the walk holds.
    pub define_constants: &'a [String],
    /// The `<ProjectReference>` items the walk holds.
    pub project_references: &'a [ResolvedItem],
}

impl ParsedProject {
    /// The F# preprocessor symbols of the evaluated `$(DefineConstants)`,
    /// when the walk commits to them; otherwise why it does not (every
    /// recorded cause, never none).
    ///
    /// What `Certain` covers: the list the evaluation of the project's
    /// documents gives `$(DefineConstants)`, split on the escaped value's
    /// semicolons, globals and the environment included. **Not** the symbols
    /// the SDK's targets add at build time (`DEBUG`, `TRACE`, the `NET6_0`
    /// family), which the walk does not run and does not doubt the list for:
    /// a symbol missing from a `Certain` list is not proof that the compiler
    /// leaves it undefined. An uncertain write inside the SDK's own files is
    /// tolerated on the same grounds. `Unknown` covers a user-authored write
    /// (or its gate) leaning on a value the walk cannot pin, content the walk
    /// did not enter, and a project MSBuild may reject.
    pub fn define_constants(&self) -> Verdict<&[String], &[DefineConstantsUncertaintyCause]> {
        if self.define_constants_uncertain {
            Verdict::Unknown(&self.define_constants_uncertainties)
        } else {
            Verdict::Certain(&self.define_constants)
        }
    }

    /// The `<ProjectReference>` items in document order, when the walk
    /// commits to them; otherwise [`ProjectReferencesUnknown`].
    ///
    /// What `Certain` covers is a **subset** of MSBuild's evaluated list: it
    /// holds no item the build lacks (no phantom edge), but an `Include` the
    /// walk dropped behind a gate it could not decide may be missing from it,
    /// as may one whose value it could not compute from names it holds
    /// exactly. So a reference missing from a `Certain` list is not proof that
    /// the build has none. `Unknown` covers an item the build may lack or
    /// whose identity the walk may have wrong: an `Update`/`Remove` that may
    /// run, a kept `Include` behind a doubted gate or reading a doubted name,
    /// an `<ItemDefinitionGroup>` default, content the walk did not enter, and
    /// a project MSBuild may reject. Target-time mutation is out of contract.
    pub fn project_references(&self) -> Verdict<&[ResolvedItem], ProjectReferencesUnknown> {
        if self.project_references_uncertain {
            Verdict::Unknown(ProjectReferencesUnknown)
        } else {
            Verdict::Certain(&self.project_references)
        }
    }

    /// The walk's own values for what this type publishes as verdicts,
    /// whether or not the build holds them ([`BestGuess`]).
    pub fn best_guess(&self) -> BestGuess<'_> {
        BestGuess {
            define_constants: &self.define_constants,
            project_references: &self.project_references,
        }
    }

    /// What a read of `name` sees at the end of the evaluation
    /// ([`Self::property_reads`]). Case-insensitive (MSBuild property names
    /// compare OrdinalIgnoreCase).
    pub fn property(&self, name: &str) -> PropertyRead {
        self.property_reads.read(name)
    }

    /// Whether this evaluation is the outer build of a multi-targeted
    /// project, which dispatches one inner build per target framework and
    /// compiles nothing itself: the SDK's `IsCrossTargetingBuild`, which it
    /// sets when `TargetFrameworks` is and `TargetFramework` is not. `None`
    /// when the walk does not trust the property.
    pub fn is_outer_build(&self) -> Option<bool> {
        match self.property("IsCrossTargetingBuild") {
            PropertyRead::Value(value) => Some(value.eq_ignore_ascii_case("true")),
            PropertyRead::Unset => Some(false),
            _ => None,
        }
    }
}

/// Parse the `DefineConstants` MSBuild value into the F# preprocessor's
/// symbol list. Used by the evaluator at project-exit time to populate
/// [`ParsedProject::define_constants`].
/// The `DefineConstants` list, built the way MSBuild builds a list out of a
/// property: split on the semicolons of the **escaped** value, then decode each
/// fragment. So `A%3bB` is the single define `A;B`, not two
/// (oracle-pinned 2026-07-12) — decoding first would split it.
pub(crate) fn define_constants_from_escaped(
    value: &crate::properties::escaping::Escaped,
) -> Vec<String> {
    value
        .split_list()
        .map(|fragment| fragment.unescape().trim().to_string())
        .filter(|s| !s.is_empty())
        .collect()
}

#[derive(Debug)]
pub enum ParseError {
    /// The project file is not well-formed XML.
    Xml(roxmltree::Error),
    /// `extra_properties` contained a key that names an MSBuild
    /// reserved property (any spelling, under MSBuild's case-insensitive
    /// comparison, of a name in `ReservedPropertyNames`:
    /// `MSBuildProjectName`, `MSBuildToolsPath`, `MSBuildVersion`, …).
    /// MSBuild refuses such a global property and evaluates nothing
    /// (`MSB4177: …property name is reserved` from the command line), so
    /// we refuse it too. The stored name is the caller's original casing.
    ReservedPropertyInExtras(String),
    /// `extra_properties` contained a key that is not a valid MSBuild
    /// property name: empty, or not an ASCII letter or `_` followed by
    /// ASCII letters, digits, `_` and `-` (`XmlUtilities`' element-name
    /// rule). MSBuild refuses such a global property and evaluates
    /// nothing, so we refuse it too.
    InvalidPropertyNameInExtras(String),
    /// `extra_properties` contained two keys that compare equal under
    /// MSBuild's `OrdinalIgnoreCase` property-name comparison
    /// (e.g., `Configuration` and `configuration`). The substitution
    /// map is keyed case-insensitively, and `HashMap` iteration order
    /// is unspecified — picking one silently would let
    /// `$(Configuration)` resolve to a different value across runs.
    /// Stored as a lexicographically-sorted pair so the error is
    /// deterministic regardless of iteration order.
    DuplicateExtraProperty { first: String, second: String },
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Xml(e) => write!(f, "malformed XML: {e}"),
            ParseError::ReservedPropertyInExtras(name) => {
                write!(
                    f,
                    "extra_properties contains the reserved MSBuild property name {name:?}"
                )
            }
            ParseError::InvalidPropertyNameInExtras(name) => {
                write!(
                    f,
                    "extra_properties contains {name:?}, which is not a valid MSBuild property name"
                )
            }
            ParseError::DuplicateExtraProperty { first, second } => {
                write!(
                    f,
                    "extra_properties contains case-insensitive duplicate keys {first:?} and {second:?} (MSBuild property names compare OrdinalIgnoreCase)"
                )
            }
        }
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ParseError::Xml(e) => Some(e),
            ParseError::ReservedPropertyInExtras(_) => None,
            ParseError::InvalidPropertyNameInExtras(_) => None,
            ParseError::DuplicateExtraProperty { .. } => None,
        }
    }
}

impl From<roxmltree::Error> for ParseError {
    fn from(e: roxmltree::Error) -> Self {
        ParseError::Xml(e)
    }
}

/// Evaluate `project` and extract its Compile items.
///
/// The project's full path ([`ProjectFile::path`]) is used both to resolve
/// `Include` paths relative to the project file's directory and to seed the
/// well-known MSBuild path properties (`MSBuildProjectDirectory`,
/// `MSBuildProjectName`, etc.); its text ([`ProjectFile::text`]) is the body
/// walked. No filesystem access is performed.
///
/// `extra_properties` plays the role of MSBuild's *global properties*:
/// values supplied here are visible to substitution and cannot be
/// overridden by the project file's own `<PropertyGroup>` writes
/// (matching MSBuild's command-line-property semantics).
///
/// `environment` plays the role of the process environment MSBuild
/// promotes into initial properties. Its semantics differ from
/// `extra_properties` exactly as MSBuild's differ (all pinned against
/// `dotnet msbuild` 10.0.300): environment-backed properties are
/// readable from the start, are **overridable** by project property
/// writes, and lose to global properties of the same name. Skipped and
/// left undefined: reserved names, toolset-computed names MSBuild
/// overwrites after promotion (`MSBuildToolsPath` and friends), and
/// names with a case-insensitive collision in the snapshot (MSBuild's
/// winner is unspecified).
///
/// `MSBuildExtensionsPath` is the one name whose fate depends on the
/// *toolset*: MSBuild ≤ 17 (SDK 8 and 9) promotes it and then overwrites it
/// with the toolset's own directory, while MSBuild 18 (SDK 10) lets the
/// environment value stand — where it steers `Sdk.props`'s import of
/// `Microsoft.Common.props`. The walker learns which toolset applies only when
/// an SDK resolves to the canonical dotnet layout, so through this entry point
/// — which resolves no SDK — an environment-supplied `MSBuildExtensionsPath`
/// is left undefined rather than committed to either behaviour. Callers that
/// want it honoured must go through [`parse_fsproj_with_imports`] with an SDK
/// resolver.
///
/// Pass the (filtered) environment the real
/// build would run under; an empty map means "no environment
/// variables", which is itself a claim — with the exact-undefined-read
/// model, a name absent from every input reads as exactly empty
/// wherever the walk has stayed exact.
pub fn parse_fsproj(
    project: &ProjectFile,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
) -> Result<ParsedProject, ParseError> {
    validate_inputs(extra_properties)?;
    let doc = crate::document::parse(project.text())?;
    Ok(evaluator::walk(
        &doc,
        project.path(),
        extra_properties,
        environment,
    ))
}

/// Filesystem-touching counterpart to [`parse_fsproj`]: follows explicit
/// `<Import Project="...">` references (substituting `$(...)`, resolving
/// relative paths against the importing file's directory, depth-checked,
/// with duplicate imports — cycles included — silently skipped exactly
/// as MSBuild skips them under warning MSB4011/MSB4210).
///
/// Failures during follow (file missing, malformed XML, depth limit,
/// IO error) are reported via [`DiagnosticKind::ImportFailed`].
/// Successful follows produce *no* diagnostic — the merged result is
/// itself the report. In particular,
/// [`DiagnosticKind::ImplicitImportPresent`] is **never** emitted by
/// this entry point; that diagnostic is a property of the pure
/// "what did we skip" surfacing in [`detect_implicit_imports`].
///
/// `sdk_resolver`, if supplied, turns the project's `<Project Sdk="X">`
/// shorthand (and `<Import Sdk="X" Project="Sdk.props|Sdk.targets" />`
/// elements inside the body) into on-disk [`SdkPaths`] the walker
/// imports: the root attribute's `Sdk.props` before the body and its
/// `Sdk.targets` after. When the resolver returns `None`, a
/// [`DiagnosticKind::SdkNotFound`] diagnostic is emitted; when
/// `sdk_resolver` itself is `None`, any `Sdk` attribute surfaces as
/// [`DiagnosticKind::SdkResolverAbsent`]. Either way the body is still
/// walked.
///
/// **`Directory.Build.props` and `.targets`** arrive as MSBuild's do:
/// through the SDK's own imports of `$(DirectoryBuildPropsPath)` and
/// `$(DirectoryBuildTargetsPath)` (in `Microsoft.Common.props` and
/// `.targets`), at those imports' positions and under their conditions, so
/// a project no SDK reaches imports neither. An import point the walk
/// cannot decide, or one in content it could not see, makes the whole
/// evaluation uncertain from there (the evaluator's `directory_build`
/// module states exactly which points are decided).
///
/// **Explicit-only SDK projects.** A project using the *explicit*
/// form `<Project><Import Sdk="X" Project="Sdk.props"/>...</Project>`
/// with no root `Sdk` attribute is handled by a body pre-scan: the
/// first unconditional `<Import Sdk="X" Project="Sdk.props"/>` (and
/// the matching trailing `Sdk.targets`, if present) is promoted to
/// the same outermost positions the root-`Sdk` shorthand uses.
/// Promotion is conservative — it only fires when `Sdk.props` is the
/// first element child of root (and `Sdk.targets` the last), so it
/// never reorders user-visible work; anything else is walked at its
/// in-body position.
///
/// **Nested SDK roots in imported files.** When an `<Import>` is
/// chased into a file whose own `<Project>` carries `Sdk="X"`, that
/// SDK is resolved through the same resolver and its
/// `Sdk.props` / `Sdk.targets` are walked before / after the
/// imported file's body; its files' `Directory.Build.*` import points
/// are import points like the entry SDK's. Spans for SDK-contributed
/// items/diagnostics collapse to the entry project's `<Import>` site,
/// like any other imported content.
///
/// **Glob expansion.** When `glob_resolver` is supplied, an item
/// element whose `Include` contains an MSBuild wildcard (or that carries
/// an `Exclude`) is routed through it: the evaluator builds a
/// [`GlobRequest`] (project dir + ref-stripped include fragments + split
/// excludes) and splices the returned paths verbatim, each as an item of
/// the element's kind. When it is `None`, a wildcard `Include` surfaces
/// as [`DiagnosticKind::UnsupportedGlob`] and an `Exclude` as
/// [`DiagnosticKind::UnsupportedItemOperation`] — see [`GlobResolver`].
///
/// Same input validation contract as [`parse_fsproj`]: `extra_properties`
/// must neither name a reserved MSBuild property nor contain
/// case-insensitive duplicates.
/// `environment` carries the same semantics as on [`parse_fsproj`]
/// (overridable environment-backed properties; reserved names ignored).
///
/// The evaluation asks each file-system query once (see [`observed`]), and
/// parses every file it imports; [`parse_fsproj_with_imports_reusing`]
/// reuses the parses of an earlier evaluation.
pub fn parse_fsproj_with_imports(
    project: &ProjectFile,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    sdk_resolver: Option<&SdkResolver<'_>>,
    glob_resolver: Option<&GlobResolver<'_>>,
) -> Result<ParsedProject, ParseError> {
    parse_fsproj_probed(
        project,
        extra_properties,
        environment,
        sdk_resolver,
        glob_resolver,
        None,
        #[cfg(any(test, feature = "test-support"))]
        None,
    )
    .map(|walked| walked.project)
}

/// [`parse_fsproj_with_imports`], reusing the documents of `documents` that
/// were parsed from exactly the bytes this evaluation reads, and leaving in
/// it the document of every file it imported.
///
/// The result is [`parse_fsproj_with_imports`]'s, read set and counts
/// included, whatever `documents` holds: an imported file is read either way,
/// and a document is reused only for the very bytes it was parsed from
/// ([`observed::ImportDocuments`]).
pub fn parse_fsproj_with_imports_reusing(
    project: &ProjectFile,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    sdk_resolver: Option<&SdkResolver<'_>>,
    glob_resolver: Option<&GlobResolver<'_>>,
    documents: &mut observed::ImportDocuments,
) -> Result<ParsedProject, ParseError> {
    let observer = observed::Observer::with_documents(std::mem::take(documents));
    let (walked, kept) = parse_fsproj_observed(
        project,
        extra_properties,
        environment,
        sdk_resolver,
        glob_resolver,
        None,
        observer,
        #[cfg(any(test, feature = "test-support"))]
        None,
    );
    *documents = kept;
    walked.map(|walked| walked.project)
}

/// [`parse_fsproj_with_imports`] through an observer that asks the file system
/// every query it is asked and parses every file it reads
/// ([`observed::Observer::asking_every_time`]): the reference the memo and the
/// document reuse are held to.
#[cfg(any(test, feature = "test-support"))]
pub fn parse_fsproj_with_imports_asking_every_time(
    project: &ProjectFile,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    sdk_resolver: Option<&SdkResolver<'_>>,
    glob_resolver: Option<&GlobResolver<'_>>,
) -> Result<ParsedProject, ParseError> {
    parse_fsproj_observed(
        project,
        extra_properties,
        environment,
        sdk_resolver,
        glob_resolver,
        None,
        observed::Observer::asking_every_time(),
        None,
    )
    .0
    .map(|walked| walked.project)
}

/// [`parse_fsproj_with_imports`] of the build a process started in
/// `startup_directory` runs, when one is given, also answering `probe` from
/// the end of the walk when one is given (see `evaluator::reads`). Only the
/// differential tests pass a probe, so a build without them has neither that
/// module nor the `probe` parameter.
///
/// `startup_directory` is the working directory of a build process the caller
/// itself launches, which MSBuild exposes as `MSBuildStartupDirectory`. It is
/// a host fact, not a global property, and only an evaluation that models such
/// a process may supply it: the restore cone's (A₁ in
/// `docs/nuget-dgspec-boundary-plan.md`). The public entry points, which
/// model a build nobody launched, have no such parameter and pass `None`, so
/// what they return never carries a guessed startup directory.
#[allow(clippy::too_many_arguments)]
pub(crate) fn parse_fsproj_probed(
    project: &ProjectFile,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    sdk_resolver: Option<&SdkResolver<'_>>,
    glob_resolver: Option<&GlobResolver<'_>>,
    startup_directory: Option<&Path>,
    #[cfg(any(test, feature = "test-support"))] probe: Option<&evaluator::reads::ReadProbe>,
) -> Result<evaluator::Walked, ParseError> {
    parse_fsproj_observed(
        project,
        extra_properties,
        environment,
        sdk_resolver,
        glob_resolver,
        startup_directory,
        observed::Observer::new(),
        #[cfg(any(test, feature = "test-support"))]
        probe,
    )
    .0
}

/// [`parse_fsproj_probed`] through `observer`, handing back the documents it
/// holds when the evaluation ends ([`observed::Observer::finish_with_documents`]).
#[allow(clippy::too_many_arguments)]
fn parse_fsproj_observed(
    project: &ProjectFile,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    sdk_resolver: Option<&SdkResolver<'_>>,
    glob_resolver: Option<&GlobResolver<'_>>,
    startup_directory: Option<&Path>,
    observer: observed::Observer,
    #[cfg(any(test, feature = "test-support"))] probe: Option<&evaluator::reads::ReadProbe>,
) -> (
    Result<evaluator::Walked, ParseError>,
    observed::ImportDocuments,
) {
    if let Err(error) = validate_inputs(extra_properties) {
        return (Err(error), observer.finish_with_documents().2);
    }
    let project_path = project.path();
    // Detection only: the walk follows the SDK's own imports of the
    // props/targets files, and holds the files found here as the ones the
    // SDK's discovery names by default. The per-kind `ImplicitImportPresent`
    // diagnostic `detect_implicit_imports` would add is suppressed.
    // `DirectoryPackagesProps` is not imported here either: NuGet's own
    // `NuGet.props` (reached through `Sdk.props` →
    // `Microsoft.Common.props` when an SDK resolves to the canonical
    // dotnet layout) owns that import point, and the walker evaluates
    // those real files. The detected path is passed down so the walk
    // keeps the conservative "central versions not folded in" cause
    // whenever it never reached the file (no resolver, non-SDK project,
    // or a break anywhere along the chain).
    let mut implicit_props = None;
    let mut implicit_targets = None;
    let mut cpm_props_path = None;
    for diag in imports::detect_implicit_imports(project_path, &observer) {
        if let DiagnosticKind::ImplicitImportPresent { path, kind } = diag.kind {
            match kind {
                ImplicitImportKind::DirectoryBuildProps => implicit_props = Some(path),
                ImplicitImportKind::DirectoryBuildTargets => implicit_targets = Some(path),
                ImplicitImportKind::DirectoryPackagesProps => cpm_props_path = Some(path),
            }
        }
    }
    let doc = match crate::document::parse(project.text()) {
        Ok(doc) => doc,
        Err(error) => return (Err(error.into()), observer.finish_with_documents().2),
    };
    let mut walked = evaluator::walk_with_imports(
        &doc,
        project_path,
        extra_properties,
        environment,
        implicit_props.as_deref(),
        implicit_targets.as_deref(),
        cpm_props_path.as_deref(),
        sdk_resolver,
        glob_resolver,
        startup_directory,
        &observer,
        #[cfg(any(test, feature = "test-support"))]
        probe,
    );
    // The MSBuild that builds the project is the resolved SDK's: its
    // version directory.
    // An SDK of another layout (a NuGet SDK, a custom resolver's) names no
    // MSBuild directory, and the search reads nothing.
    let msbuild_dir = walked
        .project
        .resolved_sdk_root
        .as_deref()
        .and_then(evaluator::dotnet_sdk_version_dir)
        .map(Path::to_path_buf);
    walked.project.auto_response_file =
        imports::find_auto_response_file(project_path, msbuild_dir.as_deref(), &observer);
    let (read_set, read_counts, documents) = observer.finish_with_documents();
    walked.project.read_set = read_set;
    walked.project.read_counts = read_counts;
    (Ok(walked), documents)
}

/// Input-validation shared between the pure and with-imports entry
/// points: both reject the same set of malformed `extra_properties` up front,
/// before any XML parsing. The project's path was validated when its
/// [`ProjectFile`] was made.
fn validate_inputs(extra_properties: &HashMap<String, String>) -> Result<(), ParseError> {
    // Property lookup is OrdinalIgnoreCase, but `HashMap<String,_>` is
    // case-sensitive — so the caller can hand us `Configuration` and
    // `configuration` as two distinct entries, then `State::new`
    // inserts whichever HashMap iteration happens to visit last,
    // making `$(Configuration)` non-deterministic across runs. Reject
    // collisions up front. We sort the pair so the error message is
    // stable regardless of iteration order.
    let mut seen: HashMap<String, &String> = HashMap::with_capacity(extra_properties.len());
    for key in extra_properties.keys() {
        let lower = key.to_ascii_lowercase();
        if let Some(prior) = seen.get(&lower) {
            let (first, second) = if prior.as_str() <= key.as_str() {
                ((*prior).clone(), key.clone())
            } else {
                (key.clone(), (*prior).clone())
            };
            return Err(ParseError::DuplicateExtraProperty { first, second });
        }
        seen.insert(lower, key);
    }
    // MSBuild refuses a global property whose name is not a valid property
    // name, or is reserved (`MSB4177` from the command line), and evaluates
    // nothing. Honouring such a key would commit a value the real build never
    // has: the caller's in place of the path-derived `MSBuildProjectName`, or
    // of the seeded `MSBuildAssemblyVersion`. `tests/reserved_global_diff.rs`
    // holds this verdict to MSBuild's, name for name. Sorted, so that which
    // key the error names does not depend on the map's iteration order.
    let mut keys: Vec<&String> = extra_properties.keys().collect();
    keys.sort();
    for key in keys {
        if !evaluator::is_valid_name(key) {
            return Err(ParseError::InvalidPropertyNameInExtras(key.clone()));
        }
        if evaluator::is_msbuild_reserved_name(key) {
            return Err(ParseError::ReservedPropertyInExtras(key.clone()));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod with_imports_tests;
