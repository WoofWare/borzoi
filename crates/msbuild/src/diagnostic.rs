//! Diagnostics produced while extracting source-file ordering from a
//! `.fsproj`. Anything we couldn't faithfully evaluate is recorded here
//! rather than silently dropped or silently included (plan D3).

use std::ops::Range;
use std::path::PathBuf;

use crate::{SdkVersion, VersionSpec};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub kind: DiagnosticKind,
    /// Byte span of the offending construct in the original project source.
    /// For diagnostics produced by filesystem-touching helpers that don't
    /// see the project XML (notably [`DiagnosticKind::ImplicitImportPresent`]
    /// from [`crate::detect_implicit_imports`]), this is `0..0` —
    /// there is no meaningful location in the project file to point at.
    pub span: Range<usize>,
    /// Where the construct that triggered this diagnostic actually
    /// lives. See [`DiagnosticOrigin`] — the short version is that
    /// `span` is always a valid offset into the entry project's
    /// source (callers don't need to think about which file produced
    /// it), but consumers that want to suppress noise from imported
    /// SDK/props/targets files can filter on this.
    pub origin: DiagnosticOrigin,
}

/// Whether a diagnostic came from the entry project's own source or
/// from a file the with-imports walker followed into.
///
/// `parse_fsproj` (pure) never emits anything but [`Buffer`]; only
/// [`parse_fsproj_with_imports`](crate::parse_fsproj_with_imports)
/// can emit [`Imported`]. The walker remaps spans from inside imported
/// files to the *entry project's* `<Import>` site (so byte offsets
/// stay valid for the entry source), but the original-file origin is
/// preserved here so the LSP — which only ever shows the buffer — can
/// drop content-level diagnostics produced from inside SDK targets
/// rather than mislabel them as buffer problems.
///
/// [`Buffer`]: DiagnosticOrigin::Buffer
/// [`Imported`]: DiagnosticOrigin::Imported
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticOrigin {
    /// Generated while walking the entry project's own XML. Surfaces
    /// to the user as a real problem with the buffer they're editing.
    Buffer,
    /// Generated while walking the body of an imported file (any
    /// depth: SDK `Sdk.props`/`Sdk.targets`, ancestor
    /// `Directory.Build.props`, an explicit `<Import>` chain). The
    /// span has been remapped to the top-level `<Import>` site in the
    /// entry project, so it's still a valid byte offset, but the
    /// underlying issue lives in a file the buffer's author may not
    /// be able to edit. LSP-style callers typically want to drop
    /// these; build-tooling callers may want to keep them.
    Imported,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiagnosticKind {
    /// `<Import Project="..."/>` encountered while evaluating through
    /// the pure entry point [`crate::parse_fsproj`], which by
    /// design does no IO and therefore cannot follow imports. The
    /// filesystem-touching variant
    /// [`crate::parse_fsproj_with_imports`] follows imports
    /// and emits [`DiagnosticKind::ImportFailed`] only when something
    /// actually goes wrong.
    UnresolvedImport { path: String },
    /// An `<Import>` (explicit) or implicit `Directory.Build.*` file
    /// the with-imports walker tried to follow but could not. The
    /// `path` is what we tried to read (after `$(...)` substitution
    /// and relative-path resolution for explicit imports; the
    /// detected on-disk path for implicit ones). The `reason`
    /// distinguishes recoverable from structural problems —
    /// see [`ImportFailReason`].
    ///
    /// `is_partial` is set whenever any of these fire: an import we
    /// failed to follow may have defined properties our property bag
    /// is now missing, which can cascade into further
    /// `UndefinedProperty` diagnostics downstream.
    ImportFailed {
        path: PathBuf,
        reason: ImportFailReason,
    },
    /// Top-level element we don't know how to interpret: `<Choose>`,
    /// `<Target>`, `<UsingTask>`, `<ItemDefinitionGroup>`, etc.
    UnsupportedConstruct { element: String },
    /// Wildcard characters (`*`, `?`) in an `Include` attribute. Phase 1
    /// does not expand globs (plan D3).
    UnsupportedGlob { pattern: String },
    /// The glob resolver could not reproduce MSBuild's expansion of this
    /// `Include` (with its excludes) exactly, so it spliced nothing — see
    /// [`crate::GlobDecline`].
    GlobDeclined {
        include: String,
        reason: crate::GlobDecline,
    },
    /// `$(Name)` appeared but `Name` wasn't defined anywhere we could see —
    /// not in the project file's already-walked `<PropertyGroup>` elements,
    /// not in the caller's `extra_properties`, and not in the reserved
    /// well-known set. The reference is substituted as the empty string,
    /// matching MSBuild, and this diagnostic records the divergence.
    UndefinedProperty { name: String },
    /// `$(...)` enclosing something other than a bare identifier — e.g.
    /// `$([System.IO.Path]::Combine(a, b))` or `$(Items->'%(Identity)')`.
    /// Phase 2 only models simple property references; the expression is
    /// left literal in the substituted output.
    UnsupportedPropertyExpression { expression: String },
    /// MSBuild's Unix path adjustment of an expanded value turns on what the
    /// evaluation does not know: whether a directory exists relative to the
    /// directory MSBuild runs in, or (on the path that asks no file system)
    /// under the root. `value` is the escaped text adjusted: one piece of the
    /// expansion (a literal run or a reference's value), or the whole of it.
    /// A backslash a reserved, toolset, environment or global property holds
    /// meets the adjustment when it is read, so declining it is what keeps a
    /// value MSBuild would respell from being committed as written.
    PathAdjustmentUndecided { value: String },
    /// `@(Foo)` appeared in an attribute — a reference to another item
    /// list. We have no item evaluator, so we can't expand it.
    UnresolvedItemReference { reference: String },
    /// `%(Metadata)` appeared in an attribute — a metadata reference
    /// used by MSBuild batching. Out of scope for phase 1.
    UnresolvedMetadataReference { reference: String },
    /// `Condition="..."` on a `<PropertyGroup>`, `<ItemGroup>`, item
    /// element, or property element used syntax we don't model
    /// (unsupported functions like `HasTrailingSlash(...)`, arithmetic
    /// comparisons, item references, etc. — see the `condition` module for
    /// the supported subset). Plan D5 has us treat such a condition as
    /// **exclusionary**: we never silently include the containing
    /// construct, since proceeding-as-if-true would leak items
    /// MSBuild might have skipped. The diagnostic records the
    /// divergence so callers can surface it.
    UnsupportedCondition { condition: String },
    /// An item operation that can change a captured item set but is not
    /// modelled here, e.g. `<Compile Remove="..."/>`. Metadata-only Compile
    /// `Update` elements are ignored unless they write `CompileOrder`, since
    /// that metadata participates in the F# target's source ordering.
    UnsupportedItemOperation { operation: String },
    /// A compile-order `<Compile Update>` whose spec MSBuild's lazy evaluator
    /// abandons batching part-way through, leaving the fragments before
    /// `fragment` *stranded*: `LazyItemEvaluator.ComputeItems` removes them
    /// from its batch under their written spelling, not the full-path key it
    /// stored them under, so they apply again at the next flush — to items
    /// `Include`d *after* the `Update` too. Batching stops at a fragment that
    /// repeats an earlier one's path (`Update="a.fs;a.fs"`) or holds a `%`
    /// (an escape). That is an upstream bug the evaluator does not mirror, so
    /// the Compile order is not claimed.
    StrandedUpdatePrefix { update: String, fragment: String },
    /// A `<Compile Update>` (`update` is its spec) that may leave
    /// `LazyItemEvaluator.ComputeItems`'s batch of `Update`s past its first
    /// fragment, stranding the fragments before it to apply late. The
    /// evaluator does not follow the batch, so the Compile order is not
    /// claimed.
    UnmodelledUpdateBatch { update: String },
    /// `<Project Sdk="X">` or `<Import Sdk="X" .../>` was encountered,
    /// the with-imports walker was given an SDK resolver, and the
    /// resolver returned `None` for this SDK identifier — i.e. the
    /// caller could not locate `X` on disk. The walker walks the body
    /// without the SDK's files (so it reaches none of their
    /// `Directory.Build.*` import points) and records this diagnostic so
    /// `is_partial` flips. `name` is the SDK
    /// identifier as it appeared in the XML, *before* any `$(...)`
    /// substitution (we don't substitute SDK names — MSBuild itself
    /// reads them literally).
    SdkNotFound { name: String },
    /// `<Project Sdk="X">` or `<Import Sdk="X" .../>` was encountered
    /// and the SDK resolver located *some* installed copies of `X` but
    /// none of them satisfied the version constraint in scope —
    /// typically a `global.json` pin with its `rollForward` policy, or
    /// (when we ever wire it in) an MSBuild `Sdk="Name/Version"`
    /// per-import pin. The walker falls back to the no-SDK code path
    /// just like `SdkNotFound`, but the user-facing remediation is
    /// different: install a matching version, or relax the constraint.
    ///
    /// `name` is the SDK identifier as it appeared in the XML, pre-
    /// substitution. `spec` is the constraint that filtered them out;
    /// `available` is the sorted list of versions actually present on
    /// disk, so a UI can present both sides without re-walking.
    SdkVersionNotSatisfied {
        name: String,
        spec: VersionSpec,
        available: Vec<SdkVersion>,
    },
    /// A resolver-backed locator SDK (the workload locators) was
    /// encountered and the resolver recognised it, but the on-disk
    /// state is outside the layout envelope it can resolve *exactly* —
    /// a workload set, an install-state pin, ambiguous manifest
    /// versions, a user-local install we weren't given a root for.
    /// Resolving approximately could import the wrong file set, so the
    /// resolver declines instead (the "degrade, don't guess" rule) and
    /// the walker treats the import like a failed one. `reason` is a
    /// short human-readable description of the envelope violation.
    SdkResolutionUnsupported { name: String, reason: String },
    /// `<Project Sdk="X">` or `<Import Sdk="X" .../>` was encountered and
    /// the caller supplied no SDK resolver: the pure
    /// [`crate::parse_fsproj`] never has one, and a
    /// [`crate::parse_fsproj_with_imports`] caller passes `None` when it
    /// could not establish where SDKs live (the LSP does so when SDK
    /// discovery fails, and renders this with discovery's reason). `name`
    /// is the SDK identifier as it appeared in the XML.
    ///
    /// Outside [`Self::hides_unseen_content`] although the SDK's content
    /// never entered the walk: every site that emits it also records a
    /// structural skip (`ProjectSdkUnsupported` / `ExplicitSdkUnsupported`)
    /// at the same span, which carries all of that class's consequences.
    /// Membership would record the one cause twice.
    SdkResolverAbsent { name: String },
    /// One of the well-known files MSBuild implicitly imports —
    /// `Directory.Build.props`, `Directory.Build.targets`, or
    /// `Directory.Packages.props` — exists in the project's ancestor
    /// directories. The fsproj parser does *not* follow these files
    /// (plan D3); this diagnostic exists so a caller (the LSP shell)
    /// can surface the incompleteness rather than silently diverge
    /// from MSBuild. Produced only by
    /// [`crate::detect_implicit_imports`], which is filesystem-
    /// touching and explicitly separate from `parse_fsproj`.
    ///
    /// The `path` is the on-disk location of the discovered file as
    /// constructed by joining the ancestor directory with the well-known
    /// filename — *not* canonicalised. The span carried by the
    /// enclosing [`Diagnostic`] is `0..0` because the discovery has no
    /// source location in the project XML.
    ImplicitImportPresent {
        path: PathBuf,
        kind: ImplicitImportKind,
    },
    /// MSBuild may reject the whole project, for `cause`
    /// ([`RejectionCertainty::Possible`]); see
    /// [`crate::ParsedProject::rejection`], which holds the first certain one,
    /// else the first. The diagnostic sits at the construct, and the item and
    /// define axes name it as their cause.
    MayBeRejected { cause: RejectionCause },
    /// MSBuild rejects the whole project, for `cause`
    /// ([`RejectionCertainty::Certain`]): as [`Self::MayBeRejected`], and a
    /// claim the differentials grade.
    Rejected { cause: RejectionCause },
}

/// Why MSBuild may reject the whole project, and how sure the walk is of it:
/// [`crate::ParsedProject::rejection`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rejection {
    pub certainty: RejectionCertainty,
    pub cause: RejectionCause,
    /// Byte span of the construct in the entry project's source, remapped to
    /// the `<Import>` site for imported files (as [`Diagnostic::span`]).
    pub span: Range<usize>,
    /// Whether the construct lives in the entry project or an imported file.
    pub origin: DiagnosticOrigin,
}

impl Rejection {
    /// The diagnostic that names this rejection as an axis's cause.
    pub fn diagnostic_kind(&self) -> DiagnosticKind {
        let cause = self.cause.clone();
        match self.certainty {
            RejectionCertainty::Possible => DiagnosticKind::MayBeRejected { cause },
            RejectionCertainty::Certain => DiagnosticKind::Rejected { cause },
        }
    }
}

/// How sure the walk is that MSBuild rejects the project.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RejectionCertainty {
    /// MSBuild may reject it: the walk cannot rule the rejection out, and
    /// claims nothing about it. What is graded is the withdrawal alone: no
    /// value is published as the build's, whichever way MSBuild goes.
    Possible,
    /// MSBuild rejects it. A claim: the property-table and import-graph
    /// differentials hold every such verdict to the oracle's rejection. It
    /// needs the construct reached for certain (see
    /// [`crate::ParsedProject::rejection`]); short of that, the same construct
    /// is [`Self::Possible`].
    Certain,
}

/// What may make MSBuild reject the project.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RejectionCause {
    /// An `<Import>` MSBuild may make names no file it can load, and MSBuild
    /// fails the evaluation when it makes one (MSB4019 for a missing file,
    /// MSB4025 for malformed XML, MSB4020/MSB4035 for an empty path).
    /// `project` names the import: its `Project` text as written, or the path
    /// of a file that failed to load. `gate_undecided`:
    /// the walk could not decide the import's condition, which does not
    /// require the file to exist (#820); otherwise the walk took the import
    /// (#845).
    Import {
        project: String,
        gate_undecided: bool,
        why: UnloadableImport,
    },
    /// A `Condition` MSBuild evaluates and throws on: a syntax error, or an
    /// ill-typed operand on the path it evaluates (MSB4086, MSB4092, MSB4113,
    /// …). `condition` is the attribute's text.
    IllegalCondition { condition: String },
    /// A construct MSBuild refuses when it loads the file holding it, before
    /// it evaluates any of it, whatever any condition in the file holds.
    LoadTime(LoadTimeError),
    /// An item operation MSBuild refuses as it builds it, for an item of an
    /// item group it evaluates whatever the group's or the item's condition
    /// holds: a `Remove` with `MatchOnMetadata` that names more than item
    /// types. `item` is the item's type.
    IllegalItemOperation { item: String },
    /// A property expression MSBuild evaluates and throws on (MSB4184): an
    /// indexer out of range, a malformed `[MSBuild]::Version*` operand.
    /// `expression` is the `$(…)` text.
    ThrowingExpression { expression: String },
    /// A `<UsingTask>` MSBuild refuses as it registers the task, without an
    /// expression throwing: `attribute` (`TaskName`, `TaskFactory`,
    /// `AssemblyFile`, `AssemblyName`, a body's `Evaluate`, a parameter's
    /// `ParameterType`, `Output` or `Required`) expanded to `value`, which
    /// the registration does not take (an empty name, a flag that is no
    /// boolean, a type it does not resolve, a body under no task factory).
    /// `task` is the `TaskName` as written.
    UsingTaskRegistration {
        task: String,
        attribute: String,
        value: String,
    },
    /// Two parameters of a `<UsingTask>`'s `<ParameterGroup>` whose names
    /// MSBuild's registry, keyed case-insensitively, takes for one: it fails
    /// on the `second`, after the `first` (MSB1025). `task` is the
    /// `TaskName` as written.
    UsingTaskParameterCollision {
        task: String,
        first: String,
        second: String,
    },
}

/// A construct MSBuild's loader (`ProjectParser`) refuses when it loads a
/// file (#888, #917). Element and attribute names are as MSBuild reads them,
/// prefix included.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoadTimeError {
    /// A property element (or a task output's `PropertyName`) named for a
    /// reserved property (any case), or for one of the names MSBuild reserves
    /// for its own elements (exact case): MSB4004.
    ReservedProperty { name: String },
    /// An item type, or an item's metadatum, named for one of the names
    /// MSBuild reserves for its own elements (MSB4117, MSB4033).
    ReservedItemName { name: String },
    /// A metadatum named for an item-spec modifier (`FullPath`, `Filename`,
    /// …, any case): MSB4033.
    ReservedMetadata { name: String },
    /// An item without a usable `Include`, `Update` or `Remove`: one present
    /// and empty (MSB4035), more than one (MSB4115), or, outside a `<Target>`,
    /// none (MSB4232). `item` is its type.
    ItemWithoutSpec { item: String },
    /// An `<Import>` whose `Project` is absent or empty: MSB4035.
    ImportWithoutProject,
    /// A `<Choose>` whose structure MSBuild refuses: no `<When>` (MSB4085), a
    /// `<When>` without a `Condition` (MSB4035), an `<Otherwise>` out of place
    /// (MSB4082, MSB4084), or nested past MSBuild's ceiling.
    MalformedChoose,
    /// An attribute `element` does not take: MSB4066.
    UnrecognizedAttribute { element: String, attribute: String },
    /// A child `parent` does not take: MSB4067. Text that is not whitespace
    /// is `#text`, a CDATA section `#cdata-section`, and a processing
    /// instruction its target.
    UnrecognizedChild { parent: String, child: String },
    /// An element named with a character MSBuild does not allow in a
    /// property, item or metadatum name: MSB5016.
    InvalidName { name: String },
    /// Any other rule of the loader `element` breaks, as `rule` says: a
    /// required attribute missing or empty, two of a child it takes once, an
    /// `<OnError>` before other content, and the like.
    Malformed { element: String, rule: &'static str },
    /// The project element asks for whitespace to be kept: an `xml:space`
    /// attribute that is not `default`. Under `preserve`, MSBuild's loader
    /// refuses whitespace between elements (MSB4067, an unrecognised
    /// `<#significant-whitespace>`), and a project without any is evaluated
    /// with the whitespace in its bodies kept. Never certain.
    WhitespaceKept,
}

/// Why an import may load no file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnloadableImport {
    /// The walk could not compute the path, so the build's may name no file.
    PathUndecided,
    /// The path is empty, or the import has no `Project` at all.
    NoPath,
    /// The path names no file the walk could load.
    Failed(ImportFailReason),
}

impl DiagnosticKind {
    /// Whether this diagnostic means a *file's worth of content never entered
    /// the walk* — an import we couldn't follow, an SDK we couldn't resolve, an
    /// implicit file we don't follow. Everything such a file might have
    /// declared is therefore unknown to us.
    ///
    /// This is the class, not a judgement about any one axis. Several
    /// consequences hang off it and must agree on membership: the evaluator
    /// goes opaque for later undefined-property reads, raises
    /// [`crate::ParsedProject::items_uncertain`] and
    /// [`crate::ParsedProject::project_references_uncertain`] wherever the
    /// file was named, and the LSP borrows exactly these causes to explain a dropped
    /// `<ProjectReference>` edge set (whose own axis records none). Hence one
    /// public definition rather than a `matches!` per consumer — a new variant
    /// added to the class is then added everywhere at once.
    pub fn hides_unseen_content(&self) -> bool {
        matches!(
            self,
            DiagnosticKind::ImportFailed { .. }
                | DiagnosticKind::UnresolvedImport { .. }
                | DiagnosticKind::SdkNotFound { .. }
                | DiagnosticKind::SdkVersionNotSatisfied { .. }
                | DiagnosticKind::SdkResolutionUnsupported { .. }
                | DiagnosticKind::ImplicitImportPresent { .. }
        )
    }
}

/// Why an `<Import>` (explicit) or implicit `Directory.Build.*` file
/// could not be followed by the with-imports walker. Each variant
/// records enough context to diagnose the failure without re-running
/// the walk — the offending `<Import>` element's range (or `0..0`
/// for implicit imports) is carried by the enclosing
/// [`Diagnostic::span`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportFailReason {
    /// The resolved path does not exist on disk, or is not a regular
    /// file. The most common case: a typo in `Project="…"`, or an
    /// explicit import gated on properties we never resolved.
    ///
    /// Note that a *duplicate* import (a path the evaluation already
    /// imported, including a cycle's back-edge) is not a failure at
    /// all: MSBuild skips it with a warning (MSB4011/MSB4210) and the
    /// evaluation succeeds, so the walker skips it silently.
    NotFound,
    /// We are already `depth` imports deep and refuse to recurse
    /// further. The limit is a defence against runaway recursion —
    /// duplicate imports are skipped, so unbounded depth needs a
    /// fresh path *spelling* per level (e.g. a directory symlink to
    /// `.`), which MSBuild itself would recurse on. Under normal
    /// MSBuild usage real chains are very shallow (project →
    /// `Directory.Build.props` → maybe one or two more).
    DepthLimit { depth: usize },
    /// The imported file was readable but not well-formed XML. The
    /// `message` is the parser's rendered error, including a position
    /// in the imported file (which is more useful than the position in
    /// the *importing* file that the [`Diagnostic::span`] carries).
    MalformedXml { message: String },
    /// Anything else from `std::fs::read_to_string` — permission denied,
    /// I/O error, etc. The message is what the OS told us.
    Io { message: String },
}

/// A `<Compile>` / `<CompileBefore>` / `<CompileAfter>` item (or the
/// `<ItemGroup>` wrapping one) **in a user-authored file** — the entry project
/// or an import that is not part of the SDK installation (`Directory.Build.*`,
/// an explicit `<Import>`) — whose **inclusion we could not determine** because
/// its `Condition` could not be faithfully evaluated. The item set we produced
/// may therefore diverge from MSBuild's *specifically in which source files
/// compile* — the narrow, correctness-relevant subset of
/// [`crate::ParsedProject::is_partial`]. Each is independently surfaceable (the
/// LSP raises one as an editor message) so a consumer can explain *why* it fell
/// back to single-file resolution rather than trusting the Compile order.
///
/// Conditions inside the SDK's *own* targets/props are deliberately **not**
/// recorded here: that machinery (`EnableDefaultItems` default-item globs, the
/// link-metadata group) is conditional in every project and never decides which
/// hand-written sources compile, so flagging it would be pure noise.
///
/// Distinct from the flat [`DiagnosticKind::UndefinedProperty`] /
/// [`DiagnosticKind::UnsupportedCondition`] the same site also emits: those
/// carry no information about *what the condition gated*, so a consumer can't
/// tell a harmless undefined property in an imported SDK target from one that
/// decides whether a file compiles. This type records exactly that distinction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompileConditionUncertainty {
    /// The raw `Condition` attribute text, verbatim (so a UI can show it
    /// without re-reading the project).
    pub condition: String,
    /// Why we couldn't trust the condition's verdict — see
    /// [`CompileConditionReason`].
    pub reason: CompileConditionReason,
    /// Byte span of the conditioned element in the entry project's source,
    /// remapped to the `<Import>` site for imported files (same contract as
    /// [`Diagnostic::span`]).
    pub span: Range<usize>,
    /// Whether the conditioned element lives in the entry project's own source
    /// or an imported file (same meaning as [`Diagnostic::origin`]).
    pub origin: DiagnosticOrigin,
}

/// Why a [`CompileConditionUncertainty`]'s condition couldn't be trusted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileConditionReason {
    /// The condition is within our supported grammar but relied on one or more
    /// properties we never resolved (each was substituted as `""`, per
    /// MSBuild). The verdict — and so the item's inclusion — could be wrong if
    /// the real build defines them. Carries the undefined property names, in
    /// first-seen order.
    UndefinedProperties(Vec<String>),
    /// The condition used syntax outside our supported subset (unsupported
    /// functions, arithmetic, item/metadata references). We treated it as
    /// **exclusionary** (plan D5), so any gated Compile items were dropped —
    /// possibly wrongly.
    Unsupported,
}

/// One concrete reason the captured Compile item set is not trustworthy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompileItemUncertaintyCause {
    pub kind: CompileItemUncertaintyCauseKind,
    /// Byte span of the causal construct in the entry project's source,
    /// remapped to the `<Import>` site for imported files.
    pub span: Range<usize>,
    /// Whether the causal construct lives in the entry project or an imported
    /// file.
    pub origin: DiagnosticOrigin,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompileItemUncertaintyCauseKind {
    /// A diagnostic that directly made the Compile item set untrustworthy:
    /// for example an undefined property while evaluating a Compile condition,
    /// or a failed user import that could have carried Compile items.
    Diagnostic(DiagnosticKind),
    /// A dropped structural construct whose generic diagnostic does not itself
    /// say why Compile items may be missing.
    Structural(StructuralCompileItemUncertainty),
    /// A Compile item's `Include` or `Condition` (or another text deciding the
    /// source set) read a value the walk held from before content it could not
    /// see, which may have rewritten it: `reference` is that text as written,
    /// and `hidden_by` what the walk could not see.
    StaleValue {
        reference: String,
        hidden_by: crate::UntrustedCause,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StructuralCompileItemUncertainty {
    /// The project root SDK could not be evaluated because no SDK resolver was
    /// available. The SDK may have contributed default Compile items.
    ProjectSdkUnsupported { sdk: String },
    /// An explicit `<Import Sdk="...">` could not be evaluated because no SDK
    /// resolver was available.
    ExplicitSdkUnsupported { sdk: String },
    /// An explicit SDK import's `Project` attribute contained unresolved
    /// property syntax, named no file at all, or used a character outside the
    /// path alphabet the walker models, so the import was dropped.
    SdkImportProjectUnresolved { sdk: String, project: String },
    /// A user import that could not be resolved to a definite import
    /// decision, so it was dropped: its `Project` attribute contained
    /// unresolved property syntax, or the resolved path is a
    /// near-duplicate of an already-imported path under Unicode case
    /// folding (where MSBuild's ordinal-ignore-case dedup verdict cannot
    /// be reproduced exactly).
    ImportProjectUnresolved { project: String },
    /// A user-authored `<Choose>` we could not evaluate may add Compile items:
    /// one whose branch decision we could not pin down, with a Compile item in
    /// a still-possible branch, or one MSBuild would refuse to load.
    UnsupportedChoose,
    /// A `Directory.Build.*` import the walk could not decide (#677): MSBuild
    /// may import the file the walk did not, or not import the one it did,
    /// so what it contributes is unknown; and an import of a file only such
    /// an import made, which may or may not be a duplicate. `project` is the
    /// import's `Project` text. `references` says whether that may include
    /// `<ProjectReference>` mutations: always when the file's identity was in
    /// doubt, else only when the file the walk doubted declares some.
    DirectoryBuildImportUndecided { project: String, references: bool },
}

impl StructuralCompileItemUncertainty {
    /// Whether skipping this construct also makes the `<ProjectReference>` list
    /// untrustworthy — i.e. whether it could have carried reference *mutations*
    /// we never saw.
    ///
    /// True for everything except [`Self::UnsupportedChoose`]: `handle_choose`
    /// scans a `<Choose>`'s still-possible branches for reference operations
    /// itself, so a Compile-only branch says nothing about the list, and an
    /// Include-only one stays at worst a missed reference rather than a wrong
    /// list. [`Self::DirectoryBuildImportUndecided`] says for itself.
    ///
    /// Public because a consumer explaining a dropped reference set must borrow
    /// exactly this subset — attributing the drop to a Compile-only `<Choose>`
    /// would name a construct that had nothing to do with it.
    pub fn hides_project_references(&self) -> bool {
        match self {
            StructuralCompileItemUncertainty::UnsupportedChoose => false,
            StructuralCompileItemUncertainty::DirectoryBuildImportUndecided {
                references, ..
            } => *references,
            _ => true,
        }
    }
}

/// One concrete reason the evaluated `DefineConstants` set is not trustworthy —
/// the explaining channel for [`crate::ParsedProject::define_constants_uncertain`],
/// in the mould of [`CompileItemUncertaintyCause`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefineConstantsUncertaintyCause {
    pub kind: DefineConstantsUncertaintyCauseKind,
    /// Byte span of the causal construct in the entry project's source,
    /// remapped to the `<Import>` site for imported files.
    pub span: Range<usize>,
    /// Whether the causal construct lives in the entry project or an imported
    /// file.
    pub origin: DiagnosticOrigin,
}

/// What made the define set untrustworthy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefineConstantsUncertaintyCauseKind {
    /// A diagnostic raised while resolving a user-authored `<DefineConstants>`
    /// write or the condition gating it: an undefined property in the gating
    /// condition, an unsupported condition or property expression, an
    /// unexpanded item/metadata reference in the value.
    Diagnostic(DiagnosticKind),
    /// Content the walk did not enter, described as
    /// [`crate::ParsedProject::hidden_content`] describes it. It may write
    /// `DefineConstants` or import a user file that does, and no later read
    /// need see that write: it may be the last, and the
    /// `$(DefineConstants);FOO` append reads its own name without doubting the
    /// set. So the set is withdrawn wherever the content is, in an SDK file as
    /// in a user's (#843, #862).
    HiddenContent(crate::UntrustedCause),
}

/// One concrete reason the captured package/framework reference set is not
/// trustworthy.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PackageReferenceUncertaintyCause {
    pub kind: PackageReferenceUncertaintyCauseKind,
    /// Byte span of the causal construct in the entry project's source,
    /// remapped to the `<Import>` site for imported files when one exists.
    pub span: Range<usize>,
    /// Whether the causal construct lives in the entry project or an imported
    /// file.
    pub origin: DiagnosticOrigin,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PackageReferenceUncertaintyCauseKind {
    /// A diagnostic that directly made the package/framework reference set
    /// untrustworthy: for example an unsupported condition gating a
    /// `PackageReference`, or a failed user import that could have carried
    /// dependency items.
    Diagnostic(DiagnosticKind),
    /// A dropped structural construct whose generic diagnostic does not itself
    /// say why package/framework references may be missing.
    Structural(StructuralPackageReferenceUncertainty),
    /// A `Directory.Packages.props` file exists up-tree. Central Package
    /// Management data is not folded into the captured package set yet.
    DirectoryPackagesProps { path: PathBuf },
    /// The evaluated `ManagePackageVersionsCentrally` property is true.
    ManagePackageVersionsCentrally,
    /// A `<PackageVersion>` item would contribute central package metadata.
    PackageVersion,
    /// A `<GlobalPackageReference>` item would contribute an implicit package.
    GlobalPackageReference,
    /// An `<ItemDefinitionGroup>` can contribute default package metadata we do
    /// not thread through later `PackageReference` items.
    ItemDefinitionDefault,
    /// A package/framework capture leaned on a property value the property
    /// pass could not pin down: its metadata/condition read a property whose
    /// write was gated on input we couldn't evaluate (an undefined property
    /// the real build may supply, an unsupported condition, or SDK-tainted
    /// input). SDK provenance alone is not a cause: a cleanly-evaluated SDK
    /// property write is exact under the multi-pass evaluation, so only a
    /// genuinely untrusted write poisons its readers.
    SdkDependencyItemPropertyEvaluation,
    /// A `Remove`/unsupported operation can change the dependency item set.
    UnsupportedItemOperation { item: String, operation: String },
    /// A `<PackageReference Update>` spec listed the same identity more than
    /// once (`Update="Gamma;Gamma"`). MSBuild's lazy item evaluator handles a
    /// duplicate-bearing spec through a dictionary path that applies the
    /// update **position-independently** — it modifies even `Include`s
    /// declared later — where a unique spec only modifies prior `Include`s
    /// (dotnet 10 probe). We model only the ordered semantics, so the
    /// captured set can't be trusted.
    DuplicateUpdateIdentity { id: String },
    /// A `<PackageReference Update>` (`update` is its spec) that may leave
    /// MSBuild's batch of `Update`s past its first fragment
    /// ([`DiagnosticKind::UnmodelledUpdateBatch`]).
    UnmodelledUpdateBatch { update: String },
    /// The package/framework identity could not be reduced to literal item
    /// identities.
    UnevaluableIdentity { value: String },
    /// The package/framework identity uses MSBuild glob semantics.
    UnsupportedGlob { pattern: String },
    /// The `Exclude` set could not be reduced to literal item identities.
    UnsupportedExclude { value: String },
    /// A metadata value depended on item/metadata evaluation or substitution we
    /// do not model.
    UnevaluableMetadata { name: String, value: String },
    /// A metadatum is spelt so that MSBuild may read it apart from the
    /// capture, which trims it: padded, holding a backslash MSBuild's Unix path
    /// fixup may rewrite, or written as an attribute holding a `<`, which
    /// MSBuild parses as XML. The item tables read such a value as MSBuild
    /// does or mark it inexact themselves, so this cause says nothing about
    /// them.
    UnreadableMetadata { name: String, value: String },
    /// A declaring `<PackageReference Include="...">` had no local version or
    /// version override, so the effective version is determined elsewhere.
    VersionlessPackageReference { id: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StructuralPackageReferenceUncertainty {
    /// The project root SDK could not be evaluated. The SDK may have
    /// contributed implicit package/framework references.
    ProjectSdkUnsupported { sdk: String },
    /// An explicit `<Import Sdk="...">` could not be evaluated.
    ExplicitSdkUnsupported { sdk: String },
    /// An explicit SDK import's `Project` attribute contained unresolved
    /// property syntax, named no file at all, or used a character outside the
    /// path alphabet the walker models, so the import was dropped.
    SdkImportProjectUnresolved { sdk: String, project: String },
    /// An import that could not be resolved to a definite import decision,
    /// so it was dropped: unresolved property syntax in its `Project`
    /// attribute, or a near-duplicate of an already-imported path under
    /// Unicode case folding. See the compile-side twin
    /// [`StructuralCompileItemUncertainty::ImportProjectUnresolved`].
    ImportProjectUnresolved { project: String },
    /// A `<Choose>` we could not evaluate may add package/framework
    /// references: one whose branch decision we could not pin down, with a
    /// package-affecting item in a still-possible branch, or one MSBuild would
    /// refuse to load.
    UnsupportedChoose,
}

/// Which MSBuild-implicit file was discovered. The three are distinct
/// import points (different stages in MSBuild's evaluation) so we
/// preserve the distinction rather than collapse to a single kind.
///
/// The `Ord` derive uses declaration order: `DirectoryBuildProps <
/// DirectoryBuildTargets < DirectoryPackagesProps`. Tests rely on
/// this for stable ordering, and it matches the in-walk emission
/// order from [`crate::detect_implicit_imports`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ImplicitImportKind {
    /// `Directory.Build.props` — imported before the project's own
    /// `PropertyGroup`s. Common carrier for cross-project property
    /// defaults.
    DirectoryBuildProps,
    /// `Directory.Build.targets` — imported after the project body.
    /// Typically defines or overrides build targets.
    DirectoryBuildTargets,
    /// `Directory.Packages.props` — Central Package Management
    /// version file (NuGet feature).
    DirectoryPackagesProps,
}
