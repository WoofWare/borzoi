//! Two-pass evaluation of a parsed `.fsproj` XML tree, mirroring
//! MSBuild's own pass ordering:
//!
//!   1. **Property pass** — a document-order walk over the project body
//!      and (in the with-imports variant) every followed import.
//!      `<PropertyGroup>`s evaluate as encountered, so a property VALUE's
//!      forward reference to a name defined later in the file reads empty
//!      and emits [`DiagnosticKind::UndefinedProperty`]. Each
//!      `<ItemGroup>` encountered is *deferred* — recorded, in encounter
//!      order, for the second pass ([`State::defer_item_group`]).
//!   2. **Item pass** ([`item_pass::replay_deferred_item_groups`]) — the
//!      deferred groups evaluate against the now-final property table, so
//!      an item's `Include`, `Condition`, and metadata see properties no
//!      matter where in the import graph they were written. This matches
//!      MSBuild, which finalises every property before evaluating any
//!      item.
//!
//! `Condition` attributes are evaluated on every gated construct
//! (`<ItemGroup>`, `<PropertyGroup>`, individual `<Compile>` items,
//! individual property elements), each against the property table of its
//! own pass. Conditions outside the supported subset surface as
//! [`DiagnosticKind::UnsupportedCondition`] and treat the containing
//! construct as **excluded** — plan D5's "never silently include"
//! stance, since we can't tell whether the construct would have
//! contributed any items. Conditions that we *can* evaluate but only
//! by treating an unknown `$(Name)` reference as the empty string
//! emit [`DiagnosticKind::UndefinedProperty`] for each such name, so
//! the project is marked partial: our property map may be missing
//! values MSBuild itself would have seen.
//!
//! Property values and item attributes have `$(Name)` substituted
//! against a map seeded with caller globals and well-known MSBuild
//! path properties, then extended by the project's own
//! `<PropertyGroup>` writes.
//!
//! What the pure entry point still doesn't model: `<Import>`, `<Choose>`,
//! glob expansion, item-list `@(...)` and metadata `%(...)` references.
//! Each emits a [`Diagnostic`] and marks the project partial.
//!
//! ## Two entry points
//!
//! [`walk`] is the pure document-order walker reached from
//! [`super::parse_fsproj`]: no IO, `<Import>` elements emit
//! [`DiagnosticKind::UnresolvedImport`].
//!
//! [`walk_with_imports`] is the filesystem-touching variant reached from
//! [`super::parse_fsproj_with_imports`]. It follows explicit `<Import>`
//! (substituting `$(...)` in the path, resolving relative to the
//! importing file, recursing depth-limited, with duplicate imports —
//! cycles included — skipped exactly as MSBuild skips them), the SDK's
//! own `Directory.Build.props` / `Directory.Build.targets` imports among
//! them. Walked-imported files share the same [`State`] as the project
//! body, so properties they define become visible to substitutions
//! further down the project file.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::ops::Range;
use std::path::{Path, PathBuf};

use roxmltree::{Document, Node};

use crate::document::attribute;

use super::condition;
use super::diagnostic::{
    CompileConditionReason, CompileConditionUncertainty, CompileItemUncertaintyCause,
    CompileItemUncertaintyCauseKind, DefineConstantsUncertaintyCause,
    DefineConstantsUncertaintyCauseKind, Diagnostic, DiagnosticKind, DiagnosticOrigin,
    ImportFailReason, PackageReferenceUncertaintyCause, PackageReferenceUncertaintyCauseKind,
    StructuralCompileItemUncertainty, StructuralPackageReferenceUncertainty,
};
use super::dotnet_io;
use super::imports::normalise;
use super::observed::{self, EntryKind, Observer, ReadCounts, ReadSet};
use super::properties::escaping::Escaped;
use super::properties::trust::{
    OpacityCause, PropertyProvenance, RefusedOutcome, ResolvedProvenance, SdkPackagePropertyTaint,
    StaleOutcome, TaintOutcome, Trust, UndefinedBecause, UnpinnedOutcome, UnpinnedRoot,
};
use super::properties::{self, Issue, PropertyMap, Provenanced};
use super::{
    FrameworkReference, GlobRequest, GlobResolver, GlobalPackageReference, ItemKind,
    ItemMetadataValue, PackageRefOp, PackageReference, PackageVersion, ParsedProject, ResolvedItem,
    SdkPaths, SdkResolution, SdkResolveError, SdkResolver,
};

mod directory_build;
#[cfg(any(test, feature = "test-support"))]
pub(crate) mod executor;
#[cfg(test)]
pub(crate) use directory_build::DirectoryBuildFile;
mod item_pass;
mod item_spec;
mod loader;
pub(crate) use loader::is_valid_name;
pub(crate) mod property_reads;
#[cfg(any(test, feature = "test-support"))]
pub(crate) mod reads;
mod rejection;
use item_pass::{
    CapturedPackageReference, CurrentFile, DeferredGroupKind, DeferredItemGroup,
    RetainedImportedFile, item_key, replay_deferred_item_groups,
};
use property_reads::PropertyRead;
#[cfg(any(test, feature = "test-support"))]
use reads::{EvaluationReads, ReadProbe};
#[cfg(any(test, feature = "test-support"))]
pub(crate) use rejection::element_inner_contents;

/// Maximum recursion depth for `<Import>` following. MSBuild itself
/// caps at ~100; we pick a number well above any sane real-world
/// project's chain depth (project → `Directory.Build.props` → maybe
/// one or two more is typical) but well below the stack-overflow
/// danger zone for hostile inputs.
const MAX_IMPORT_DEPTH: usize = 64;

/// The assembly MSBuild registers its built-in tasks from, as
/// `Microsoft.Common.tasks` names it.
#[cfg(any(test, feature = "test-support"))]
const MSBUILD_TASKS_ASSEMBLY: &str = "Microsoft.Build.Tasks.Core, Version=15.1.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a";

/// Pure walker reachable from [`super::parse_fsproj`]: no IO, every
/// `<Import>` element produces an [`DiagnosticKind::UnresolvedImport`]
/// diagnostic and is *not* followed.
pub fn walk(
    doc: &Document<'_>,
    project_path: &Path,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
) -> ParsedProject {
    // The pure walker follows no import and resolves no SDK, so nothing
    // reaches the observer; `parse_fsproj` promises that.
    let observer = Observer::new();
    let first = |second_walk: bool| {
        pure_walk(
            doc,
            project_path,
            extra_properties,
            environment,
            &observer,
            second_walk,
        )
    };
    let mut state = first(false);
    if state.second_walk_needed.get() {
        let second = first(true);
        state.adopt_second_walk(second);
    }
    #[cfg(feature = "test-support")]
    state.record_published_sites();
    let project = state.into_project();
    assert!(
        observer.finish().0.is_empty(),
        "the pure walker observed the file system"
    );
    project
}

/// [`walk`]'s walk, the first or the second ([`State::second_walk`]), up to
/// its publication.
fn pure_walk<'r>(
    doc: &Document<'_>,
    project_path: &Path,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    observer: &'r Observer,
    second_walk: bool,
) -> State<'r> {
    let root = doc.root_element();
    let local_overrides = collect_local_overrides(root);
    let mut state = State::new(
        project_path,
        extra_properties,
        environment,
        &local_overrides,
        false,
        None,
        None,
        None,
        observer,
    );
    state.second_walk = second_walk;
    let project_dir = project_path.parent().unwrap_or_else(|| Path::new(""));
    state
        .foreign_definitions
        .record_document(root, project_path);
    // MSBuild loads the project before it evaluates any of it.
    rejection::judge_load_time(root, &mut state);
    // SDK resolution requires IO, which the pure walker doesn't do.
    // Surface the attribute so the caller knows the result may be
    // incomplete (Compile defaults, etc.). Mirrors what
    // `walk_with_imports` does in the no-resolver branch — including marking
    // the Compile set uncertain, since the SDK's (possibly default-item)
    // contributions never ran.
    if let Some(sdk) = attribute(root, "Sdk").as_deref() {
        state.push(
            DiagnosticKind::SdkResolverAbsent {
                name: sdk.to_string(),
            },
            root.range(),
        );
        state.mark_structural_skip(
            StructuralCompileItemUncertainty::ProjectSdkUnsupported {
                sdk: sdk.to_string(),
            },
            root.range(),
        );
    }
    walk_doc_body(root, project_dir, &mut state);
    replay_deferred_item_groups(doc, &mut state);
    state
}

/// With-imports walker reachable from [`super::parse_fsproj_with_imports`].
///
/// The import graph is the document's own, as MSBuild's is. A root `Sdk`
/// attribute imports the SDK's `Sdk.props` before the body and `Sdk.targets`
/// after it; every other file arrives through an `<Import>` some file makes,
/// under that import's own condition, at that import's position. All share
/// one [`State`], so properties written by an earlier file are visible to
/// substitutions in later ones, as in MSBuild's left-to-right evaluation.
///
/// `Directory.Build.props` and `.targets` arrive the same way: through the
/// SDK's own imports in `Microsoft.Common.props` and `.targets`, so a project
/// no SDK reaches gets neither. Where the walk cannot decide such an import
/// point, the whole evaluation is uncertain from there, and the file is
/// walked doubted ([`directory_build`]).
///
/// When the resolver does not know the SDK the walker emits
/// [`DiagnosticKind::SdkNotFound`]; when `sdk_resolver` is `None`, the SDK
/// attribute surfaces as [`DiagnosticKind::SdkResolverAbsent`], as in the
/// pure walker. Either way the body is still walked.
#[allow(clippy::too_many_arguments)]
pub fn walk_with_imports<'r>(
    doc: &Document<'_>,
    project_path: &Path,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    implicit_props: Option<&Path>,
    implicit_targets: Option<&Path>,
    detected_packages_props: Option<&Path>,
    sdk_resolver: Option<&'r SdkResolver<'r>>,
    glob_resolver: Option<&'r GlobResolver<'r>>,
    startup_directory: Option<&Path>,
    observer: &'r Observer,
    #[cfg(any(test, feature = "test-support"))] probe: Option<&ReadProbe>,
) -> Walked {
    let first = |second_walk: bool| {
        walk_imported(
            doc,
            project_path,
            extra_properties,
            environment,
            implicit_props,
            implicit_targets,
            detected_packages_props,
            sdk_resolver,
            glob_resolver,
            startup_directory,
            observer,
            second_walk,
        )
    };
    let mut state = first(false);
    if state.second_walk_needed.get() {
        let second = first(true);
        state.adopt_second_walk(second);
    }
    #[cfg(feature = "test-support")]
    state.record_published_sites();
    #[cfg(any(test, feature = "test-support"))]
    let reads = probe.map(|probe| state.read_probe(probe));
    let project = state.into_project();
    // The published reads answer every name as the probe's read of it does:
    // the table enumerates only some names, and the rest must fall to the
    // rule it states for them.
    #[cfg(any(test, feature = "test-support"))]
    if let Some(reads) = &reads {
        for (name, read) in &reads.properties {
            assert_eq!(
                project.property(name),
                *read,
                "the published read of `{name}` differs from the walk's"
            );
        }
    }
    Walked {
        project,
        #[cfg(any(test, feature = "test-support"))]
        reads,
    }
}

/// [`walk_with_imports`]'s walk, the first or the second
/// ([`State::second_walk`]), up to its publication.
#[allow(clippy::too_many_arguments)]
fn walk_imported<'r>(
    doc: &Document<'_>,
    project_path: &Path,
    extra_properties: &HashMap<String, String>,
    environment: &HashMap<String, String>,
    implicit_props: Option<&Path>,
    implicit_targets: Option<&Path>,
    detected_packages_props: Option<&Path>,
    sdk_resolver: Option<&'r SdkResolver<'r>>,
    glob_resolver: Option<&'r GlobResolver<'r>>,
    startup_directory: Option<&Path>,
    observer: &'r Observer,
    second_walk: bool,
) -> State<'r> {
    let root = doc.root_element();
    let local_overrides = collect_local_overrides(root);
    let mut state = State::new(
        project_path,
        extra_properties,
        environment,
        &local_overrides,
        true,
        sdk_resolver,
        glob_resolver,
        startup_directory,
        observer,
    );
    state.second_walk = second_walk;
    // The entry project is never inside an SDK.
    state
        .foreign_definitions
        .record_document(root, project_path);
    // MSBuild loads the project before it evaluates any of it, or
    // resolves its SDK.
    rejection::judge_load_time(root, &mut state);
    // Seed `imports_seen` with the entry project so an import that names
    // the entry — directly or through a chain — is skipped the way
    // MSBuild skips it (warning MSB4210, "attempting to import itself";
    // the evaluation succeeds).
    state.imports_seen.insert(import_dedup_key(project_path));
    state
        .imports_seen_fuzzy
        .insert(import_dedup_fuzzy_key(project_path));
    state
        .walked_files
        .insert(canonicalise_or_normalise(observer, project_path));
    state
        .directory_build
        .discover(implicit_props, implicit_targets);
    let project_dir = project_path.parent().unwrap_or_else(|| Path::new(""));

    // The entry root offers its `DefaultTargets` before its implicit SDK
    // imports, as each imported root does in [`walk_external_file`].
    latch_default_targets(root, &mut state);

    // The project root's SDK: `Sdk.props` before the body and `Sdk.targets`
    // after it, the import-site span the root `<Project>` element, where the
    // `Sdk="X"` attribute lives. MSBuild's explicit form, `<Project>` with no
    // `Sdk` attribute but body `<Import Sdk="X" Project="Sdk.props"/>` and
    // `Sdk.targets`, is equivalent when those imports are the body's first and
    // last elements, and only then does [`find_explicit_sdk_promotion`] hoist
    // them to the same positions (so the entry's SDK is recorded the same way),
    // spanned at the user's own `<Import>` elements. The ranges it returns are
    // marked in `state.hoisted_sdk_imports` so the body walk skips them:
    // walking `Sdk.targets` in the body would register it first and make the
    // bottom import the skipped duplicate.
    let (sdk_props_to_splice, sdk_targets_to_splice) = match resolve_project_sdk(root, &mut state) {
        Some(sdk_paths) => {
            // The entry project's own root `Sdk` *is* the framework SDK —
            // record it (the one place we do).
            state.record_sdk_root(&sdk_paths.root);
            (
                Some((sdk_paths.props, root.range())),
                Some((sdk_paths.targets, root.range())),
            )
        }
        None => match find_explicit_sdk_promotion(root, &state) {
            Some(promotion) => {
                // The entry's promoted explicit-form SDK — the same framework
                // SDK in `<Import Sdk=... Project="Sdk.props"/>` spelling.
                state.record_sdk_root(&promotion.sdk_paths.root);
                state
                    .hoisted_sdk_imports
                    .insert(promotion.props_range.clone());
                let targets = promotion.targets_range.map(|range| {
                    state.hoisted_sdk_imports.insert(range.clone());
                    (promotion.sdk_paths.targets, range)
                });
                (
                    Some((promotion.sdk_paths.props, promotion.props_range)),
                    targets,
                )
            }
            None => (None, None),
        },
    };

    if let Some((props, span)) = sdk_props_to_splice.as_ref() {
        walk_external_file(props, span.clone(), &mut state);
    }

    walk_doc_body(root, project_dir, &mut state);

    if let Some((targets, span)) = sdk_targets_to_splice.as_ref() {
        walk_external_file(targets, span.clone(), &mut state);
    }
    // Every import point the walk could reach is behind it, so a
    // `Directory.Build.*` file whose point it never reached is settled here.
    directory_build::settle_unaccounted(&mut state);

    // The property pass is complete — every import has been followed and
    // every `<PropertyGroup>` evaluated. Run the item pass against the
    // final property table.
    replay_deferred_item_groups(doc, &mut state);

    // A `Directory.Packages.props` detected up-tree holds central package
    // versions (and can enable CPM), so a walk that never reached it has
    // an incomplete/unversioned captured set. When the walk *did* import
    // it — via the real chain `Sdk.props` → `Microsoft.Common.props` →
    // `NuGet.props` → `$(DirectoryPackagesPropsPath)` — its contents are
    // ordinary captured state and need no blanket flag; anything still
    // untrustworthy about them is reported by its own precise cause.
    // Conservative on purpose in the other direction: the walk may have
    // skipped the file because NuGet's own gates said so (e.g.
    // `ImportDirectoryPackagesProps=false`), which a real build would
    // also skip — distinguishing that certain skip from "chain never
    // reached NuGet.props" is a future refinement.
    // A walked central-package import point also discharges: when a repo
    // redirects `DirectoryPackagesPropsPath` away from the detected
    // ancestor and the chain imported the redirect target, that ancestor
    // is not part of the real build either, and the file that IS got
    // captured like any other import. The check is *provenance* — the
    // file walked through the `$(DirectoryPackagesPropsPath)`-shaped
    // import, cross-checked against the final property value — because
    // every final-state signal (the `CentralPackageVersionsFileImported`
    // marker, a path value that happens to name some walked file) can be
    // written by a project without any central file having been
    // evaluated.
    let redirected_central_file_walked = state
        .walked_directory_packages_props_import
        .as_ref()
        .is_some_and(|walked| {
            // No consumer to protect: the discharge this decides never fires
            // on a real SDK chain (P2′ of
            // `docs/msbuild-value-carried-provenance-plan.md`).
            state
                .lookup
                .get_unescaped_ignoring_trust("DirectoryPackagesPropsPath")
                .map(|raw| raw.trim().replace('\\', "/"))
                .filter(|path| !path.is_empty())
                .is_some_and(|path| {
                    canonicalise_or_normalise(observer, Path::new(&path)) == *walked
                })
        });
    if let Some(path) = detected_packages_props
        && !redirected_central_file_walked
        && !state
            .walked_files
            .contains(&canonicalise_or_normalise(observer, path))
    {
        state.package_references_uncertain = true;
        state
            .package_reference_uncertainties
            .push(PackageReferenceUncertaintyCause {
                kind: PackageReferenceUncertaintyCauseKind::DirectoryPackagesProps {
                    path: path.to_path_buf(),
                },
                span: 0..0,
                origin: DiagnosticOrigin::Imported,
            });
    }
    state
}

/// [`walk_with_imports`]'s result.
pub struct Walked {
    pub project: ParsedProject,
    /// The walk's answer to the caller's [`ReadProbe`], when it passed one.
    /// Only the differential tests probe the walk.
    #[cfg(any(test, feature = "test-support"))]
    pub reads: Option<EvaluationReads>,
}

#[derive(Debug, Clone)]
struct OrderedResolvedItem {
    order: usize,
    item: ResolvedItem,
    /// The item's identity as MSBuild records it — the `Include` fragment,
    /// trimmed and decoded, which is what a later `Remove`/`Exclude` matches and
    /// what `@(…)` hands on. `None` for an item spliced from the glob
    /// resolver, which returns paths rather than the relative spelling MSBuild
    /// derives from the glob.
    identity: Option<String>,
    /// The item as an item table reads it, metadata and item-definition
    /// defaults included, for a `<ProjectReference>` declared by a literal
    /// identity. `None` for a Compile item and for one spliced from the glob
    /// resolver.
    #[cfg(any(test, feature = "test-support"))]
    row: Option<EvaluatedItem>,
}

/// The walk's items as the caller receives them, each [`ResolvedItem::include`]
/// MSBuild's `FullPath` of it: the lexical full path, so `sub/../a.fs` is
/// `a.fs` and `sub//a.fs` is `sub/a.fs` beside the project. The walk keeps
/// each spelling as written until here, since MSBuild compares some spellings
/// as written (`crate::glob::compares_unnormalised`).
fn into_resolved_items(items: Vec<OrderedResolvedItem>) -> Vec<ResolvedItem> {
    items
        .into_iter()
        .map(|ordered| ResolvedItem {
            include: item_full_path(&ordered.item.include),
            ..ordered.item
        })
        .collect()
}

/// `Path.GetFullPath` of a rooted item path on a Unix host, trailing separator
/// kept: the file matcher's [`crate::glob::file_matcher::full_path`]. A path
/// that is not UTF-8 is collapsed by components, its trailing separator
/// restored. Windows' rule (drive-relative paths, verbatim prefixes, a `:`
/// inside a segment) is not modelled, so there the path is kept as joined.
///
/// A path holding a NUL (a decoded `%00`) has no full path in MSBuild
/// (`GetFullPath` throws), and is kept as joined too: collapsing a `..` past
/// its NUL-bearing segment would name a real file MSBuild never names.
fn item_full_path(path: &Path) -> PathBuf {
    if !cfg!(unix) || path.as_os_str().as_encoded_bytes().contains(&0) {
        return path.to_path_buf();
    }
    if let Some(text) = path.to_str()
        && text.starts_with('/')
    {
        return PathBuf::from(crate::glob::file_matcher::full_path(text));
    }
    let full = normalise(path);
    if path.as_os_str().as_encoded_bytes().last() == Some(&b'/') && full.parent().is_some() {
        let mut text = full.into_os_string();
        text.push("/");
        PathBuf::from(text)
    } else {
        full
    }
}

/// Examine the project root's `Sdk` attribute and decide whether the
/// SDK chain will handle the import job. Four outcomes:
///   * no attribute → returns `None`, caller takes the Directory.Build.*
///     path silently;
///   * attribute present, resolver supplied and returns `Ok(paths)` →
///     returns those paths, no diagnostic;
///   * attribute present but resolver missing → emits
///     [`DiagnosticKind::SdkResolverAbsent`] and returns `None`;
///   * attribute present and resolver returned an `Err` → emits the
///     diagnostic matching the [`SdkResolveError`] variant (see
///     [`crate::SdkResolver`] for the mapping) and returns `None`.
///
/// Fall-back semantics let an unknown SDK degrade gracefully rather
/// than producing a project with no imports at all: the real build
/// would fail outright, but as a parser we'd rather still surface a
/// best-effort Compile list and let the caller decide what to do with
/// the diagnostic.
fn resolve_project_sdk(root: Node<'_, '_>, state: &mut State<'_>) -> Option<SdkPaths> {
    let sdk = attribute(root, "Sdk")?;
    let sdk: &str = &sdk;
    let Some(resolver) = state.sdk_resolver else {
        state.push(
            DiagnosticKind::SdkResolverAbsent {
                name: sdk.to_string(),
            },
            root.range(),
        );
        // The SDK couldn't be evaluated (no resolver — e.g. the LSP found no
        // `dotnet`), so its default-item machinery never ran. Our Compile list
        // is then a *subset* (the body's explicit items only); for a project
        // relying on default items it's incomplete, so the Compile set is
        // untrustworthy. (Cross-assembly resolution needs the SDK packs anyway,
        // which are equally absent.)
        state.mark_structural_skip(
            StructuralCompileItemUncertainty::ProjectSdkUnsupported {
                sdk: sdk.to_string(),
            },
            root.range(),
        );
        return None;
    };
    match resolver(sdk, state.observer) {
        // SDK-root *recording* (for `ParsedProject::resolved_sdk_root`) is the
        // entry caller's responsibility; but the *tolerance* set must include
        // every resolved SDK — entry, nested, and via `<Import Sdk=…>` — so its
        // own conditional default-item machinery isn't mistaken for user intent.
        Ok(SdkResolution::Single(paths)) => {
            state.note_sdk_tolerance(&paths.root);
            Some(paths)
        }
        Ok(SdkResolution::Roots(_)) => {
            // A locator-style resolution has no Sdk.props/Sdk.targets entry
            // points, so it cannot back the `<Project Sdk="…">` shorthand.
            // No real project names a locator here; degrade like an
            // unresolvable SDK rather than inventing entry points.
            state.push(
                DiagnosticKind::UnsupportedConstruct {
                    element: format!("Project Sdk={sdk:?} (locator-style resolution)"),
                },
                root.range(),
            );
            state.mark_structural_skip(
                StructuralCompileItemUncertainty::ProjectSdkUnsupported {
                    sdk: sdk.to_string(),
                },
                root.range(),
            );
            None
        }
        Err(err) => {
            state.push(sdk_error_to_diagnostic(sdk, err), root.range());
            None
        }
    }
}

/// The body pre-scan's result when a project uses MSBuild's explicit
/// SDK form (no root `Sdk` attribute, `<Import Sdk="X" Project="Sdk.props"/>`
/// inside the body) and we want to splice the SDK chain at root-equivalent
/// positions. `props_range` is the byte range of the body Import node we
/// promoted; `targets_range` is the matching `Sdk.targets` body Import
/// if one exists (`None` if the project only declared `Sdk.props`).
/// Both ranges are added to `state.hoisted_sdk_imports` so the body
/// walk skips them on second encounter — without that, a body-position
/// walk of `Sdk.targets` would register the file before the bottom
/// splice, turning the splice into the skipped duplicate.
struct ExplicitSdkPromotion {
    sdk_paths: SdkPaths,
    props_range: Range<usize>,
    targets_range: Option<Range<usize>>,
}

/// When the project root has *no* `Sdk` attribute and its body opens
/// with `<Import Sdk="X" Project="Sdk.props"/>` *as the very first
/// element child*, hoist that import — and the matching trailing
/// `Sdk.targets` — to the OUTERMOST splice positions, just like the
/// root-Sdk shorthand. Without this, `walk_with_imports` would splice
/// `Directory.Build.props` before the body, and the body's
/// `Sdk.props` import would walk *after* Directory.Build.props — the
/// reverse of MSBuild's effective ordering, causing
/// `UndefinedProperty` diagnostics from a Directory.Build.props that
/// conditions on SDK-supplied names.
///
/// Canonical-position discipline (deliberately narrow, so promotion
/// never reorders user-visible work):
///   * `Sdk.props` must be the **first** element child of root. Any
///     preceding `<PropertyGroup>`, `<ItemGroup>`, etc. would in
///     MSBuild evaluate *before* the SDK chain; promoting silently
///     reverses that order.
///   * `Sdk.targets` (if promoted at all) must be the **last** element
///     child of root, and carry the same SDK name. Anything after it
///     would in MSBuild run *after* Sdk.targets; promotion reverses
///     that too. When something trails the import we leave it for the
///     body walk in-place.
///   * `<ImportGroup>` wrappers are not promotion candidates: the
///     root-Sdk shorthand expands to bare `<Import>` elements at root
///     position, so an `<ImportGroup>`-wrapped import is not
///     semantically equivalent.
///   * Conditional imports (any `Condition` attribute) are left to the
///     body walk — promoting would silently bypass the gate.
///   * If the SDK resolver is missing or returns `Err`, we return
///     `None` and let the body walk emit the diagnostic naturally at
///     its in-body position.
///
/// Emits no diagnostics: promotion is silent. Callers gate the splice
/// on the returned `Some(_)` and mark `state.hoisted_sdk_imports` for
/// the skip-on-body-walk contract.
fn find_explicit_sdk_promotion(
    root: Node<'_, '_>,
    state: &State<'_>,
) -> Option<ExplicitSdkPromotion> {
    if root.has_attribute("Sdk") {
        return None;
    }
    let resolver = state.sdk_resolver?;

    let mut element_children = root.children().filter(Node::is_element);
    let first = element_children.next()?;
    let (props_node, sdk_name) = canonical_sdk_import(first, "Sdk.props")?;
    // Promotion needs the canonical entry points; a locator-style
    // resolution has none, so it is not a promotion candidate (the body
    // walk handles the import naturally).
    let sdk_paths = match resolver(&sdk_name, state.observer).ok()? {
        SdkResolution::Single(paths) => paths,
        SdkResolution::Roots(_) => return None,
    };

    // `Sdk.targets` only promotes when it is the *last* element child
    // of root. Re-scan to find the last element; if it's different from
    // `props_node` and is a matching canonical `Sdk.targets`, promote
    // it. (A project with only `Sdk.props` and no `Sdk.targets` still
    // promotes the props import; targets stays unspliced.)
    let last = root.children().rfind(Node::is_element)?;
    let targets_range = if last.range() == props_node.range() {
        // Only one element child total — `Sdk.props` itself. No
        // `Sdk.targets` to promote.
        None
    } else {
        canonical_sdk_import(last, "Sdk.targets")
            .filter(|(_, name)| *name == sdk_name)
            .map(|(node, _)| node.range())
    };

    Some(ExplicitSdkPromotion {
        sdk_paths,
        props_range: props_node.range(),
        targets_range,
    })
}

/// Treat `node` as a canonical `<Import Sdk="X" Project="<expected_project>"/>`:
/// it must be an `<Import>` element with no `Condition` attribute, an
/// `Sdk` attribute, and a `Project` attribute matching
/// `expected_project`. Returns the node and the `Sdk` name on success.
fn canonical_sdk_import<'a, 'input>(
    node: Node<'a, 'input>,
    expected_project: &str,
) -> Option<(Node<'a, 'input>, std::borrow::Cow<'a, str>)> {
    if node.tag_name().name() != "Import" {
        return None;
    }
    if node.has_attribute("Condition") {
        return None;
    }
    let sdk_name = attribute(node, "Sdk")?;
    if attribute(node, "Project").as_deref() != Some(expected_project) {
        return None;
    }
    Some((node, sdk_name))
}

/// Map a resolver-side [`SdkResolveError`] to the matching
/// [`DiagnosticKind`]. Pulled out so the project-root and `<Import Sdk=>`
/// handlers stay consistent.
fn sdk_error_to_diagnostic(sdk_name: &str, err: SdkResolveError) -> DiagnosticKind {
    match err {
        SdkResolveError::NotFound => DiagnosticKind::SdkNotFound {
            name: sdk_name.to_string(),
        },
        SdkResolveError::VersionNotSatisfied { spec, available } => {
            DiagnosticKind::SdkVersionNotSatisfied {
                name: sdk_name.to_string(),
                spec,
                available,
            }
        }
        SdkResolveError::UnsupportedLayout { reason } => DiagnosticKind::SdkResolutionUnsupported {
            name: sdk_name.to_string(),
            reason,
        },
    }
}

/// Does `value` satisfy an MSBuild `'$(Prop)' == 'true'` comparison?
///
/// `==` tries the boolean vocabulary before an ordinal-ignore-case string
/// compare, and every string spelling that survives to the fallback and
/// matches `true` is already in the vocabulary — so membership *is* the
/// comparison. Oracle-pinned over the vocabulary and its neighbours by
/// `msbuild_gate_boolean_diff`.
pub(crate) fn is_msbuild_true(value: &str) -> bool {
    condition::parse_msbuild_bool(value) == Some(true)
}

/// `TreatAsLocalProperty="Foo;Bar"` on `<Project>` is MSBuild's escape
/// hatch: names listed here can be locally reassigned even when
/// supplied as global properties. Without honouring it we'd silently
/// drop the project's writes and keep substituting the caller's value
/// — a real-world divergence (the F# SDK uses this attribute for
/// `RestoreAdditionalProjectSources`). Names are stored lowercased to
/// match MSBuild's OrdinalIgnoreCase property-name comparison.
fn collect_local_overrides(root: Node<'_, '_>) -> HashSet<String> {
    attribute(root, "TreatAsLocalProperty")
        .as_deref()
        .map(|s| {
            s.split(';')
                .map(str::trim)
                .filter(|n| !n.is_empty())
                .map(str::to_ascii_lowercase)
                .collect()
        })
        .unwrap_or_default()
}

/// Walk every element child of `root` as a top-level construct.
/// Shared by the project body and every imported file — the only
/// per-file state is `current_file_dir`, which becomes the base for
/// relative `<Import Project="...">` resolution.
///
/// The `Sdk` attribute on the project root is handled by the callers
/// ([`walk`] and [`walk_with_imports`]), not here — those know
/// whether IO and an SDK resolver are available. `walk_doc_body` is
/// also invoked on external files via [`walk_external_file`], and SDK
/// props/targets stubs aren't expected to carry an `Sdk` attribute of
/// their own.
fn walk_doc_body(root: Node<'_, '_>, current_file_dir: &Path, state: &mut State<'_>) {
    // The executor does not run `InitialTargets` yet; it declines a project
    // any of whose files names some.
    #[cfg(any(test, feature = "test-support"))]
    if attribute(root, "InitialTargets")
        .as_deref()
        .is_some_and(|targets| !targets.trim().is_empty())
    {
        state.initial_targets_named = true;
    }
    // A top-level `<Sdk Name="X"/>` element is the `Sdk` attribute's
    // sibling form: MSBuild imports X's `Sdk.props` before everything in
    // this file and `Sdk.targets` after it, wherever the element sits
    // (probed on dotnet msbuild 10.0.301: `$(UsingMicrosoftNETSdk)` reads
    // `true` even when the element follows the read). The element form is
    // not modelled, so degrade — as a pre-scan, before walking any child,
    // or a name the un-imported SDK chain defines would be read as
    // exactly-undefined by properties earlier in the document.
    for child in root.children().filter(Node::is_element) {
        if child.tag_name().name() == "Sdk" {
            let sdk = attribute(child, "Name").unwrap_or_default().to_string();
            state.push(
                DiagnosticKind::UnsupportedConstruct {
                    element: format!("Sdk (Name={sdk:?})"),
                },
                child.range(),
            );
            state.mark_structural_skip(
                StructuralCompileItemUncertainty::ProjectSdkUnsupported { sdk },
                child.range(),
            );
        }
    }
    for child in root.children().filter(Node::is_element) {
        walk_top_level(child, current_file_dir, state);
    }
}

/// Try to canonicalise `path` (through `observer`); on failure (file doesn't exist yet,
/// permission error, etc.) fall back to lexical `.`/`..` collapse.
/// We never compare these paths to anything other than other
/// canonicalised paths.
fn canonicalise_or_normalise(observer: &Observer, path: &Path) -> PathBuf {
    observed::canonicalize(observer, path).unwrap_or_else(|_| normalise(path))
}

/// First tier of the import-dedup identity, modelling MSBuild's
/// `Evaluator._importsSeen` key: the **lexically** normalised path —
/// `.`/`..` collapsed as strings, no symlink resolution (probed on dotnet
/// msbuild 10.0.301: a symlink alias of an already-imported file imports
/// *again*, `sub/../a.props` dedups against `a.props`) — **ASCII**
/// case-folded. MSBuild compares with `StringComparer.OrdinalIgnoreCase`
/// (Evaluator.cs; probed: `A.PROPS` dedups against `a.props`, string-level,
/// before any file IO), and ASCII-fold equality implies ordinal-ignore-case
/// equality on every .NET, so a hit on this key is a *certain* duplicate.
///
/// Non-ASCII case pairs are deliberately **not** folded here: .NET's
/// ordinal casing table is neither Unicode's simple nor full uppercase
/// (probed on dotnet 10: `ı`≠`I`, `ſ`≠`S`, `İ`≠`I`, `ß`≠`ẞ`, Kelvin
/// `K`≠`K` — yet `σ`==`ς`==`Σ`), so committing either verdict from a Rust
/// fold would be a wrong commit in one direction or the other. Pairs that
/// only a Unicode fold would equate land in the second tier
/// ([`import_dedup_fuzzy_key`]) and *decline* instead of guessing.
///
/// A trailing separator stays in the key, as it stays in MSBuild's full path:
/// `E.props/` names a directory, which MSBuild fails to import (MSB4019) even
/// after it imported `E.props`.
fn import_dedup_key(path: &Path) -> String {
    import_key_text(path).to_ascii_uppercase()
}

/// The text both duplicate keys fold: `path` collapsed, a trailing separator
/// kept.
fn import_key_text(path: &Path) -> String {
    let mut text = normalise(path).to_string_lossy().into_owned();
    let bytes = path.as_os_str().as_encoded_bytes();
    if bytes.last() == Some(&b'/') || (cfg!(windows) && bytes.last() == Some(&b'\\')) {
        text.push('/');
    }
    text
}

/// Second tier: the char-wise full Unicode uppercase of the same
/// normalised path. This fold **over-approximates** .NET's
/// ordinal-ignore-case equality: .NET-equal pairs are equal under
/// Unicode's simple uppercase (.NET's table is simple-uppercase minus
/// carve-outs like the Turkish-I family), simple-equal pairs of
/// non-expanding chars are full-fold-equal, and expanding chars (`ß`,
/// the ligatures) are .NET-equal only to themselves — which any fold
/// preserves. So: **not** fuzzy-equal ⟹ .NET treats the paths as
/// distinct imports (safe to walk both), while fuzzy-equal without a
/// first-tier hit means MSBuild's verdict is unknowable from here — the
/// caller declines rather than committing a skip *or* a second walk.
fn import_dedup_fuzzy_key(path: &Path) -> String {
    import_key_text(path)
        .chars()
        .flat_map(char::to_uppercase)
        .collect()
}

struct State<'r> {
    /// Full lookup map: well-known seeds, caller globals, and any
    /// project-defined properties added during the walk. Used for every
    /// `$(Name)` substitution. Keyed case-insensitively, matching
    /// MSBuild's OrdinalIgnoreCase property-name comparison.
    lookup: PropertyMap,
    /// Lowercased names whose project-side writes must be discarded —
    /// `properties::well_known` seeds (always) plus the caller's
    /// `extra_properties` (unless `TreatAsLocalProperty` opts them out).
    /// Writes targeting these names — under any casing — are silently
    /// ignored, matching MSBuild's "global properties override project
    /// properties" / "reserved properties are read-only" rules.
    protected: HashSet<String>,
    /// Lowercased names any walked root opted out of global protection with
    /// `TreatAsLocalProperty` — the union across the entry document and every
    /// file the walk imported, whether or not the name was actually a global
    /// (so it answers "could this document have overwritten a global of this
    /// name?" independently of what the caller happened to supply). Surfaced on
    /// [`ParsedProject::locally_overridable_properties`].
    locally_overridable: HashSet<String>,
    /// Lowercased names of MSBuild reserved well-known properties
    /// (everything seeded by [`properties::well_known`]). Snapshot
    /// taken at construction time. Used by [`walk_external_file`] to
    /// distinguish "protected because reserved" from "protected
    /// because supplied as a global property" when an imported
    /// `<Project TreatAsLocalProperty="...">` asks to unprotect a
    /// name: MSBuild's `TreatAsLocalProperty` only applies to
    /// globals, not reserved names, so we never unprotect anything
    /// in this set even if an import lists it.
    reserved: HashSet<String>,
    /// Lowercased names supplied as *read-only globals*
    /// (`extra_properties`, minus the entry project's
    /// `TreatAsLocalProperty` opt-outs). Immutable for the whole walk:
    /// unlike `protected`, it is never touched by `walk_external_file`'s
    /// per-file `TreatAsLocalProperty` handling, so it is a stable
    /// answer to "is this property a sticky global?". A global's value
    /// cannot be rewritten by MSBuild's `Microsoft.Common.props`
    /// default-fill assignments, so an *empty* sticky global stays
    /// empty rather than defaulting to "true" / the discovered path.
    /// Consulted only by the target executor ([`executor`]).
    #[cfg(any(test, feature = "test-support"))]
    sticky_globals: HashSet<String>,
    /// What the caller's environment said about `MSBuildExtensionsPath`, held
    /// aside rather than promoted: whether that value survives is the one
    /// toolset behaviour that differs across the SDKs we support, so it cannot
    /// be settled until an SDK resolves and names the toolset. See
    /// [`EnvExtensionsPath`] and [`State::seed_toolset_properties`].
    env_extensions_path: EnvExtensionsPath,
    /// Map from lowercased name to the *project's* canonical casing
    /// for every property successfully assigned by a `<PropertyGroup>`
    /// write. Used to filter and key [`ParsedProject::properties`] —
    /// the result records *only what the project wrote*, under the
    /// spelling that appeared in the XML. Extras that were
    /// treated-as-local but never reassigned by the project must not
    /// surface here (their value remains in `lookup` for substitution
    /// but never enters this map); and when a project does override an
    /// extras-supplied name with different casing, the project's
    /// casing wins for the exported map (the extras casing would
    /// surprise callers doing exact `properties.get("Configuration")`
    /// lookups against what they read in the XML).
    written: HashMap<String, String>,
    compile_first: Vec<OrderedResolvedItem>,
    explicit_compile_before: Vec<OrderedResolvedItem>,
    compile_before: Vec<OrderedResolvedItem>,
    compile_main: Vec<OrderedResolvedItem>,
    compile_after: Vec<OrderedResolvedItem>,
    explicit_compile_after: Vec<OrderedResolvedItem>,
    compile_last: Vec<OrderedResolvedItem>,
    /// Compile items whose current `CompileOrder` metadata is not one of the
    /// values the F# target buckets. Kept internally so a later literal
    /// `<Compile Update=... CompileOrder=...>` can still mutate the existing
    /// item back into a bucket that is emitted.
    compile_excluded: Vec<OrderedResolvedItem>,
    next_item_order: usize,
    /// `<ProjectReference>` items. Separate bucket from the Compile
    /// trio because ProjectReference is not a Compile input — it
    /// describes an inter-project dependency the downstream binder
    /// must resolve, and mixing it into [`ParsedProject::items`] would
    /// silently change every consumer's notion of "files to compile".
    project_references: Vec<OrderedResolvedItem>,
    /// `<PackageReference>` items as captured during the item pass, before
    /// Include + `Update` collapse — [`item_pass::finalize_package_references`]
    /// folds these into [`Self::package_references`] once every item is seen.
    captured_package_references: Vec<CapturedPackageReference>,
    /// `<PackageReference>` / `<FrameworkReference>` items — the NuGet
    /// dependency set. Separate buckets from Compile/ProjectReference: a
    /// package reference is neither a source input nor an inter-project
    /// edge, and it carries version/asset metadata the others don't. The
    /// effective (post-merge) `PackageReference` set; populated by the item
    /// pass's `finalize_package_references`.
    package_references: Vec<PackageReference>,
    /// The effective `PackageReference` items as an item table reads them:
    /// each with every metadatum, exactly ([`EvaluatedItem::exact_metadata`]),
    /// collapsed through `Update` as MSBuild collapses it. Only the probe reads
    /// these ([`reads`]); the dependency capture reads `package_references`.
    #[cfg(any(test, feature = "test-support"))]
    package_reference_rows: Vec<EvaluatedItem>,
    /// The `FrameworkReference` items as an item table reads them, as
    /// [`Self::package_reference_rows`] holds `PackageReference`s.
    #[cfg(any(test, feature = "test-support"))]
    framework_reference_rows: Vec<EvaluatedItem>,
    /// Metadata names an `Update` the dependency capture skipped (it writes no
    /// package metadatum) may have written on any `PackageReference`: unknown
    /// on every row.
    #[cfg(any(test, feature = "test-support"))]
    package_reference_unknown_names: HashSet<String>,
    /// The `PackageVersion` items as an item table reads them, as
    /// [`Self::package_reference_rows`] holds `PackageReference`s.
    #[cfg(any(test, feature = "test-support"))]
    package_version_rows: Vec<EvaluatedItem>,
    /// The `GlobalPackageReference` items as an item table reads them, as
    /// [`Self::package_reference_rows`] holds `PackageReference`s.
    #[cfg(any(test, feature = "test-support"))]
    global_package_reference_rows: Vec<EvaluatedItem>,
    /// Whether a `GlobalPackageReference` `Update` or `Remove` ran.
    #[cfg(any(test, feature = "test-support"))]
    global_package_references_mutated: bool,
    /// The dependency list each package-set cause is about, by its index in
    /// [`Self::package_reference_uncertainties`]: the type of the element
    /// being walked when it was recorded, or `PackageReference` for the
    /// collapse. A cause with no owner (an item group, an import, an item
    /// definition) may be about any list.
    #[cfg(any(test, feature = "test-support"))]
    package_cause_owners: HashMap<usize, item_pass::PackageItemKind>,
    /// Whether `MSBuildProjectDefaultTargets` is settled ([`latch_default_targets`]):
    /// set from a root's `DefaultTargets`, or left unset because a root's
    /// could not be decided.
    default_targets_decided: bool,
    package_versions: Vec<PackageVersion>,
    package_versions_untracked: bool,
    global_package_references: Vec<GlobalPackageReference>,
    framework_references: Vec<FrameworkReference>,
    /// Static item lists whose item type is not otherwise modelled by this
    /// evaluator. This intentionally starts narrow: package/framework reference
    /// capture can consume safe lists like `@(MIBCPackage)` without changing
    /// Compile item semantics or surfacing arbitrary item diagnostics.
    evaluated_items: HashMap<String, Vec<EvaluatedItem>>,
    /// Item types whose static declarations could not be fully evaluated.
    /// Consumers that reference one of these lists should keep whatever clean
    /// entries were captured, but mark their own result uncertain.
    tainted_item_lists: HashSet<String>,
    /// Item types whose live MSBuild item table can contain entries we did not
    /// copy into `evaluated_items`. A later exact `@(Type)` reference must not
    /// treat a missing captured list as confidently empty.
    untracked_item_lists: HashSet<String>,
    /// Package-metadata defaults declared by `<ItemDefinitionGroup>` for
    /// helper item types. These do not change helper identities, but they can
    /// supply metadata to helper items that a later `<PackageReference
    /// Include="@(Helper)">` inherits.
    helper_item_definition_defaults: HashMap<String, HashMap<String, HelperMetadataUncertainty>>,
    /// Each item type's item-definition defaults, by metadata name, as
    /// MSBuild's pass 2 leaves them: the value, or `None` where a definition
    /// that may apply has a condition or value the walk cannot decide. Applied
    /// to the exact rows of items declared directly ([`EvaluatedItem`]'s
    /// `definitions_applied`).
    #[cfg(any(test, feature = "test-support"))]
    item_definition_values: HashMap<String, HashMap<String, Option<String>>>,
    diagnostics: Vec<Diagnostic>,
    /// Whether `<Import>` elements should be followed by reading the
    /// referenced file (`true`, set by [`walk_with_imports`]) or just
    /// reported as [`DiagnosticKind::UnresolvedImport`] (`false`, set by
    /// the pure [`walk`]). The flag lives on `State` rather than being
    /// threaded everywhere because every `<Import>` site needs it and
    /// the alternative is a parallel parameter list.
    follow_imports: bool,
    /// Our model of MSBuild's `Evaluator._importsSeen`: the
    /// [`import_dedup_key`] of every import this walk has performed, the
    /// entry project included (seeded in [`walk_with_imports`]). MSBuild registers
    /// an import *before* evaluating the imported file's contents and
    /// skips any later import that resolves to a registered path —
    /// warning MSB4011, or MSB4210 when the target is the entry project —
    /// with the evaluation succeeding, so a duplicate here (a repeated
    /// list segment, a diamond, a cycle's back-edge) is a clean silent
    /// skip, not a degrade. Entries are never removed: the set is
    /// per-evaluation, exactly like MSBuild's. Termination for the
    /// pathological spelling-generating cases the string key cannot close
    /// (a directory symlink to `.` growing a fresh spelling per level)
    /// falls to [`MAX_IMPORT_DEPTH`], which degrades conservatively.
    imports_seen: HashSet<String>,
    /// Shadow of [`Self::imports_seen`] under the wider
    /// [`import_dedup_fuzzy_key`] fold. A hit here without a hit on the
    /// certain key means the import *might* be a duplicate under .NET's
    /// ordinal casing (whose non-ASCII table we cannot reproduce
    /// exactly), so the walk declines it — structural skip, not a
    /// silent skip and not a second walk.
    imports_seen_fuzzy: HashSet<String>,
    /// Every file the walk has *ever* entered (canonical), entry project
    /// included. Unlike [`Self::imports_seen`] — whose key is the
    /// *lexically* normalised spelling, because that is what MSBuild
    /// dedups on — this records symlink-resolved identity, so it can
    /// answer "was this file part of the evaluation?" after the walk
    /// completes (the `Directory.Packages.props` discharge check reads
    /// it).
    walked_files: HashSet<PathBuf>,
    /// The canonical file successfully walked through an
    /// `<Import Project="$(DirectoryPackagesPropsPath)">`-shaped import —
    /// NuGet's central-package import point (only `NuGet.props` uses that
    /// shape in practice, and a user file spelling it out behaves
    /// identically: the walked file is exactly what a real build's
    /// `NuGet.props` would import for the same property value).
    /// Provenance, not final property state, so it cannot be spoofed by
    /// writing marker/path properties — the discharge check compares it
    /// against the *final* `DirectoryPackagesPropsPath` value to also
    /// catch a post-import reassignment.
    walked_directory_packages_props_import: Option<PathBuf>,
    /// Current import nesting depth. `0` while we're walking the
    /// entry project's body; `+1` for each [`walk_external_file`]
    /// frame on the stack. Compared against [`MAX_IMPORT_DEPTH`] as a
    /// stack-overflow safeguard against hostile input.
    depth: usize,
    /// Directory of the entry project file. Pinned for the whole walk:
    /// MSBuild resolves an unqualified `<Compile Include="Generated.fs"
    /// />` *appearing in an imported file* relative to the entry
    /// project's directory, not the importing file's directory. (The
    /// `$(MSBuildThisFileDirectory)` prefix is how an import opts in
    /// to its own folder.) Distinct from the per-call
    /// `current_file_dir`, which is what relative `<Import Project="
    /// ...">` paths resolve against.
    entry_project_dir: PathBuf,
    /// The caller's environment names a parse configuration
    /// (`MSBUILD_PARSE_CONFIG`), which a newer MSBuild reads to relax its
    /// loader (`rejection::parse_configuration_may_apply`).
    parse_configuration_named: bool,
    /// `Some(range)` while walking an imported file; `None` while
    /// walking the entry project's body. The range is the span of the
    /// top-level `<Import>` element *in the entry project* that
    /// ultimately led to the current file. Diagnostics and items
    /// produced inside an imported buffer would otherwise carry
    /// `node.range()` byte offsets *into that buffer*, which are
    /// meaningless to callers who only ever see the entry project's
    /// source. We collapse all imported-file spans to this single
    /// project-source location so the byte-offset contract holds:
    /// every span in the output is a valid offset into the source
    /// the caller handed in. The first descent into an external file
    /// sets it; nested descents preserve it (so spans always point at
    /// the *top-level* import site, not the most-recent one); unwind
    /// restores the prior value.
    import_site_span: Option<Range<usize>>,
    /// Caller-supplied SDK resolver, if any. Consulted by
    /// [`resolve_project_sdk`] for the project root's `Sdk` attribute
    /// and by [`follow_explicit_import`] for `<Import Sdk="..."/>`.
    /// `None` means the caller declined to do SDK resolution; any
    /// `Sdk` attribute then becomes a [`DiagnosticKind::SdkResolverAbsent`].
    sdk_resolver: Option<&'r SdkResolver<'r>>,
    /// Caller-supplied glob resolver, if any. Consulted by the item
    /// walk for a `<Compile>` / `<ProjectReference>` whose `Include`
    /// contains an MSBuild wildcard, or that carries an `Exclude`.
    /// `None` means the caller declined glob expansion; a wildcard then
    /// becomes [`DiagnosticKind::UnsupportedGlob`] and an `Exclude`
    /// [`DiagnosticKind::UnsupportedItemOperation`]. See
    /// [`crate::GlobResolver`].
    glob_resolver: Option<&'r GlobResolver<'r>>,
    /// Where every file-system query of the walk is made and recorded
    /// ([`crate::observed`]), the resolvers' included.
    observer: &'r Observer,
    /// Byte ranges of *entry-project* body `<Import Sdk="X"
    /// Project="Sdk.{props,targets}"/>` nodes that the pre-scan in
    /// [`find_explicit_sdk_promotion`] has hoisted to the root SDK
    /// splice positions. When the entry project's body walk later
    /// reaches one of these nodes, [`follow_explicit_import`] must
    /// skip it — for `Sdk.props` the walk would be a harmless
    /// duplicate skip (the top splice already registered the file),
    /// but `Sdk.targets` splices at the *bottom*, so walking it at
    /// body position would register it first and make the splice the
    /// skipped duplicate. Empty unless we're in the explicit-only
    /// promotion case.
    ///
    /// The ranges are byte offsets into the *entry project's* XML.
    /// [`follow_explicit_import`] gates the skip on
    /// `import_site_span.is_none()` (i.e. "we're inside the entry
    /// project body, not an imported file") so an `<Import>` at the
    /// same byte offset inside `Directory.Build.props` or `Sdk.props`
    /// is never accidentally matched.
    hoisted_sdk_imports: HashSet<Range<usize>>,
    /// The two `Directory.Build.*` import points: what the walk discovered,
    /// reached and could not decide ([`directory_build`]).
    directory_build: directory_build::Bookkeeping,
    /// The staleness of the conditions that let the property writes being
    /// walked run: an enclosing `<PropertyGroup>`'s, and the `<When>`s of an
    /// enclosing `<Choose>` that chose the branch. A write a stale value let
    /// run may be one MSBuild never makes, so its value is stale too, as for
    /// its own condition.
    enclosing_condition_stale: Option<properties::trust::StaleCause>,
    /// The [`SdkPaths::root`] of the entry project's own (root / promoted)
    /// SDK, recorded by [`Self::record_sdk_root`]; `None` for an SDK-less
    /// entry. Surfaced on [`ParsedProject::resolved_sdk_root`] by
    /// [`Self::into_project`].
    resolved_sdk_root: Option<PathBuf>,
    /// The canonical `…/sdk/<version>` directory of the entry project's own SDK,
    /// when it resolved into the canonical .NET layout. A document outside it
    /// has its definitions recorded in [`Self::foreign_definitions`].
    entry_sdk_version_dir: Option<PathBuf>,
    /// Surfaced on [`ParsedProject::foreign_definitions`].
    foreign_definitions: crate::ForeignDefinitions,
    /// Surfaced on [`ParsedProject::workload_definitions`].
    workload_definitions: crate::ForeignDefinitions,
    /// Surfaced on [`ParsedProject::sdk_files_imported_from_outside`].
    sdk_files_imported_from_outside: BTreeSet<PathBuf>,
    /// `true` while the walk is inside a context whose uncertainty would
    /// affect the **Compile item set**: a source-set-changing
    /// `<Compile>`/`<CompileBefore>`/`<CompileAfter>` element, or an
    /// `<ItemGroup>` that has such a child (metadata-only `Update` is ignored
    /// unless it writes `CompileOrder`). Any diagnostic
    /// [`Self::push`]ed while this is set flips [`Self::items_uncertain`], and
    /// a Compile-gating condition recorded here becomes a
    /// [`CompileConditionUncertainty`]. Scoped save/restore by the callers, so
    /// it tracks the *position* in the walk rather than a kind.
    compile_context: bool,
    /// The package-set analogue of [`Self::compile_context`]: `true` while
    /// positioned at a `<PackageReference>`/`<FrameworkReference>` element,
    /// or an `<ItemGroup>` that has such a child. A condition here that is
    /// unsupported or undefined-property-laden flips
    /// [`Self::package_references_uncertain`] — we can't trust whether the
    /// gated package is in the set. Scoped save/restore by the callers.
    package_context: bool,
    /// `true` while walking a file that physically lives inside the entry
    /// SDK's installation tree (see [`Self::sdk_tolerance_roots`]). The .NET
    /// SDK's own targets/props are full of conditional Compile machinery
    /// (`<ItemGroup Condition="'$(EnableDefaultItems)' == 'true'">…`, the
    /// link-metadata `<Compile Update=…>` group) gated on properties we can't
    /// resolve; treating those as Compile-affecting would flag essentially
    /// every real project. So Compile-affecting uncertainty inside the SDK tree
    /// is *tolerated* (it never decides which hand-written files compile),
    /// while the same uncertainty in the entry project or a user-authored
    /// import (`Directory.Build.*`, an explicit `<Import>`) is respected. Path-
    /// based, so it's independent of *how* a file was reached — a user file
    /// pulled in through the SDK's import chain is still judged by its path.
    in_sdk_subtree: bool,
    /// Whether the walk is in a document outside the entry .NET SDK's version
    /// directory and its workload manifests: the entry project, or one it
    /// imports from outside the install. Writes made here are checked into
    /// [`Self::foreign_write_failures`].
    in_foreign_document: bool,
    /// Surfaced on [`ParsedProject::foreign_write_failures`].
    foreign_write_failures: std::collections::BTreeMap<String, Option<String>>,
    /// Surfaced on [`ParsedProject::workload_manifests_outside_install`].
    workload_manifests_outside_install: BTreeSet<PathBuf>,
    /// Surfaced on [`ParsedProject::imported_sdk_files`].
    imported_sdk_files: BTreeSet<PathBuf>,
    /// Surfaced on [`ParsedProject::workload_manifest_files`].
    workload_manifest_files: BTreeSet<String>,
    /// Directories under which a file counts as SDK-installed — one per resolved
    /// SDK *root's parent* (e.g. `…/Sdks/Microsoft.NET.Sdk`, which holds both
    /// `Sdk/Sdk.props` and `targets/…DefaultItems…`), canonicalised. A *set*
    /// because an SDK variant pulls in others: `Microsoft.NET.Sdk.Web`'s
    /// `Sdk.props` does `<Import Sdk="Microsoft.NET.Sdk">`, whose files live
    /// under a *sibling* dir — both must be tolerated. Populated by
    /// [`Self::note_sdk_tolerance`] at every successful SDK resolution (entry,
    /// nested, and `<Import Sdk=…>`); empty for an SDK-less entry (then
    /// [`Self::in_sdk_subtree`] is always `false`).
    sdk_tolerance_roots: Vec<PathBuf>,
    /// Accumulates into [`ParsedProject::items_uncertain`].
    items_uncertain: bool,
    /// Whether the captured `<ProjectReference>` list may diverge from
    /// MSBuild (an unmodelled `Update`/`Remove` mutation). Accumulates into
    /// [`ParsedProject::project_references_uncertain`].
    project_references_uncertain: bool,
    /// Whether a `<ProjectReference>` `Include` that may run in the real build
    /// went uncaptured — skipped on an untrusted gate, or one we could not
    /// evaluate. Every captured item is still one MSBuild has (that is
    /// [`Self::project_references_uncertain`]'s to doubt), but the list may lack
    /// one, so it is published as incomplete
    /// ([`ParsedProject::project_references_incomplete`]): a missing edge is no
    /// proof the build lacks it. An `Include` whose value read a name the walk
    /// doubts raises `project_references_uncertain` as well, dropped or kept
    /// (`item_pass::reads_a_doubted_name`). A list *derived* from
    /// `@(ProjectReference)` is then incomplete too, and a `Remove` driven by
    /// it can miss an item MSBuild removes. [`item_pass`]'s item-list view
    /// reads it.
    project_reference_includes_hidden: bool,
    /// Whether the captured package/framework-reference set may diverge from
    /// MSBuild. Accumulates into [`ParsedProject::package_references_uncertain`].
    package_references_uncertain: bool,
    /// Accumulates into [`ParsedProject::package_reference_uncertainties`].
    package_reference_uncertainties: Vec<PackageReferenceUncertaintyCause>,
    /// The preprocessor-symbol analogue of [`Self::compile_context`]: `true`
    /// while resolving a user-authored `<DefineConstants>` write or the
    /// `<PropertyGroup>` condition gating one. A diagnostic [`Self::push`]ed
    /// here means the evaluated `$(DefineConstants)` may diverge from MSBuild,
    /// so files would parse under the wrong `#if` branches. SDK-internal define
    /// manipulation the walk entered is tolerated (gated `!in_sdk_subtree` at
    /// the set sites, like `compile_context`) — we already don't model the
    /// framework defines the SDK adds in targets. Content it did not enter is
    /// not: [`Self::latch_walk_opaque`] withdraws the set for it.
    define_context: bool,
    /// `true` only while expanding a `<DefineConstants>` *value* (not its
    /// condition). The `$(DefineConstants)` self-reference exemption
    /// ([`is_define_self_reference`]) applies only here, and only to the value's
    /// own read ([`Self::push_undefined_read`]) — the append idiom is a value
    /// construct; a *condition* referencing `$(DefineConstants)` is a genuine
    /// branch decision that must still flag.
    in_define_value: bool,
    /// Accumulates into [`ParsedProject::define_constants_uncertain`].
    define_constants_uncertain: bool,
    /// Accumulates into [`ParsedProject::define_constants_uncertainties`], at
    /// the same site that raises [`Self::define_constants_uncertain`] — the two
    /// are one fact recorded twice, never independently.
    define_constants_uncertainties: Vec<DefineConstantsUncertaintyCause>,
    /// `true` while evaluating an `<Import>` / `<ImportGroup>` `Condition`, in
    /// any file. An import skipped by a condition we couldn't trust
    /// (unsupported, or relying on an undefined property) might have
    /// contributed `<Compile>` items or gating properties, and one followed
    /// may be one the real build skips, so any diagnostic [`Self::push`]ed here
    /// flips [`Self::items_uncertain`] and [`Self::project_references_uncertain`].
    /// An SDK file's import is no exception: the file it names may be a
    /// user's, or import one (#821, #848).
    import_gate_context: bool,
    /// Package-reference analogue of [`Self::import_gate_context`]: SDK imports
    /// are a normal source of implicit package/framework references, so an
    /// import skipped by an untrusted condition can hide dependency items.
    package_import_gate_context: bool,
    /// Accumulates into [`ParsedProject::compile_condition_uncertainties`].
    compile_condition_uncertainties: Vec<CompileConditionUncertainty>,
    /// Accumulates into [`ParsedProject::compile_item_uncertainties`].
    compile_item_uncertainties: Vec<CompileItemUncertaintyCause>,
    /// The file the property pass is currently positioned in — the target
    /// of [`Self::defer_item_group`]'s retention. Saved/replaced/restored
    /// by [`walk_external_file`] alongside the `MSBuildThisFile` frame.
    current_file: CurrentFile,
    /// `<ItemGroup>`s recorded by the property pass, in encounter order,
    /// awaiting the item pass ([`replay_deferred_item_groups`]). Empty
    /// again by [`Self::into_project`].
    deferred_item_groups: Vec<DeferredItemGroup>,
    /// Sources of imported files that own at least one deferred group,
    /// kept so the item pass can re-parse them. Indexed by
    /// [`CurrentFile::Imported::retained`].
    retained_imported_files: Vec<RetainedImportedFile>,
    /// The entry project's path, as the caller spelt it: the file a
    /// [`Self::target_definitions`] entry of the entry project names.
    #[cfg(any(test, feature = "test-support"))]
    entry_project_path: PathBuf,
    /// Every `<Target>` element the walk reached, with its `Name` attribute,
    /// in the order it reached them. Only the probe reads these
    /// ([`reads`]); the walk itself runs no target.
    #[cfg(any(test, feature = "test-support"))]
    target_definitions: Vec<(String, reads::TargetDefinition)>,
    /// Whether a file the walk reached names `InitialTargets`, which MSBuild
    /// runs before any target a build asks for.
    #[cfg(any(test, feature = "test-support"))]
    initial_targets_named: bool,
    /// The name each `<UsingTask>` the walk reached binds a task under, but
    /// MSBuild's own registrations of its built-ins
    /// ([`Self::record_using_task`]): the executor runs a built-in task only
    /// where none may rebind it.
    #[cfg(any(test, feature = "test-support"))]
    using_task_names: Vec<String>,
    /// Lowercased referenceable names present in the caller's environment
    /// snapshot — *including* names promotion skipped (case collisions,
    /// toolset overwrites): the real build has *some* value for every one
    /// of them, so an undefined read of such a name is never exact
    /// (see [`State::undefined_read_is_exact`]).
    env_property_names: HashSet<String>,
    /// Whether the walk has passed a construct that could hide arbitrary
    /// property writes: an unfollowed/unresolved/failed import or SDK, or
    /// an import whose gate we could not decide. Once set it never
    /// clears — every later undefined read could be of a name the hidden
    /// content defined, so none is exact. Reads *before* the opaque
    /// construct are unaffected (property evaluation is a single forward
    /// pass on both sides), which the "so far" reading gives for free;
    /// the item pass runs after the whole property pass, so it correctly
    /// sees the final flag.
    ///
    /// `Some` carries what made it so (the first such construct), which is
    /// how a user learns why a name that reads as unset might not be.
    walk_opaque: Option<OpacityCause>,
    /// The first construct that may make MSBuild reject the whole project
    /// ([`rejection`]); [`Self::into_project`] withdraws what the walk publishes
    /// when it is set.
    rejection: Option<crate::Rejection>,
    /// Every site the rejection judgement noted, in order: what a second
    /// walk's sites are compared to, and adopted from
    /// ([`State::adopt_second_walk`]).
    noted_sites: Vec<rejection::NotedSite>,
    /// Whether this is the second walk, whose rejection judgement holds a
    /// bound name whose only doubt is a refusal's mark certain
    /// ([`rejection::judged_certain`]).
    second_walk: bool,
    /// The names (lower-cased) a clean write stored a value to after their
    /// last refused one, of a value reading no name whose refusal no such
    /// write discharged: whose bound value is the project's own, though the
    /// mark stays for the import points. A toolset seed filling the slot a
    /// refusal emptied is none, nor a copy of one
    /// ([`directory_build::is_certain_setting_aside_refusal`]). A value
    /// resting on a seed through another assignment, or written under a gate
    /// that read one, is held all the same, and a throw on it is a decline
    /// (#1183).
    rewritten_after_refusal: HashSet<String>,
    /// Whether the first walk's judgement read a name the second walk's
    /// would hold certain where the first doubts it ([`rejection::judged_certain`]):
    /// the trigger for the second walk, which can differ nowhere else.
    second_walk_needed: std::cell::Cell<bool>,
    /// The file the walk is in, as a site's construct names it: the entry
    /// project, whose text is the caller's buffer (`None`), or an imported
    /// document, by the path it opened, as [`State::walked_files`] names it:
    /// two fallback walks may open two documents one duplicate key covers.
    /// The two walks take one course, so they open each file at one path.
    site_file: Option<std::rc::Rc<Path>>,
    /// How many constructs the walk is inside whose gate it did not decide
    /// from certain inputs and took: a `<PropertyGroup>`, a `<Choose>` past a
    /// `<When>` so decided, or an import whose path it did not compute from
    /// certain values. Import gates count in
    /// [`directory_build::Bookkeeping`] instead. A construct reached inside
    /// one is not reached for certain ([`rejection::reach_is_certain`]).
    reach_doubted: usize,
    /// Whether the `<Import>` the walk is following names its path from
    /// certain values, so that its failure to load is MSBuild's
    /// ([`rejection`]). Set for each explicit import, and `false` for any other.
    taken_import_path_certain: bool,
    /// The kind of group the item pass replays, while it runs: its
    /// conditions are judged group by group ([`rejection::judge_deferred`]),
    /// not where the walk evaluates them, and each kind's conditions are
    /// evaluated at its own [`condition::Site`].
    item_pass: Option<DeferredGroupKind>,
    /// While the rejection judgement walks content the walk does not take
    /// ([`rejection::judge_branch`], [`rejection::judge_properties`]), or
    /// judges an item group from it ([`State::defer_judgement`]): the names
    /// written on that path before what it judges, whose value there the walk
    /// does not hold. `None` outside one.
    speculation: Option<Speculation>,
    /// The `<When>` decisions of each `<Choose>` the judgement is judging the
    /// arms of now, by the `<Choose>` (its document and offset), taken once on
    /// the state before it ([`rejection::judge_branch`]).
    arm_decisions: HashMap<(usize, usize), rejection::ArmFates>,
    /// The root each root-surfacing diagnostic stood for, by its index in
    /// `diagnostics`, captured when it was pushed. A diagnostic carries only a
    /// name, and that name's root may change later in the walk;
    /// [`Self::unpinned_root_from_recent_diagnostics`] reads these instead.
    diagnostic_roots: HashMap<usize, UnpinnedRoot>,
}

#[derive(Debug, Clone)]
struct EvaluatedItem {
    identity: String,
    /// The identity as MSBuild holds it, still escaped (`EvaluatedIncludeEscaped`):
    /// `a%2Ex` where `identity` reads `a.x`. Every expansion of the list and
    /// every metadata derivation (`%(Extension)`) starts from it, and decoding
    /// loses it. `None` where the walk does not know it.
    #[cfg(any(test, feature = "test-support"))]
    escaped_identity: Option<String>,
    /// NuGet's package metadata names only, each value trimmed as the
    /// dependency capture reads it; `None` where that reading is not MSBuild's
    /// value (padded, a value MSBuild's Unix path fixup may rewrite, an
    /// attribute it parses as XML), which a capture copying the item must treat
    /// as uncertain.
    metadata: HashMap<String, Option<String>>,
    /// Every metadatum, exactly as MSBuild evaluates it (untrimmed), for a
    /// reader of the item table itself ([`reads`]). `None` where that value
    /// cannot be known: a body holding more than text and comments, or a value
    /// MSBuild's Unix path fixup may rewrite, depending on its working
    /// directory. The dependency capture keeps its own reading of those.
    ///
    /// The read census is that reader today, and only the differential tests
    /// run it, so this and `metadata_complete` exist only in their build.
    #[cfg(any(test, feature = "test-support"))]
    exact_metadata: HashMap<String, Option<String>>,
    /// Whether `exact_metadata` names every metadatum the item carries. False
    /// for an item copied from a type whose metadata this crate models
    /// elsewhere (`@(ProjectReference)`), where a name it lacks is unknown
    /// rather than absent.
    #[cfg(any(test, feature = "test-support"))]
    metadata_complete: bool,
    /// Whether `exact_metadata` already holds the item type's definition
    /// defaults: true for an item declared directly, false for a copy
    /// (`@(Other)`), whose definitions stay uncertain.
    #[cfg(any(test, feature = "test-support"))]
    definitions_applied: bool,
    metadata_uncertainties: Vec<HelperMetadataUncertainty>,
}

impl EvaluatedItem {
    fn metadata(&self, name: &str) -> Option<String> {
        self.metadata
            .get(&name.to_ascii_lowercase())
            .cloned()
            .flatten()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum HelperMetadataUncertaintyKind {
    UnevaluableValue,
    ItemDefinitionDefault,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct HelperMetadataUncertainty {
    name: String,
    value: String,
    kind: HelperMetadataUncertaintyKind,
}

impl HelperMetadataUncertainty {
    fn new(name: &str, value: &str) -> Self {
        Self {
            name: name.to_string(),
            value: value.to_string(),
            kind: HelperMetadataUncertaintyKind::UnevaluableValue,
        }
    }

    fn item_definition_default(name: &str) -> Self {
        Self {
            name: name.to_string(),
            value: String::new(),
            kind: HelperMetadataUncertaintyKind::ItemDefinitionDefault,
        }
    }
}

/// Result of expanding `$(...)` in a raw attribute or element value. The
/// two issue flags are tracked separately because they have different
/// downstream consequences:
///   * `had_undefined` means a reference substituted to "" — the value is
///     still well-formed, just missing data. Safe to store as a property.
///   * `had_unsupported` means an expression like `$([X]::Y())` was left
///     literal in the output. Storing such a value would let later
///     `$(Name)` references silently expand to that residual, corrupting
///     downstream paths. Property writes refuse to record it.
struct Expansion {
    /// The expanded text, still in MSBuild's escaped domain — it is stored as a
    /// property without leaving it, exactly as MSBuild stores it, and each
    /// consumer unescapes at its own point of use — with the trust of every
    /// entry the expansion read. A consumer takes the trust or says it is
    /// leaving it behind ([`Provenanced`]).
    value: Provenanced<Escaped>,
    had_undefined: bool,
    had_unsupported: bool,
    /// Why the produced value cannot be trusted as final, if it can't: a
    /// direct undefined `$(Name)` substitution, or a reference to a
    /// property that is itself unpinned. Recorded when the value is stored
    /// as a property ([`Trust::unpinned`]).
    unpinned_root: Option<UnpinnedRoot>,
    /// Every `$(…)` MSBuild throws on, on the values the expansion read
    /// ([`rejection::throws_in`]); `had_unsupported` is set with any. A
    /// rejection wherever MSBuild evaluates the text: the caller judges where.
    throws: Vec<rejection::Thrown>,
}

/// The rejection judgement's walk of content the walk does not take
/// ([`State::speculation`]).
struct Speculation {
    /// Lower-cased names written on the path, whose value there is unknown.
    unheld: HashSet<String>,
    /// The names [`Self::unheld`] gained, in order, so that a branch can undo
    /// its own on leaving ([`rejection::judge_branch`]).
    gained: Vec<String>,
    /// Every write anywhere in the outermost walk, which the item groups
    /// deferred from it share ([`State::defer_judgement`]): MSBuild evaluates
    /// an item group after every property write on its path, those after the
    /// group included.
    walk_written: std::rc::Rc<std::cell::RefCell<PathWrites>>,
    /// The `<Choose>` arms the walk is in now, outermost first.
    arms: Vec<Arm>,
    /// While an item group deferred from a walk is judged, where it stands
    /// in that walk: a name written on its path there whose final value is
    /// not certain is unknown to it ([`State::judge_from_path`]).
    inherited: Option<PathOf>,
    /// How many nested walks are open.
    depth: usize,
    /// How many of [`Self::arms`] MSBuild cannot take, by gates the walk
    /// decides exactly on the state before their `<Choose>`
    /// ([`rejection::judge_branch`]): an item group deferred from within one
    /// holds no reference the build makes.
    dead_arms: usize,
}

/// An arm of a `<Choose>` the judgement walks: the `<Choose>` (its document
/// and offset) and the `<When>` or `<Otherwise>` (its offset). Two arms of
/// one `<Choose>` are never both taken.
type Arm = ((usize, usize), usize);

/// The writes in one walk of content the walk does not take
/// ([`Speculation::walk_written`]).
#[derive(Default)]
struct PathWrites {
    /// Each name written, lower-cased, and the arms of each of its writes.
    writes: HashMap<String, Vec<std::rc::Rc<[Arm]>>>,
    /// The names written whose final value is not certain, computed once, in
    /// the item pass, when the table is final.
    settled: Option<std::rc::Rc<HashSet<String>>>,
    /// Of [`Self::settled`], those whose only doubt is a refusal's mark,
    /// computed with it: `WalkCosts::refusal_paths`'s census.
    #[cfg(any(test, feature = "test-support"))]
    refusal_only: Vec<String>,
}

/// Where an item group deferred from a walk of content the walk does not
/// take stands in that walk: the walk's writes, and the arms the group is in.
#[derive(Clone)]
struct PathOf {
    writes: std::rc::Rc<std::cell::RefCell<PathWrites>>,
    arms: std::rc::Rc<[Arm]>,
}

impl PathOf {
    /// Whether `name` (lower-cased) is written on the path of the group: in
    /// no arm another arm of whose `<Choose>` holds the group. Asked of the
    /// names a judgement reads, so its cost is theirs, not the walk's.
    fn reaches(&self, name: &str) -> bool {
        self.reaches_counting(name, true)
    }

    /// [`Self::reaches`], counting nothing: for a census, whose work is not
    /// the walk's.
    #[cfg(any(test, feature = "test-support"))]
    fn reaches_uncounted(&self, name: &str) -> bool {
        self.reaches_counting(name, false)
    }

    /// [`Self::reaches`], counting the writes it examines where `counted`.
    #[cfg_attr(not(any(test, feature = "test-support")), allow(unused_variables))]
    fn reaches_counting(&self, name: &str, counted: bool) -> bool {
        self.writes.borrow().writes.get(name).is_some_and(|writes| {
            writes.iter().any(|arms| {
                if counted {
                    crate::cost::count(|costs| costs.path_writes_examined += 1);
                }
                arms.iter().all(|(choose, arm)| {
                    self.arms
                        .iter()
                        .all(|(other, other_arm)| other != choose || other_arm == arm)
                })
            })
        })
    }

    /// Whether `name` (lower-cased) reaches the group with a final value that
    /// is not certain ([`PathWrites::settled`], which must be computed).
    fn unknown(&self, name: &str) -> bool {
        self.writes
            .borrow()
            .settled
            .as_ref()
            .is_some_and(|settled| settled.contains(name))
            && self.reaches(name)
    }
}

impl Expansion {
    fn had_issue(&self) -> bool {
        self.had_undefined || self.had_unsupported
    }
}

impl<'r> State<'r> {
    /// MSBuild's own write of `MSBuildAllProjects` between its property and
    /// item passes (`Evaluator.SetAllProjectsProperty`, MSBuild 18.9): it
    /// prepends the most recently written of the project and its imports, by
    /// file times the walk does not read. So the walk holds no value of the
    /// name from here on, and drops the documents' one. What a read of an
    /// unbound name then sees is the judgement every undefined read gets
    /// ([`Self::undefined_read_is_exact`]): an `msbuild` name is one MSBuild
    /// may define where no document does
    /// ([`is_toolset_initial_property_name`]), so the read is not exact, and
    /// each consumer (an item's gate, spec or metadata, a reference's, the
    /// final table's) declines it, deciding without it where another operand
    /// settles the decision.
    fn write_all_projects(&mut self) {
        const NAME: &str = "MSBuildAllProjects";
        debug_assert!(is_toolset_initial_property_name(&NAME.to_ascii_lowercase()));
        self.lookup.unbind(NAME);
    }

    #[allow(clippy::too_many_arguments)]
    fn new(
        project_path: &Path,
        extra_properties: &HashMap<String, String>,
        environment: &HashMap<String, String>,
        local_overrides: &HashSet<String>,
        follow_imports: bool,
        sdk_resolver: Option<&'r SdkResolver<'r>>,
        glob_resolver: Option<&'r GlobResolver<'r>>,
        startup_directory: Option<&Path>,
        observer: &'r Observer,
    ) -> Self {
        let mut lookup = properties::well_known(project_path);
        // Seeded before `reserved` is taken from the table, so it is reserved
        // and protected like the path-derived names.
        if let Some(seed) = startup_directory.and_then(|dir| startup_directory_seed(observer, dir))
        {
            lookup.insert_escaped("MSBuildStartupDirectory", seed);
        }
        // Reserved well-known names are unconditionally protected;
        // `TreatAsLocalProperty` is documented to apply to *global*
        // properties only, so listing a reserved name there must not
        // unprotect it.
        let mut reserved: HashSet<String> = lookup
            .canonical_keys()
            .map(|k| k.to_ascii_lowercase())
            .collect();
        // Reserved from process start: MSBuild derives the ChangeWaves
        // threshold from the `MSBUILDDISABLEFEATURESFROMVERSION`
        // environment variable and rejects every project write to the
        // property name, so a write must never reach
        // `AreFeaturesEnabled`'s guard. Its *value* is seeded from the
        // caller's environment snapshot below — the one trusted source.
        reserved.insert("msbuilddisablefeaturesfromversion".to_string());
        let mut protected: HashSet<String> = reserved.clone();
        // The `OS` pseudo-environment property. MSBuild *synthesises* it only
        // on non-Windows hosts (dotnet/msbuild
        // `src/Build/Evaluation/Evaluator.cs`: `// Fake OS env variables when
        // not on Windows` / `if (!NativeMethodsShared.IsWindows)` →
        // `SetBuiltInProperty(osName, "Unix")`). On Windows there is no such
        // built-in at all: `OS=Windows_NT` reaches MSBuild as an ordinary
        // environment variable, so it must come from the *snapshot* — seeding
        // it unconditionally would invent `Windows_NT` for an env-cleared
        // Windows caller, where the real `$(OS)` is empty.
        //
        // Unlike the reserved well-known names above it is freely overridable:
        // a project `<OS>` write wins over the default, and a caller global
        // (the loop below runs later, so it overwrites) wins over both (pinned
        // against `dotnet msbuild` 10.0.301; see the "`OS` pseudo-environment
        // property" tests). Corpus projects gate TargetFrameworks on
        // `'$(OS)' == 'Unix'`, so leaving it unset mis-evaluates them on every
        // unix host.
        //
        // Seeded *before* the environment promotion below, mirroring MSBuild's
        // `AddBuiltInProperties()` → `AddEnvironmentProperties()` order: `OS`
        // is not reserved, so a genuine `OS` variable in the snapshot
        // overwrites this default rather than being skipped.
        if !cfg!(windows) {
            lookup.insert("OS".to_string(), "Unix".to_string());
        }
        // Environment promotion (pinned against dotnet msbuild
        // 10.0.300): env-backed properties are readable from the start,
        // lose to same-named globals (inserted after, overwriting), and
        // are overridable by project writes (NOT protected). Skipped:
        // every name MSBuild treats as reserved (see
        // `is_msbuild_reserved_name` — MSBuild filters the environment
        // against the *whole* reserved set in
        // `Utilities.GetEnvironmentProperties`, not just the subset we
        // seed, so a spoofed `MSBuildThisFileFullPath` must stay
        // unreadable), toolset-computed names MSBuild overwrites after
        // promotion (see `is_env_ignored_toolset_name`), names our
        // `$(…)` grammar cannot reference (nothing could read them),
        // and any name with a case-insensitive collision in the
        // snapshot — probed: with `ZZZTEST`/`zzztest`/`ZZZTest` all
        // set, the property's winner *changed* when the environ order
        // was reversed, so MSBuild's pick is unspecified and seeding
        // any of them could commit us to a value the real build
        // doesn't have. An unseeded name reads as undefined, which is
        // always conservative (diagnostic + unpinned value).
        //
        // The pick being unspecified is not the same as the *value* being
        // unknowable, though, and the distinction is worth keeping: when every
        // colliding spelling carries the same text, that text is the value
        // whichever one wins. So the collision is judged on the set of distinct
        // values, not the number of spellings — a name is dropped only when the
        // spellings actually disagree.
        let mut env_values_by_lower: HashMap<String, HashSet<String>> = HashMap::new();
        for (key, value) in environment {
            env_values_by_lower
                .entry(key.to_ascii_lowercase())
                .or_default()
                .insert(value.clone());
        }
        let spellings_disagree =
            |lower: &str| env_values_by_lower.get(lower).is_none_or(|v| v.len() > 1);
        let mut env_extensions_path = EnvExtensionsPath::Absent;
        let mut env_property_names: HashSet<String> = HashSet::new();
        for (key, value) in environment {
            if !properties::is_referenceable_name(key) {
                continue;
            }
            let lower = key.to_ascii_lowercase();
            // Every referenceable variable is remembered — promoted or
            // not — because the real build defines *some* property for
            // it, which the exact-undefined-read guard must respect.
            env_property_names.insert(lower.clone());

            // --- Names MSBuild does *not* fold in. Any default we seeded for
            // them is the real build's value too, so it stands. ---

            // Reserved names are filtered out of the environment by MSBuild
            // itself, so the path-derived value we seeded survives.
            if reserved.contains(&lower) || is_msbuild_reserved_name(&lower) {
                continue;
            }

            // MSBuild promotes this one, but whether the promoted value
            // *survives* is decided by the toolset, and no SDK has named the
            // toolset yet. Park it — including the case-collision verdict,
            // which a toolset that overwrites the value makes moot — and let
            // `seed_toolset_properties` adjudicate once it knows the version.
            // Until then the name stays undefined, so a read before any SDK
            // resolves declines rather than committing a version-specific
            // answer.
            if lower == "msbuildextensionspath" {
                env_extensions_path = if spellings_disagree(&lower) {
                    EnvExtensionsPath::Unspecified
                } else {
                    EnvExtensionsPath::Value(value.clone())
                };
                lookup.unbind(key);
                continue;
            }

            // --- From here MSBuild *does* fold the name in, and promotion
            // runs after the built-in defaults. So any default we seeded for
            // this name (in practice `OS`) has been overwritten in the real
            // build. Whenever we cannot model the value MSBuild ends up with,
            // it is not enough to skip the insert: the stale default would
            // still be read, and a read of a seeded property *commits*. Drop
            // it, so the read degrades to undefined instead. ---
            let unmodellable =
                // The winner of a case-collision is unspecified — probed: with
                // `OS=Windows_NT` and `os=lowercase` both set, `$(OS)` changed
                // value when the environ order was reversed. Only the spellings
                // disagreeing makes that unspecified pick reach the value.
                spellings_disagree(&lower)
                // MSBuild promotes it, then the toolset overwrites it with a
                // host fact this crate cannot know.
                || is_env_ignored_toolset_name(&lower);

            if unmodellable {
                lookup.unbind(key);
                continue;
            }
            // An environment value is *already* in MSBuild's escaped domain and
            // is stored verbatim: MSBuild folds in
            // `((IProperty)envProperty).EvaluatedValueEscaped`
            // (`Evaluator.cs::AddEnvironmentProperties`), so a `%XX` in it is an
            // escape, not literal text — probed: `FOO=%54rue` makes
            // `'$(FOO)' == 'True'` fire, and `OS=%57indows_NT` reads
            // `Windows_NT`. `insert` is exactly that domain (`Escaped::from_xml`,
            // verbatim), the same one caller globals arrive in — *not*
            // `insert_computed`, which would escape the `%` on the way in and
            // make it inert. E1's unescape-at-the-point-of-use then produces
            // MSBuild's value for free.
            lookup.insert(key.clone(), value.clone());
        }
        // The ChangeWaves threshold. MSBuild reads the
        // `MSBUILDDISABLEFEATURESFROMVERSION` variable through
        // `Environment.GetEnvironmentVariable`, whose name lookup follows
        // the *host*: case-sensitive on Unix (probed: a lowercase or
        // mixed-case spelling is ignored), case-insensitive on Windows.
        // It exposes the *normalized* result as the reserved property:
        //   * unset or set-but-empty → the enable-all sentinel
        //     `999.999` (probed: `$(MSBuildDisableFeaturesFromVersion)`
        //     reads `999.999`, and `== ''` is False);
        //   * set to anything else → the value clamped against the
        //     version-dependent wave rotation (probed: `17.4` → `17.10`,
        //     `5.0` → `17.10`, `banana` → `999.999`), which we do not
        //     model — the property is left *undefined* so every read
        //     surfaces conservatively and `AreFeaturesEnabled` declines.
        // Seeded even for an empty snapshot — an empty environment is
        // itself a claim (see `parse_fsproj`'s docs).
        match changewave_env_value(environment, cfg!(windows)) {
            None | Some("") => {
                lookup.insert("MSBuildDisableFeaturesFromVersion", "999.999".to_string());
            }
            Some(_) => {}
        }
        #[cfg(any(test, feature = "test-support"))]
        let mut sticky_globals: HashSet<String> = HashSet::new();
        for (k, v) in extra_properties {
            // A caller global is *not* already-evaluated text: MSBuild unescapes
            // global property values on the way in (`-p:G=a%20b` makes `$(G)`
            // the string `a b` — probed against dotnet msbuild 10.0.301), so an
            // escape in one is live, exactly as in project XML. Plain insert.
            lookup.insert(k.clone(), v.clone());
            let lower = k.to_ascii_lowercase();
            if !local_overrides.contains(&lower) {
                protected.insert(lower.clone());
                // A non-treated-as-local global is read-only for the
                // whole walk: record it so the target executor can tell an
                // empty global (sticky) from an unset/body-written empty
                // (default-fillable).
                #[cfg(any(test, feature = "test-support"))]
                sticky_globals.insert(lower);
            }
        }
        let entry_project_dir = project_path
            .parent()
            .map(Path::to_path_buf)
            .unwrap_or_default();
        Self {
            lookup,
            protected,
            locally_overridable: local_overrides.clone(),
            reserved,
            #[cfg(any(test, feature = "test-support"))]
            sticky_globals,
            env_extensions_path,
            written: HashMap::new(),
            compile_first: Vec::new(),
            explicit_compile_before: Vec::new(),
            compile_before: Vec::new(),
            compile_main: Vec::new(),
            compile_after: Vec::new(),
            explicit_compile_after: Vec::new(),
            compile_last: Vec::new(),
            compile_excluded: Vec::new(),
            next_item_order: 0,
            project_references: Vec::new(),
            captured_package_references: Vec::new(),
            package_references: Vec::new(),
            #[cfg(any(test, feature = "test-support"))]
            package_reference_rows: Vec::new(),
            #[cfg(any(test, feature = "test-support"))]
            framework_reference_rows: Vec::new(),
            #[cfg(any(test, feature = "test-support"))]
            package_reference_unknown_names: HashSet::new(),
            #[cfg(any(test, feature = "test-support"))]
            package_version_rows: Vec::new(),
            #[cfg(any(test, feature = "test-support"))]
            #[cfg(any(test, feature = "test-support"))]
            global_package_reference_rows: Vec::new(),
            #[cfg(any(test, feature = "test-support"))]
            global_package_references_mutated: false,
            #[cfg(any(test, feature = "test-support"))]
            package_cause_owners: HashMap::new(),
            package_versions: Vec::new(),
            package_versions_untracked: false,
            default_targets_decided: false,
            global_package_references: Vec::new(),
            framework_references: Vec::new(),
            evaluated_items: HashMap::new(),
            tainted_item_lists: HashSet::new(),
            untracked_item_lists: HashSet::new(),
            helper_item_definition_defaults: HashMap::new(),
            #[cfg(any(test, feature = "test-support"))]
            item_definition_values: HashMap::new(),
            diagnostics: Vec::new(),
            follow_imports,
            imports_seen: HashSet::new(),
            imports_seen_fuzzy: HashSet::new(),
            walked_files: HashSet::new(),
            walked_directory_packages_props_import: None,
            depth: 0,
            entry_project_dir,
            parse_configuration_named: environment.iter().any(|(key, value)| {
                (if cfg!(windows) {
                    key.eq_ignore_ascii_case("MSBUILD_PARSE_CONFIG")
                } else {
                    key == "MSBUILD_PARSE_CONFIG"
                }) && !value.trim().is_empty()
            }),
            import_site_span: None,
            sdk_resolver,
            glob_resolver,
            observer,
            hoisted_sdk_imports: HashSet::new(),
            directory_build: directory_build::Bookkeeping::default(),
            enclosing_condition_stale: None,
            resolved_sdk_root: None,
            entry_sdk_version_dir: None,
            foreign_definitions: crate::ForeignDefinitions::default(),
            workload_definitions: crate::ForeignDefinitions::default(),
            sdk_files_imported_from_outside: BTreeSet::new(),
            compile_context: false,
            in_sdk_subtree: false,
            in_foreign_document: true,
            foreign_write_failures: std::collections::BTreeMap::new(),
            workload_manifests_outside_install: BTreeSet::new(),
            imported_sdk_files: BTreeSet::new(),
            workload_manifest_files: BTreeSet::new(),
            sdk_tolerance_roots: Vec::new(),
            items_uncertain: false,
            define_constants_uncertainties: Vec::new(),
            define_context: false,
            in_define_value: false,
            define_constants_uncertain: false,
            import_gate_context: false,
            package_import_gate_context: false,
            compile_condition_uncertainties: Vec::new(),
            compile_item_uncertainties: Vec::new(),
            package_context: false,
            project_references_uncertain: false,
            project_reference_includes_hidden: false,
            package_references_uncertain: false,
            package_reference_uncertainties: Vec::new(),
            current_file: CurrentFile::Entry,
            deferred_item_groups: Vec::new(),
            retained_imported_files: Vec::new(),
            #[cfg(any(test, feature = "test-support"))]
            entry_project_path: project_path.to_path_buf(),
            #[cfg(any(test, feature = "test-support"))]
            target_definitions: Vec::new(),
            #[cfg(any(test, feature = "test-support"))]
            initial_targets_named: false,
            #[cfg(any(test, feature = "test-support"))]
            using_task_names: Vec::new(),
            env_property_names,
            walk_opaque: None,
            rejection: None,
            noted_sites: Vec::new(),
            second_walk: false,
            rewritten_after_refusal: HashSet::new(),
            second_walk_needed: std::cell::Cell::new(false),
            site_file: None,
            reach_doubted: 0,
            taken_import_path_certain: false,
            item_pass: None,
            speculation: None,
            arm_decisions: HashMap::new(),
            diagnostic_roots: HashMap::new(),
        }
    }

    /// Whether an undefined `$(name)` read is *exactly* the empty string
    /// in the real build too — the C.2b guard (see
    /// `docs/completed/sdk-chain-exactness-plan.md`). True only when every input
    /// that could have supplied the name says it doesn't exist:
    ///   * the walk has hidden no content (`walk_opaque`);
    ///   * no undecided or refused write could have set it — every
    ///     [`Trust`] channel is clean, the taint one included, since it
    ///     covers maybe-skipped writes whose gate leaned on tainted input;
    ///   * the name is not in the environment snapshot (a skipped
    ///     promotion — collision or toolset overwrite — still means the
    ///     real build defines *something*);
    ///   * the name is not a toolset-computed initial property.
    fn undefined_read_is_exact(&self, name: &str) -> bool {
        self.walk_opaque.is_none() && self.undefined_read_is_exact_but_for_opacity(name)
    }

    /// [`Self::undefined_read_is_exact`] without the opacity clause: whether
    /// `name`'s absence would be a fact had the walk seen every write.
    fn undefined_read_is_exact_but_for_opacity(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        // A consumer-contract carve-out, not an exactness fact: the define
        // machinery treats an undefined `$(DefineConstants)` as "the SDK
        // may set DEBUG/TRACE" (its uncertainty axis feeds the LSP's
        // `#if` handling).
        if lower == "defineconstants" {
            return false;
        }
        !self.env_property_names.contains(&lower)
            && self.trust_of(name).is_certain()
            && !is_toolset_initial_property_name(&lower)
    }

    /// Is `name` reading as undefined because it *is* undefined in the real
    /// build, or because the walk could not work out what it holds? Asked by
    /// the default-fill exemption ([`evaluate_condition_with_exemptions`]),
    /// whose whole justification is the former.
    ///
    /// The exemption believes the walker's environment model (a name absent
    /// from the caller's environment snapshot, and written by no file the walk
    /// saw, is unset), and nothing more. So it does not extend to a name the
    /// real build may give a value the walk cannot see:
    ///
    /// * [`Self::walk_opaque`] — the walk has passed content it could not see
    ///   (an import it could not follow, or one whose gate or path it could not
    ///   decide), and that content may write the name. The file may be one
    ///   only an input the evaluation lacks can locate: a build's working
    ///   directory (`MSBuildStartupDirectory`, which a served evaluation never
    ///   has) or a toolset value the walk does not seed, so neither the
    ///   project nor its SDK says what it writes. The SDK leans on the idiom
    ///   pervasively, but on the measured corpora the walk reaches it behind
    ///   hidden content only in projects MSBuild rejects or whose items it
    ///   declines already (`docs/msbuild-value-carried-provenance-plan.md`,
    ///   "the default-fill exemption behind opacity, withdrawn").
    /// * [`Trust::refused`] — a write we refused. Its emptiness here
    ///   is our failure to compute, not a fact; MSBuild holds what it computed
    ///   and takes the other branch.
    /// * [`Self::env_property_names`] — an environment name promotion skipped
    ///   (a case collision, a toolset overwrite). We dropped it from the lookup
    ///   precisely because we cannot model its value, and "cannot model" is not
    ///   "unset": the real build defines *something* non-empty.
    /// * [`is_toolset_predefined_name`] — a name MSBuild's toolset defines
    ///   before evaluation starts. The walk holds no value for one only when it
    ///   has not seeded it (no canonical SDK resolved, the seed was withheld,
    ///   or the toolset is one whose value we do not know), and the real build
    ///   holds its own value all the same.
    ///
    /// The value channels of [`Trust`] (taint, unpinned, stale) are
    /// deliberately *not* consulted: each describes a value we hold and may
    /// have wrong, whereas this asks about a name that read as absent.
    /// Widening to [`Trust::is_certain`] would refuse the idiom wherever any
    /// earlier write to the name was undecided.
    fn self_default_absence_is_a_fact(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        self.walk_opaque.is_none()
            && !self.trust_of(name).refused()
            && !self.env_property_names.contains(&lower)
            && !is_toolset_predefined_name(&lower)
    }

    /// Record the [`SdkPaths::root`] of the entry project's own SDK.
    ///
    /// Called **only** for the entry root's `Sdk` shorthand and its
    /// promoted explicit form — the unambiguous framework SDK. We deliberately
    /// do *not* record SDKs reached anywhere else (nested imports, an imported
    /// file's own root `Sdk`, `Directory.Build.{props,targets}` helpers): which
    /// of a body's many `<Import Sdk=...>` / `Sdk.props` / `Sdk.targets` hits
    /// "establishes" the framework is subtle and order-dependent, so rather
    /// than guess we leave [`ParsedProject::resolved_sdk_root`] `None` for
    /// SDK-less entries and let the consumer fall back to its own default-root
    /// probe. `first`-wins is therefore moot in practice (one entry SDK), but
    /// kept so a future explicit-form change can't double-record.
    fn record_sdk_root(&mut self, root: &Path) {
        let first = self.resolved_sdk_root.is_none();
        self.resolved_sdk_root
            .get_or_insert_with(|| root.to_path_buf());
        // Also tolerate it: this is the entry chokepoint for both the `Sdk`
        // shorthand and the promoted explicit form (`<Import Sdk=… Project=
        // "Sdk.props"/>` as the first body element), and the latter resolves on
        // a path that never reaches `resolve_project_sdk`. Without this its SDK
        // props/targets would be judged user-authored.
        let version_dir = self.note_sdk_tolerance(root);
        if first {
            self.entry_sdk_version_dir = version_dir;
        }
    }

    /// Add an SDK root to the tolerance set ([`Self::sdk_tolerance_roots`]).
    /// Called at *every* successful SDK resolution — the entry SDK, a nested
    /// imported file's root `Sdk`, and an `<Import Sdk=…>` — so an SDK variant
    /// that imports a base SDK from a sibling directory is tolerated too.
    ///
    /// For the canonical .NET layout (`…/sdk/<version>/Sdks/<name>/Sdk`) the
    /// conditional default-item files (`targets/…DefaultItems…`) sit in the
    /// *sibling* `…/Sdks/<name>/targets/`, and the SDK import graph also reaches
    /// shared version-level files such as `Current/Microsoft.Common.props`,
    /// `Microsoft.Common.targets`, and language targets. So we tolerate both the
    /// SDK-specific parent (`…/Sdks/<name>`) and the version directory
    /// (`…/sdk/<version>`). For any other layout — a custom/local resolver that
    /// returns a self-contained `root` directly holding `Sdk.{props,targets}`
    /// ([`SdkPaths`] allows this) — we tolerate `root` itself: broadening to its
    /// parent would wrongly mark a user-authored `Directory.Build.props` (or
    /// explicit import) sitting beside it as SDK-internal. Canonical so it
    /// compares against the canonicalised paths [`walk_external_file`] checks
    /// (both the file's own canonical path and the canonicalisation of an
    /// imported file's parent directory). Deduplicated (resolution sites
    /// overlap).
    ///
    /// Returns the canonical version directory, for the canonical layout.
    fn note_sdk_tolerance(&mut self, root: &Path) -> Option<PathBuf> {
        let version_dir = dotnet_sdk_version_dir(root);
        let boundaries: Vec<&Path> = if let Some(version_dir) = version_dir {
            self.seed_toolset_properties(version_dir);
            vec![root.parent().unwrap_or(root), version_dir]
        } else {
            vec![root]
        };
        let mut canonical_version_dir = None;
        for boundary in boundaries {
            let canon = observed::canonicalize(self.observer, boundary)
                .unwrap_or_else(|_| boundary.to_path_buf());
            if Some(boundary) == version_dir {
                canonical_version_dir = Some(canon.clone());
            }
            if !self.sdk_tolerance_roots.contains(&canon) {
                self.sdk_tolerance_roots.push(canon);
            }
        }
        canonical_version_dir
    }

    /// Seed the MSBuild toolset properties from a canonical .NET SDK
    /// version directory. In a real `dotnet msbuild` these exist from
    /// process start; this walker only learns where the toolset lives
    /// when an SDK resolves to the canonical layout, so the seed happens
    /// here — before the first SDK file is walked, which is also the
    /// first place anything can read them. Without them the SDK's own
    /// `Sdk.props` line
    /// `<Import Project="$(MSBuildExtensionsPath)\$(MSBuildToolsVersion)\Microsoft.Common.props"/>`
    /// cannot resolve, and nothing downstream of `Microsoft.Common.props`
    /// (`NuGet.props`, `Directory.Packages.props`) is ever reached.
    ///
    /// Values verified against `dotnet msbuild -getProperty:…` (10.0.300):
    /// the three path properties equal the version directory —
    /// `MSBuildExtensionsPath` *with* a trailing separator, the others
    /// without — `MSBuildSDKsPath` is its `Sdks` child, and
    /// `MSBuildToolsVersion`/`MSBuildRuntimeType` are the fixed strings
    /// `Current`/`Core`. `MSBuildAssemblyVersion` is the toolset's product
    /// version where that is probed ([`toolset_assembly_version`]).
    /// Writability was probed the same way:
    /// `MSBuildToolsPath`, `MSBuildBinPath`, `MSBuildToolsVersion`,
    /// `MSBuildRuntimeType` and `MSBuildAssemblyVersion` are reserved (a
    /// project write is MSB4004;
    /// this walker's model for protected names is to drop the write),
    /// while `MSBuildExtensionsPath`, `MSBuildExtensionsPath32` and
    /// `MSBuildSDKsPath` accept project writes.
    ///
    /// The reserved group replaces any prior *project* write (real
    /// MSBuild rejects those outright — MSB4004 — so the stored value is
    /// one no real evaluation ever sees) and cannot arrive via
    /// `extra_properties` (`validate_inputs` rejects the names). The
    /// overridable group is insert-if-absent: caller globals and project
    /// writes legitimately win there. Either way the first canonical SDK
    /// resolution's seed wins over later ones.
    fn seed_toolset_properties(&mut self, version_dir: &Path) {
        // Real `dotnet msbuild` reports its own fully-resolved location
        // (the process resolves symlinks to find itself), so canonicalise
        // for the same shape; the tolerance roots are canonical too.
        let version_dir = observed::canonicalize(self.observer, version_dir)
            .unwrap_or_else(|_| version_dir.to_path_buf());
        let dir = version_dir.to_string_lossy().replace('\\', "/");
        // The toolset is the first canonical SDK's, so a later resolution
        // seeds nothing the first one declined to.
        let first_toolset = !self.reserved.contains("msbuildtoolspath");
        let mut reserved = vec![
            ("MSBuildToolsPath", dir.clone()),
            ("MSBuildBinPath", dir.clone()),
            ("MSBuildToolsVersion", "Current".to_string()),
            ("MSBuildRuntimeType", "Core".to_string()),
        ];
        // A toolset whose product version is not probed gets no seed, and a
        // read of the name stays undefined and inexact
        // (`is_toolset_initial_property_name`).
        if first_toolset && let Some(value) = toolset_assembly_version(&version_dir) {
            reserved.push(("MSBuildAssemblyVersion", value.to_string()));
        }
        for (name, value) in reserved {
            let lower = name.to_ascii_lowercase();
            // First canonical seed wins over later SDK resolutions, and a
            // caller-supplied global (the documented environment model)
            // wins over the seed. A *project* write that landed before
            // the first SDK resolved does NOT win: real MSBuild has
            // these names reserved from process start and rejects the
            // write outright (MSB4004), so the stored value is one no
            // real evaluation ever sees — replace it and scrub its
            // bookkeeping so stale unpinned/taint marks don't outlive
            // the value they described.
            // (`validate_inputs` rejects these names in `extra_properties`,
            // so no caller-global can reach here.)
            if self.reserved.contains(&lower) {
                continue;
            }
            // Evaluator-computed (SDK/toolset paths and toolset constants), not
            // project XML: percents in them are literal.
            self.lookup.insert_computed(name, value);
            self.written.remove(&lower);
            // Scrub both provenance marks so a stale taint/unpinned entry
            // doesn't outlive the value it described.
            self.apply_property_provenance(
                name,
                PropertyProvenance {
                    taint: TaintOutcome::Clear,
                    unpinned: UnpinnedOutcome::Clear,
                    // MSB4004: the real build refuses a project write to a
                    // reserved name and keeps its own value, which is the one
                    // being seeded here. A refusal we recorded describes a
                    // write no real evaluation performs.
                    refused: RefusedOutcome::Clear,
                    // No file can rewrite a reserved name, so it never goes
                    // stale; cleared with the rest for the same reason.
                    stale: StaleOutcome::Clear,
                },
            );
            self.reserved.insert(lower.clone());
            self.protected.insert(lower);
        }
        // The overridable names below take a write from any source, so an
        // empty slot is the toolset's only if nothing that could have written
        // it is out of sight. Content the walk could not see (an import it
        // could not follow, or one whose gate it could not decide) may have
        // written any of them before this SDK resolved, and a hidden write
        // leaves no trust record. So under opacity none is seeded, and every
        // read of one declines: an undefined read behind opacity is never
        // exact, and a self-default write never takes the absence of a
        // toolset-predefined name for a fact (`is_toolset_predefined_name`).
        // The reserved seeds above stand regardless: MSBuild refuses a write
        // to them (MSB4004), hidden or not.
        if self.walk_opaque.is_some() {
            return;
        }
        // `VisualStudioVersion` is a toolset constant every name source can
        // displace: the environment (MSBuild honours a spoof on every
        // toolset), a caller global, or a project write. So it is seeded only
        // into a slot none of them claimed — not defined, not in the
        // environment snapshot (promoted or dropped, the real build has *some*
        // value for it), and never the subject of a write we could not decide
        // or refused.
        if !self.lookup.is_bound("VisualStudioVersion")
            && !self.env_property_names.contains("visualstudioversion")
            && self.trust_of("VisualStudioVersion").is_certain()
            && let Some(value) = toolset_visual_studio_version(&version_dir)
        {
            self.lookup.insert_computed("VisualStudioVersion", value);
        }
        let overridable = [
            ("MSBuildExtensionsPath32", dir.clone()),
            ("MSBuildSDKsPath", format!("{dir}/Sdks")),
        ];
        for (name, value) in overridable {
            // A name in the environment snapshot that promotion dropped
            // (spellings that disagree) has *some* value in the real build:
            // both toolsets probed honour the environment for these two (see
            // `toolset_honours_env_extensions_path`), so it is one of the
            // environment's values, not the toolset's path. The slot stays
            // empty and reads decline.
            if !self.lookup.is_bound(name)
                && !self.env_property_names.contains(&name.to_ascii_lowercase())
            {
                // Same provenance as the reserved seeds above: our own paths.
                self.lookup.insert_computed(name, value);
            }
        }
        // `MSBuildExtensionsPath` is overridable in the same way — a caller
        // global or a project write wins on every toolset (probed against
        // 8.0.420: `-p:MSBuildExtensionsPath=/SPOOF` redirects the `Sdk.props`
        // import even where an environment variable of the same name would
        // have been overwritten) — so an occupied slot still stands.
        //
        // The *environment* is the special case, and the only one in the whole
        // environment model whose answer depends on the toolset version: see
        // `toolset_honours_env_extensions_path`. Now that an SDK has named the
        // toolset, the value parked in `State::new` can be adjudicated.
        if !self.lookup.is_bound("MSBuildExtensionsPath") {
            let toolset_value = format!("{dir}/");
            match (
                &self.env_extensions_path,
                toolset_honours_env_extensions_path(&version_dir),
            ) {
                // No environment value: every toolset computes the property
                // from its own directory, so there is nothing to adjudicate.
                (EnvExtensionsPath::Absent, _) => {
                    self.lookup
                        .insert_computed("MSBuildExtensionsPath", toolset_value);
                }
                // An environment value the toolset overwrites — the toolset's
                // own directory is the value the real build reads.
                (_, Some(false)) => {
                    self.lookup
                        .insert_computed("MSBuildExtensionsPath", toolset_value);
                }
                // MSBuild 18 lets it stand. Escaped-domain text, exactly as it
                // arrived (see the promotion loop in `State::new`), so `insert`
                // rather than `insert_computed`.
                (EnvExtensionsPath::Value(value), Some(true)) => {
                    self.lookup
                        .insert("MSBuildExtensionsPath", value.to_string());
                }
                // The toolset would honour a value we cannot name (colliding
                // spellings), or we cannot read the toolset's version and so
                // cannot say which of the two behaviours applies. Either way,
                // leave the property undefined: the read declines instead of
                // committing a guess.
                (EnvExtensionsPath::Unspecified, Some(true)) | (_, None) => {}
            }
        }
    }

    fn into_project(self) -> ParsedProject {
        debug_assert!(
            self.deferred_item_groups.is_empty(),
            "the item pass must consume every deferred ItemGroup before \
             the walk produces its result"
        );
        // Content the walk could not see may hold or import anything, so
        // neither the Compile order (#819, #821), the reference list (#848)
        // nor the define set (#843, #862) is certain after it: every site that
        // latches opacity withdraws all three, in an SDK file as anywhere.
        debug_assert!(
            self.walk_opaque.is_none() || self.items_uncertain,
            "the walk hid content ({:?}) but kept its Compile set certain",
            self.walk_opaque
        );
        debug_assert!(
            self.walk_opaque.is_none() || self.project_references_uncertain,
            "the walk hid content ({:?}) but kept its reference list certain",
            self.walk_opaque
        );
        debug_assert!(
            self.walk_opaque.is_none() || self.define_constants_uncertain,
            "the walk hid content ({:?}) but kept its define set certain",
            self.walk_opaque
        );
        // The output-name verdict and the property reads need `&self`, so
        // compute them before the destructure below consumes it.
        let target_name = self.target_name_verdict();
        let property_reads = self.property_reads();
        let hidden_content = self
            .walk_opaque
            .as_ref()
            .map(crate::UntrustedCause::of_opacity);
        let State {
            lookup,
            protected: _,
            reserved: _,
            #[cfg(any(test, feature = "test-support"))]
                sticky_globals: _,
            env_extensions_path: _,
            written,
            compile_first,
            explicit_compile_before,
            compile_before,
            compile_main,
            compile_after,
            explicit_compile_after,
            compile_last,
            compile_excluded: _,
            next_item_order: _,
            project_references,
            // Already collapsed into `package_references` by the item pass's
            // `finalize_package_references`.
            captured_package_references: _,
            package_references,
            #[cfg(any(test, feature = "test-support"))]
                package_reference_rows: _,
            #[cfg(any(test, feature = "test-support"))]
                framework_reference_rows: _,
            #[cfg(any(test, feature = "test-support"))]
                package_reference_unknown_names: _,
            #[cfg(any(test, feature = "test-support"))]
                package_version_rows: _,
            #[cfg(any(test, feature = "test-support"))]
                global_package_reference_rows: _,
            #[cfg(any(test, feature = "test-support"))]
                global_package_references_mutated: _,
            #[cfg(any(test, feature = "test-support"))]
                package_cause_owners: _,
            default_targets_decided: _,
            package_versions,
            package_versions_untracked,
            global_package_references,
            framework_references,
            evaluated_items: _,
            tainted_item_lists: _,
            untracked_item_lists: _,
            helper_item_definition_defaults: _,
            #[cfg(any(test, feature = "test-support"))]
                item_definition_values: _,
            diagnostics,
            follow_imports: _,
            imports_seen: _,
            imports_seen_fuzzy: _,
            walked_files: _,
            walked_directory_packages_props_import: _,
            depth: _,
            entry_project_dir: _,
            parse_configuration_named: _,
            import_site_span: _,
            sdk_resolver: _,
            glob_resolver: _,
            observer: _,
            hoisted_sdk_imports: _,
            directory_build: _,
            enclosing_condition_stale: _,
            resolved_sdk_root,
            entry_sdk_version_dir: _,
            foreign_definitions,
            workload_definitions,
            sdk_files_imported_from_outside,
            locally_overridable,
            compile_context: _,
            in_sdk_subtree: _,
            in_foreign_document: _,
            foreign_write_failures,
            workload_manifests_outside_install,
            imported_sdk_files,
            workload_manifest_files,
            sdk_tolerance_roots: _,
            items_uncertain,
            define_context: _,
            in_define_value: _,
            define_constants_uncertain,
            define_constants_uncertainties,
            import_gate_context: _,
            package_import_gate_context: _,
            compile_condition_uncertainties,
            compile_item_uncertainties,
            package_context: _,
            project_references_uncertain,
            project_reference_includes_hidden,
            package_references_uncertain,
            package_reference_uncertainties,
            current_file: _,
            deferred_item_groups: _,
            retained_imported_files: _,
            #[cfg(any(test, feature = "test-support"))]
                entry_project_path: _,
            #[cfg(any(test, feature = "test-support"))]
                target_definitions: _,
            #[cfg(any(test, feature = "test-support"))]
                initial_targets_named: _,
            #[cfg(any(test, feature = "test-support"))]
                using_task_names: _,
            env_property_names: _,
            walk_opaque: _,
            rejection,
            noted_sites: _,
            second_walk: _,
            rewritten_after_refusal: _,
            second_walk_needed: _,
            site_file: _,
            reach_doubted: _,
            taken_import_path_certain: _,
            item_pass: _,
            speculation: _,
            arm_decisions: _,
            diagnostic_roots: _,
        } = self;
        // Central Package Management opt-in: a versionless
        // `<PackageReference Include="X"/>` may receive its effective version
        // from `<PackageVersion>` items. Start conservative, then let the
        // inline CPM pass below clear the uncertainty only for the exact subset
        // it can prove from already-captured items.
        // Both opt-in flags are read by MSBuild `==` comparisons in
        // `NuGet.targets` (`'$(ManagePackageVersionsCentrally)' == 'true' AND
        // '$(CentralPackageVersionsFileImported)' == 'true'`), so they take the
        // boolean vocabulary, not string equality — see [`is_msbuild_true`].
        //
        // Their trust is answered at the write, not here: a CPM flag's
        // condition and value are package-affecting (`package_context`), so an
        // untrusted write of either already left the package set uncertain.
        let manages_versions_centrally = lookup
            .get_unescaped_ignoring_trust("ManagePackageVersionsCentrally")
            .is_some_and(|v| is_msbuild_true(&v));
        let central_package_versions_file_imported = lookup
            .get_unescaped_ignoring_trust("CentralPackageVersionsFileImported")
            .is_some_and(|v| is_msbuild_true(&v));
        // `CentralPackageVersionOverrideEnabled` is different in kind: the SDK
        // does not compare it, it forwards the raw value to the restore task,
        // so the vocabulary is NuGet's C# rather than MSBuild's and this crate
        // cannot ground-truth it with the condition oracle. Treat *either*
        // reading's "false" as opting out, which is a superset of the literal
        // spelling and therefore conservative under both: an opt-out keeps the
        // reference unresolved (`all_includes_resolved = false`), so widening
        // it can only retain uncertainty, never commit a version override the
        // real restore would reject.
        let central_package_version_override_enabled = !lookup
            .get_unescaped_ignoring_trust("CentralPackageVersionOverrideEnabled")
            .is_some_and(|v| condition::parse_msbuild_bool(&v) == Some(false));
        // `package_references` is already the effective (Include + Update
        // collapsed) set, with versionless uncertainty detected on it, from the
        // item pass's `finalize_package_references`.
        let mut package_references = package_references;
        let mut package_references_uncertain = package_references_uncertain;
        let mut package_reference_uncertainties = package_reference_uncertainties;
        if manages_versions_centrally {
            package_references_uncertain = true;
            package_reference_uncertainties.push(PackageReferenceUncertaintyCause {
                kind: PackageReferenceUncertaintyCauseKind::ManagePackageVersionsCentrally,
                span: 0..0,
                origin: DiagnosticOrigin::Buffer,
            });
        }
        apply_inline_cpm_versions(
            manages_versions_centrally && central_package_versions_file_imported,
            &mut package_references,
            &package_versions,
            package_versions_untracked,
            &global_package_references,
            central_package_version_override_enabled,
            &mut package_reference_uncertainties,
        );
        if package_reference_uncertainties.is_empty() {
            package_references_uncertain = false;
        }
        // MSBuild may reject the project, and then holds nothing, whatever the
        // walk bound before or after the construct: every facet is withdrawn,
        // each axis naming the rejection as its cause. The property reads
        // were withdrawn above, by `read_property`.
        let mut items_uncertain = items_uncertain;
        let mut compile_item_uncertainties = compile_item_uncertainties;
        let mut define_constants_uncertain = define_constants_uncertain;
        let mut define_constants_uncertainties = define_constants_uncertainties;
        let mut project_references_uncertain = project_references_uncertain;
        let mut hidden_content = hidden_content;
        if let Some(rejection) = &rejection {
            let kind = rejection.diagnostic_kind();
            let (span, origin) = (rejection.span.clone(), rejection.origin.clone());
            items_uncertain = true;
            compile_item_uncertainties.push(CompileItemUncertaintyCause {
                kind: CompileItemUncertaintyCauseKind::Diagnostic(kind.clone()),
                span: span.clone(),
                origin: origin.clone(),
            });
            define_constants_uncertain = true;
            define_constants_uncertainties.push(DefineConstantsUncertaintyCause {
                kind: DefineConstantsUncertaintyCauseKind::Diagnostic(kind.clone()),
                span: span.clone(),
                origin: origin.clone(),
            });
            package_references_uncertain = true;
            package_reference_uncertainties.push(PackageReferenceUncertaintyCause {
                kind: PackageReferenceUncertaintyCauseKind::Diagnostic(kind),
                span,
                origin,
            });
            project_references_uncertain = true;
            hidden_content.get_or_insert_with(|| {
                crate::UntrustedCause::Rejected(Box::new(rejection.clone()))
            });
        }
        let is_partial = !diagnostics.is_empty();
        let mut items = into_resolved_items(compile_first);
        items.extend(into_resolved_items(explicit_compile_before));
        items.extend(into_resolved_items(compile_before));
        items.extend(into_resolved_items(compile_main));
        items.extend(into_resolved_items(compile_after));
        items.extend(into_resolved_items(explicit_compile_after));
        items.extend(into_resolved_items(compile_last));
        let project_references = into_resolved_items(project_references);
        // `properties` is documented as "what the project wrote". Use
        // the project's canonical casing as recorded in `written` for
        // the output keys — otherwise a treated-as-local override
        // where extras supplied a different casing would surface the
        // extras casing here, and an exact `properties.get("Foo")`
        // would miss the project's write. Look the value up via
        // case-insensitive `PropertyMap::get`, which handles the same
        // mismatch on the value side.
        let properties = written
            .into_values()
            .filter_map(|project_name| {
                // Trust-blind by contract: `property_reads` carries each
                // name's trust to a consumer that decides on it.
                lookup
                    .get_unescaped_ignoring_trust(&project_name)
                    .map(|v| (project_name, v))
            })
            .collect();
        // `define_constants` reflects the *evaluated* `$(DefineConstants)`
        // value: globals supplied via `extra_properties` and reserved
        // well-knowns are deliberately absent from `properties` (which
        // documents "what the project wrote"), but the F# preprocessor
        // sees the merged effect. Source the value from `lookup`, which
        // is the same map MSBuild would consult when expanding
        // `$(DefineConstants)` itself.
        // The list is split on the semicolons of the **escaped** value and each
        // fragment decoded after — MSBuild's property-to-list conversion, which
        // makes `A%3bB` the single define `A;B` rather than two
        // (oracle-pinned 2026-07-12). Decoding first would split it in two.
        // Its trust is `define_constants_uncertain`, a consequence-side flag
        // raised where a user-authored write could diverge.
        let define_constants = lookup
            .get_ignoring_trust("DefineConstants")
            .map(crate::define_constants_from_escaped)
            .unwrap_or_default();
        // Same rule, same reason: split the escaped value, decode each fragment.
        // The plural is consumed as a declared list whose TFM-invariant
        // intersection trusts no single branch (the `msbuild-trust-audit`
        // skill, entry 11), so its trust is not read here.
        let target_frameworks: Vec<String> = lookup
            .get_ignoring_trust("TargetFrameworks")
            .map(|v| {
                v.split_list()
                    .map(|f| f.unescape().trim().to_string())
                    .filter(|s| !s.is_empty())
                    .collect()
            })
            .unwrap_or_default();
        // `<LangVersion>` from the same merged map. Trim and drop empties so an
        // unset (or whitespace-only) value reads as `None` rather than `Some("")`.
        // Published beside `property_reads`; the LSP reads the
        // `LangVersion` read there into its fold's cache key, beside the
        // consequence-side `shape_depends_on_language_version`.
        let lang_version_untrimmed = lookup
            .get_unescaped_ignoring_trust("LangVersion")
            .map(|v| v.to_string())
            .filter(|s| !s.is_empty());
        let other_flags = lookup
            .get_unescaped_ignoring_trust("OtherFlags")
            .map(|v| v.to_string())
            .filter(|s| !s.is_empty());
        let lang_version = lang_version_untrimmed
            .as_deref()
            .map(|v| v.trim().to_string())
            .filter(|s| !s.is_empty());
        ParsedProject {
            target_frameworks,
            items,
            project_references,
            project_references_uncertain,
            project_references_incomplete: project_reference_includes_hidden,
            package_references,
            package_versions,
            global_package_references,
            framework_references,
            properties,
            define_constants,
            lang_version,
            lang_version_untrimmed,
            other_flags,
            target_name,
            property_reads,
            foreign_definitions,
            workload_definitions,
            sdk_files_imported_from_outside,
            foreign_write_failures,
            workload_manifests_outside_install,
            imported_sdk_files,
            workload_manifest_files,
            auto_response_file: crate::AutoResponseFile::Unread,
            hidden_content,
            rejection,
            diagnostics,
            is_partial,
            items_uncertain,
            define_constants_uncertain,
            define_constants_uncertainties,
            compile_condition_uncertainties,
            compile_item_uncertainties,
            package_references_uncertain,
            package_reference_uncertainties,
            locally_overridable_properties: locally_overridable.into_iter().collect(),
            // The read set is the whole evaluation's, every pass included, so
            // `parse_fsproj_with_imports` fills it in once the walk is done.
            read_set: ReadSet::default(),
            read_counts: ReadCounts::default(),
            resolved_sdk_root,
        }
    }

    /// Whether `name` (case-insensitive) is *currently* a read-only
    /// global property — i.e. one MSBuild's `Microsoft.Common.props`
    /// default-fill cannot write through. See [`State::sticky_globals`].
    ///
    /// A name only counts as sticky while it is *also* still protected:
    /// an imported root's `TreatAsLocalProperty` unprotects a global for
    /// that file's scope (removing it from [`State::protected`]), which
    /// makes it locally writable there — so the default-fill *can* write
    /// through and the sticky-global short-circuit must stand down. This
    /// keeps the answer in lockstep with the `TreatAsLocalProperty` model
    /// `walk_external_file` already implements via `protected`.
    #[cfg(any(test, feature = "test-support"))]
    fn is_sticky_global(&self, name: &str) -> bool {
        let lower = name.to_ascii_lowercase();
        self.sticky_globals.contains(&lower) && self.protected.contains(&lower)
    }

    /// Flag the package/framework-reference set as untrustworthy for a
    /// divergence that raises no diagnostic (an ignored `Remove`, an
    /// `@(…)`/`%(…)` reference in an `Include`, a substitution issue). Only
    /// effective in a `package_context`, matching the diagnostic-driven flip in
    /// [`Self::push`].
    fn note_package_uncertain(
        &mut self,
        kind: PackageReferenceUncertaintyCauseKind,
        span: Range<usize>,
    ) {
        if self.package_context {
            self.package_references_uncertain = true;
            self.record_package_reference_uncertainty(kind, span);
        }
    }

    /// Mark the package/framework-reference set untrustworthy because a
    /// structural construct that can carry dependency items was skipped, and
    /// latch opacity. Only [`Self::mark_structural_skip`] calls it, so the
    /// Compile set and the reference list are withdrawn with it.
    fn mark_package_structural_skip(
        &mut self,
        kind: StructuralPackageReferenceUncertainty,
        span: Range<usize>,
    ) {
        self.package_references_uncertain = true;
        // Every structural skip funnels through here, and each one hides
        // content that could carry property writes — an unfollowable SDK
        // or import, a malformed Choose (which fails MSBuild's evaluation
        // outright). An undecided Choose does not come here: its branch
        // writes are enumerated per name instead.
        self.latch_walk_opaque(
            OpacityCause::Unentered(format!("{kind:?}").into()),
            span.clone(),
        );
        self.record_package_reference_uncertainty(
            PackageReferenceUncertaintyCauseKind::Structural(kind),
            span,
        );
    }

    /// Mark every captured item set untrustworthy because a structural
    /// construct that can carry them was skipped — a dropped/unfollowable
    /// `<Import>` or SDK, or a malformed `<Choose>` — wherever it is. Such a
    /// construct can hold `<Compile>`, `<ProjectReference>` and
    /// `<PackageReference>`/`<FrameworkReference>` items alike, import a user
    /// file that does, or import a file a later import names again (which
    /// MSBuild then skips as a duplicate, #819). So no item set is certain once
    /// the walk has passed it, in an SDK file as anywhere (#821, #848): that
    /// the construct sits in an SDK file says nothing of what it reaches.
    /// (Build-time-only containers like `<Target>` never call this — they
    /// contribute to no *static* set, matching MSBuild's static item
    /// evaluation.)
    fn mark_structural_skip(&mut self, kind: StructuralCompileItemUncertainty, span: Range<usize>) {
        // The un-descended `<Choose>` is not content the walk failed to
        // enter: its branches are scanned for reference operations instead
        // ([`item_pass::UndecidedChooseItems`]), and a malformed one, which
        // MSBuild refuses to load, withdraws the list at its own site. The
        // rule is [`StructuralCompileItemUncertainty::hides_project_references`]
        // rather than a local `matches!`, because a consumer explaining the
        // dropped reference list must borrow exactly the subset that caused
        // it.
        if kind.hides_project_references() {
            self.project_references_uncertain = true;
        }
        self.items_uncertain = true;
        self.mark_package_structural_skip(
            package_structural_uncertainty_from_compile(&kind),
            span.clone(),
        );
        self.record_compile_item_uncertainty(
            CompileItemUncertaintyCauseKind::Structural(kind),
            span,
        );
    }

    fn push(&mut self, kind: DiagnosticKind, span: Range<usize>) {
        self.push_on_define_axis(kind, span, DefineAxis::Doubts);
    }

    /// [`Self::push`], with the diagnostic's effect on the define axis chosen
    /// by the caller. Only [`Self::push_undefined_read`] chooses
    /// [`DefineAxis::SelfAppend`], for the one read it can see is the idiom.
    fn push_on_define_axis(
        &mut self,
        kind: DiagnosticKind,
        span: Range<usize>,
        define_axis: DefineAxis,
    ) {
        // An import that did not load fails MSBuild's evaluation (#845), but
        // for the walk's own depth limit, which MSBuild does not have. Judged
        // before the failure latches the walk opaque below: what it hides
        // comes after it.
        let failed_import = match &kind {
            DiagnosticKind::ImportFailed { path, reason }
                if !matches!(reason, ImportFailReason::DepthLimit { .. }) =>
            {
                let certainty = rejection::import_failure_certainty(self, path, reason);
                Some((
                    path.display().to_string(),
                    reason.clone(),
                    span.clone(),
                    certainty,
                ))
            }
            _ => None,
        };
        // `import_site_span.is_some()` iff we're currently walking an
        // imported file — `walk_external_file` sets it on first
        // descent and preserves it on nested descents. That's the
        // same condition `effective_span` already keys on, so the two
        // stay in lockstep without extra state: any diagnostic whose
        // span was remapped also gets `Imported`, and any diagnostic
        // produced from the entry project keeps its native span and
        // `Buffer`.
        // Any diagnostic raised while resolving a Compile item/group concerns
        // *that* item's inclusion, so it makes the Compile set untrustworthy.
        // So does one raised while deciding an import's gate, and a kind that
        // means a file's worth of content did not enter the walk (a failed
        // import / unresolved SDK — see [`is_structural_compile_risk`]), in an
        // SDK file as anywhere ([`State::mark_structural_skip`] says why).
        // Everything else (an undefined property or skipped `<Target>` in an
        // SDK file) leaves the Compile set intact, even though it still flips
        // `is_partial`.
        // A structural kind means a file's worth of content did not enter
        // the walk — after it, an undefined read could be of a name that
        // hidden content defined (see [`State::walk_opaque`]).
        if is_structural_compile_risk(&kind) {
            self.latch_walk_opaque(
                OpacityCause::Unentered(format!("{kind:?}").into()),
                span.clone(),
            );
        }
        let compile_uncertain =
            self.compile_context || self.import_gate_context || is_structural_compile_risk(&kind);
        if compile_uncertain {
            self.items_uncertain = true;
        }
        // The preprocessor-symbol analogue: uncertainty while resolving a user
        // `<DefineConstants>` write (or its gating condition) means the `#if`
        // symbol set may be wrong. `define_context` is only set outside the SDK
        // tree, so no further provenance check. The one exception is the
        // `$(DefineConstants);FOO` append idiom's own read, which the caller
        // names. (Hidden content withdraws the set where it is latched,
        // [`Self::latch_walk_opaque`].)
        let define_uncertain = self.define_context && define_axis == DefineAxis::Doubts;
        if define_uncertain {
            self.define_constants_uncertain = true;
        }
        // The package-set analogue of the Compile rule above, with the same
        // shape: a diagnostic raised while resolving a package/framework
        // reference or its gating group (`package_context`) makes the set
        // untrustworthy, and so does a structural construct that can *carry*
        // such references — an unresolved/failed import or missing SDK —
        // anywhere (`is_structural_compile_risk` names Compile but the same
        // imports can hold `<PackageReference>` items). Unlike Compile
        // uncertainty, package structural risk is not SDK-gated: SDK imports
        // are a normal source of implicit dependency items.
        let package_uncertain = self.package_context
            || self.package_import_gate_context
            || is_structural_compile_risk(&kind);
        if package_uncertain {
            self.package_references_uncertain = true;
        }
        // The reference-list analogue of the Compile rule's import half: a
        // failed or unfollowable import, or one whose gate we could not
        // decide, may carry `<ProjectReference>` mutations we never saw, so the
        // captured list may claim references the real build strips. In an SDK
        // file as anywhere: the file such an import names may be a user's, or
        // import one (#848).
        if self.import_gate_context || is_structural_compile_risk(&kind) {
            self.project_references_uncertain = true;
        }
        let origin = self.current_origin();
        let span = self.effective_span(span);
        if compile_uncertain {
            self.compile_item_uncertainties
                .push(CompileItemUncertaintyCause {
                    kind: CompileItemUncertaintyCauseKind::Diagnostic(kind.clone()),
                    span: span.clone(),
                    origin: origin.clone(),
                });
        }
        if package_uncertain {
            self.package_reference_uncertainties
                .push(PackageReferenceUncertaintyCause {
                    kind: PackageReferenceUncertaintyCauseKind::Diagnostic(kind.clone()),
                    span: span.clone(),
                    origin: origin.clone(),
                });
        }
        if define_uncertain {
            self.define_constants_uncertainties
                .push(DefineConstantsUncertaintyCause {
                    kind: DefineConstantsUncertaintyCauseKind::Diagnostic(kind.clone()),
                    span: span.clone(),
                    origin: origin.clone(),
                });
        }
        self.diagnostics.push(Diagnostic { kind, span, origin });
        if let Some((project, reason, span, certainty)) = failed_import {
            self.note_rejection(
                certainty,
                crate::RejectionCause::Import {
                    project,
                    gate_undecided: false,
                    why: crate::UnloadableImport::Failed(reason),
                },
                span,
            );
        }
    }

    /// The [`DiagnosticOrigin`] for a construct reached at the current walk
    /// position: `Imported` iff we're inside an imported file (the same
    /// `import_site_span` test [`Self::push`] uses).
    fn current_origin(&self) -> DiagnosticOrigin {
        if self.import_site_span.is_some() {
            DiagnosticOrigin::Imported
        } else {
            DiagnosticOrigin::Buffer
        }
    }

    /// Record a [`CompileConditionUncertainty`] for a Compile item/group whose
    /// `Condition` we couldn't trust. Span/origin follow the same remap rules
    /// as [`Self::push`]. Callers gate on [`Self::compile_context`].
    fn record_compile_condition_uncertainty(
        &mut self,
        condition: &str,
        reason: CompileConditionReason,
        span: Range<usize>,
    ) {
        let origin = self.current_origin();
        let span = self.effective_span(span);
        self.compile_condition_uncertainties
            .push(CompileConditionUncertainty {
                condition: condition.to_string(),
                reason,
                span,
                origin,
            });
    }

    fn record_compile_item_uncertainty(
        &mut self,
        kind: CompileItemUncertaintyCauseKind,
        span: Range<usize>,
    ) {
        let origin = self.current_origin();
        let span = self.effective_span(span);
        self.compile_item_uncertainties
            .push(CompileItemUncertaintyCause { kind, span, origin });
    }

    /// Attribute every package-set cause recorded since index `from` to the
    /// `owner` list ([`Self::package_cause_owners`]).
    #[cfg(any(test, feature = "test-support"))]
    fn attribute_package_causes(&mut self, from: usize, owner: item_pass::PackageItemKind) {
        let to = self.package_reference_uncertainties.len();
        self.package_cause_owners
            .extend((from..to).map(|index| (index, owner)));
    }

    fn record_package_reference_uncertainty(
        &mut self,
        kind: PackageReferenceUncertaintyCauseKind,
        span: Range<usize>,
    ) {
        let origin = self.current_origin();
        let span = self.effective_span(span);
        self.package_reference_uncertainties
            .push(PackageReferenceUncertaintyCause { kind, span, origin });
    }

    fn taint_item_list(&mut self, item_type: &str) {
        self.tainted_item_lists.insert(item_key(item_type));
    }

    fn invalidate_item_list(&mut self, item_type: &str) {
        let key = item_key(item_type);
        self.evaluated_items.remove(&key);
        self.tainted_item_lists.insert(key);
    }

    fn mark_untracked_item_list(&mut self, item_type: &str) {
        self.untracked_item_lists.insert(item_key(item_type));
    }

    fn record_helper_item_definition_default(&mut self, item_type: &str, metadata_name: &str) {
        self.helper_item_definition_defaults
            .entry(item_key(item_type))
            .or_default()
            .entry(item_key(metadata_name))
            .or_insert_with(|| HelperMetadataUncertainty::item_definition_default(metadata_name));
    }

    /// What the walk knows about `name`'s stored value, bound or not: the
    /// trust its entry in [`Self::lookup`] carries.
    fn trust_of(&self, name: &str) -> &Trust {
        self.lookup.trust(name)
    }

    /// The trust a *value* inherits from the properties it references: the
    /// join over every `$(…)` in `raw`, in source order.
    ///
    /// One scan serves every channel. Reading the channels separately would
    /// mean one scan per channel, and a scan that quietly covered two of the
    /// three would look exactly like this one at the call site.
    fn trust_for_raw(&self, raw: &str) -> Trust {
        Trust::join_all(properties::property_references(raw).map(|name| self.trust_of(name)))
    }

    fn sdk_package_property_is_tainted(&self, name: &str) -> bool {
        self.trust_of(name).sdk_package().is_some()
    }

    /// A write's verdict with its taint span resolved — remapped to the entry
    /// file and stamped with the current origin — because that is walk state
    /// the write sites don't carry.
    fn resolve_provenance(&self, provenance: PropertyProvenance) -> ResolvedProvenance {
        provenance.map_taint(|span| SdkPackagePropertyTaint {
            span: self.effective_span(span),
            origin: self.current_origin(),
        })
    }

    /// Apply a [`PropertyProvenance`] verdict to all three channels of
    /// `name`'s entry, leaving its value alone: a write that did not store a
    /// value (skipped under a gate, or refused after [`PropertyMap::unbind`]).
    /// A write that stores one goes through [`Self::write_property`].
    fn apply_property_provenance(&mut self, name: &str, provenance: PropertyProvenance) {
        if matches!(provenance.refused, RefusedOutcome::Set) {
            self.rewritten_after_refusal
                .remove(&name.to_ascii_lowercase());
        }
        // A write that stored nothing holds a value only if it may have
        // happened: one under a gate that decided against it holds none.
        if provenance.is_doubtful() {
            self.note_foreign_write(name, None);
        }
        self.directory_build.note_write(name);
        let resolved = self.resolve_provenance(provenance);
        self.lookup.apply_provenance(name, resolved);
    }

    /// Store an evaluated write's value and its verdict together, so a value
    /// cannot enter the table without the write saying what it does to the
    /// name's trust.
    fn write_property(&mut self, name: &str, value: Escaped, provenance: PropertyProvenance) {
        let second_walk = self.second_walk;
        crate::cost::count(|costs| {
            if second_walk {
                costs.second_walk_property_writes += 1;
            } else {
                costs.property_writes += 1;
            }
        });
        let held = (!provenance.is_doubtful()).then_some(&value);
        self.note_foreign_write(name, held);
        self.directory_build.note_write(name);
        let resolved = self.resolve_provenance(provenance);
        self.lookup.write(name, value, resolved);
    }

    /// Check a write of `name` made in a document outside the install against
    /// the grammar the compiled-name derivation holds the name to
    /// ([`crate::fsc::grammar_of`]): the value it stored, or `None` when the
    /// walk is not certain of it. Only the first failure of each name is kept,
    /// and names the derivation does not admit are not looked at, so the record
    /// stays as small as the lists however often a document writes.
    fn note_foreign_write(&mut self, name: &str, value: Option<&Escaped>) {
        if !self.in_foreign_document {
            return;
        }
        let Some(grammar) = crate::fsc::grammar_of(name) else {
            return;
        };
        let lower = name.to_ascii_lowercase();
        if self.foreign_write_failures.contains_key(&lower) {
            return;
        }
        let value = value.map(Escaped::unescape);
        if !value.as_deref().is_some_and(|v| grammar.admits(v)) {
            self.foreign_write_failures.insert(lower, value);
        }
    }

    fn sdk_package_taint_for_raw(&self, raw: &str) -> Option<SdkPackagePropertyTaint> {
        self.trust_for_raw(raw).sdk_package().cloned()
    }

    fn raw_uses_sdk_package_taint(&self, raw: &str) -> bool {
        self.sdk_package_taint_for_raw(raw).is_some()
    }

    /// The way the gate `condition` of a reference, its group or an arm of a
    /// `<Choose>` around it decides whatever the names the walk doubts hold
    /// (the reference gates' policy: unpinned or SDK-tainted, held as no value
    /// it can show undefined, or written on the path the judgement walks), on
    /// the values it holds, three-valued (`condition::decide_without`), `Exists`
    /// resolved against `dir`, or, with none, probing nothing (an `Exists` leaf
    /// then decides nothing): a gate MSBuild may not evaluate (a `<When>` after
    /// one it takes) is decided with none, so the read set gains no probe
    /// MSBuild does not make. A refusal a clean write overwrote leaves the
    /// bound value deciding, as it does not for an import point
    /// ([`directory_build::decision_from_certain_inputs`]). Once the walk has
    /// hidden content, a doubted name it reads settles nothing
    /// ([`Self::condition_is_decided_exactly`] says why).
    fn reference_gate_decision(&self, condition: &str, dir: Option<&Path>) -> Option<bool> {
        let unknown = |name: &str| {
            self.trust_of(name).reference_is_untrusted()
                || (!self.lookup.is_bound(name) && !self.undefined_read_is_exact(name))
                || self.speculatively_unheld(name)
        };
        if self.walk_opaque.is_some() && properties::property_references(condition).any(unknown) {
            return None;
        }
        let observer = self.observer;
        let exists = dir.map(|dir| move |path: &str| condition_exists(observer, path, dir));
        let probes = match (&exists, self.follow_imports) {
            (Some(exists), true) => Some(condition::Probes { exists, observer }),
            _ => None,
        };
        match condition::decide_without(
            condition,
            &self.lookup,
            probes,
            self.condition_site(),
            &unknown,
        ) {
            condition::Decision::Decided(value) => Some(value),
            _ => None,
        }
    }

    /// Whether `raw` reads a name whose value the real build may hold
    /// otherwise than the walk: one it holds and doubts (unpinned or
    /// SDK-tainted, [`Trust::reference_is_untrusted`]), or one it holds no
    /// value of and cannot show undefined (a write it refused to compute,
    /// [`Self::undefined_read_is_exact`]). Read off the text of an item's
    /// spec ([`properties::item_spec_references`]), so that what the
    /// expansion did with the name (stop at a function it does not model,
    /// say) cannot hide the read, with the names a function reads without
    /// naming them ([`condition::implicit_references`]).
    fn raw_reads_a_doubted_name(&self, raw: &str) -> bool {
        let doubted = |name: &str| {
            self.trust_of(name).reference_is_untrusted()
                || (!self.lookup.is_bound(name) && !self.undefined_read_is_exact(name))
        };
        let mut implicit = Vec::new();
        condition::implicit_references(raw, &mut implicit);
        properties::item_spec_references(raw).any(doubted)
            || implicit.iter().any(|name| doubted(name))
    }

    /// The root to record for a value that read `name` while it was
    /// undefined: "read `name` while undefined", explained by why, taken at
    /// the read — `name`'s own root when the walk has one (its write was
    /// skipped under a gate we could not decide, say), else the opacity that
    /// hides a possible write. Taken now, so a later write to `name` cannot
    /// rewrite what this value rests on; flattened, so reporting needs no
    /// chase.
    fn root_for_undefined_read(&self, name: &str) -> UnpinnedRoot {
        let because = match self.trust_of(name).unpinned() {
            Some(own) => Some(own.undefined_because()),
            // Opacity explains the read only when nothing else would have
            // made it inexact: a refused or environment name has its own story.
            None => self
                .walk_opaque
                .as_ref()
                .filter(|_| self.undefined_read_is_exact_but_for_opacity(name))
                .map(|cause| UndefinedBecause::Opacity(cause.clone())),
        };
        UnpinnedRoot::undefined(name, because)
    }

    /// Latch [`Self::walk_opaque`], keeping the first cause.
    ///
    /// Every latch, not only the first, also marks each value bound now stale
    /// ([`Trust::stale`]): the content just passed may have rewritten it. A
    /// reserved name cannot be rewritten by any file, so it does not go stale;
    /// a caller global can, by a file that names it in its project's
    /// `TreatAsLocalProperty` (#1037).
    ///
    /// The first latch also withdraws the define set, in an SDK file as
    /// anywhere, recording the construct at `span` as the cause
    /// ([`DefineConstantsUncertaintyCauseKind::HiddenContent`] says why).
    fn latch_walk_opaque(&mut self, cause: OpacityCause, span: Range<usize>) {
        self.lookup
            .go_stale(&std::sync::Arc::new(cause.clone()), &self.reserved);
        if self.walk_opaque.is_none() {
            self.define_constants_uncertain = true;
            self.define_constants_uncertainties
                .push(DefineConstantsUncertaintyCause {
                    kind: DefineConstantsUncertaintyCauseKind::HiddenContent(
                        crate::UntrustedCause::of_opacity(&cause),
                    ),
                    span: self.effective_span(span),
                    origin: self.current_origin(),
                });
            self.walk_opaque = Some(cause);
        }
        // Content the walk could not see may hold the root that settles
        // `MSBuildProjectDefaultTargets` ([`latch_default_targets`]): an offer
        // still open settles with the property unset.
        if !self.default_targets_decided {
            self.default_targets_decided = true;
            self.lookup.unbind("MSBuildProjectDefaultTargets");
        }
    }

    /// The opacity behind `node`'s gate where the walk did not decide it from
    /// certain inputs (`decided` false) and it reads a value content the walk
    /// could not see may have rewritten ([`Trust::stale`]). Such a gate raises
    /// no diagnostic, unlike one reading an undefined or unpinned name, and may
    /// go the other way in the real build (#1037).
    fn stale_gate_cause(
        &self,
        node: Node<'_, '_>,
        decided: bool,
    ) -> Option<properties::trust::StaleCause> {
        if decided {
            return None;
        }
        let condition = attribute(node, "Condition")?;
        self.trust_for_raw(&condition).stale().cloned()
    }

    /// Mark `name` stale under `cause`: the walk skipped a write to it on a
    /// stale gate, which the real build may have run. A name the frame
    /// protects is one the real build's write would leave alone, and one the
    /// walk holds unbound needs no mark ([`Self::skipped_write_needs_mark`]).
    fn mark_skipped_write_stale(&mut self, name: &str, cause: &properties::trust::StaleCause) {
        if self.protected.contains(&name.to_ascii_lowercase())
            || !self.skipped_write_needs_mark(name)
        {
            return;
        }
        self.apply_property_provenance(
            name,
            PropertyProvenance {
                taint: TaintOutcome::Keep,
                unpinned: UnpinnedOutcome::Keep,
                refused: RefusedOutcome::Keep,
                stale: StaleOutcome::Set(cause.clone()),
            },
        );
    }

    /// Whether a write to `name` the walk skipped on a stale gate leaves a
    /// value the walk would otherwise commit. One the walk holds unbound reads
    /// as an inexact unset already: a stale gate exists only once the walk has
    /// passed content it could not see, after which no undefined read is exact
    /// ([`Self::undefined_read_is_exact`]).
    fn skipped_write_needs_mark(&self, name: &str) -> bool {
        debug_assert!(
            self.walk_opaque.is_some(),
            "a stale gate exists only after a latch"
        );
        self.lookup.is_bound(name)
    }

    /// Every property MSBuild may write in one of `branches`, alternatives of
    /// which it takes at most one (the `<When>`s and `<Otherwise>` of a
    /// `<Choose>` it may take instead of the walk's). Each is judged from the
    /// state before any of them, in its own order, its marks undone before
    /// the next; the table is as it was when this returns.
    fn skipped_branch_writes(
        &mut self,
        branches: &[Node<'_, '_>],
        current_file_dir: &Path,
        cause: &properties::trust::StaleCause,
    ) -> Vec<String> {
        let mut written = Vec::new();
        for branch in branches {
            let mut undo = HashMap::new();
            self.mark_skipped_branch_stale(
                *branch,
                current_file_dir,
                cause,
                &mut written,
                &mut undo,
            );
            for (name, trust) in undo {
                self.lookup.restore_trust(&name, trust);
            }
        }
        // Each name once, though several alternatives may write it.
        let mut seen = HashSet::new();
        written.retain(|name| seen.insert(name.to_ascii_lowercase()));
        written
    }

    /// [`Self::mark_skipped_write_stale`] for every property `branch` (a
    /// `<When>` or `<Otherwise>`) may write, in order, recording each in
    /// `written`, and each name's trust before its first mark in `undo`
    /// (`None` where it had no entry): all but those a gate decided
    /// from certain inputs rules out, the write's own or its group's
    /// (`current_file_dir` resolving the group's `Exists`), and those in a
    /// nested `<Choose>`'s branches MSBuild cannot take.
    fn mark_skipped_branch_stale(
        &mut self,
        branch: Node<'_, '_>,
        current_file_dir: &Path,
        cause: &properties::trust::StaleCause,
        written: &mut Vec<String>,
        undo: &mut HashMap<String, Option<Trust>>,
    ) {
        // A name is marked once per branch: a second mark changes nothing.
        let mut mark = |state: &mut Self, name: String| {
            let std::collections::hash_map::Entry::Vacant(slot) =
                undo.entry(name.to_ascii_lowercase())
            else {
                return;
            };
            slot.insert(state.lookup.entry_trust(&name));
            state.mark_skipped_write_stale(&name, cause);
            written.push(name);
        };
        for child in branch.children().filter(Node::is_element) {
            match child.tag_name().name() {
                "PropertyGroup" if !self.ruled_out(child, current_file_dir) => {
                    // One at a time: a write may enable a later one's gate.
                    for property in child.children().filter(Node::is_element) {
                        if property_child_could_write(property, self) {
                            mark(self, property.tag_name().name().to_owned());
                        }
                    }
                }
                "Choose" => {
                    let nested = self.choose_branches_from(child, 0, None);
                    for name in self.skipped_branch_writes(&nested, current_file_dir, cause) {
                        mark(self, name);
                    }
                }
                _ => {}
            }
        }
    }

    /// The branches of `choose` MSBuild may take, from its `first` `<When>`
    /// on, but `walked` (the walk's, by index; the `<Otherwise>` is index
    /// `whens.len()`): each whose gate does not fail whatever the uncertain
    /// names hold, up to the first whose gate holds whatever they hold, and
    /// the `<Otherwise>` only if none does.
    fn choose_branches_from<'a, 'input>(
        &self,
        choose: Node<'a, 'input>,
        first: usize,
        walked: Option<usize>,
    ) -> Vec<Node<'a, 'input>> {
        let entry_dir = self.entry_project_dir.clone();
        let mut branches = Vec::new();
        let whens = choose
            .children()
            .filter(|child| child.is_element() && child.tag_name().name() == "When");
        let mut count = 0;
        for (index, when) in whens.enumerate() {
            count = index + 1;
            if index < first {
                continue;
            }
            let decision = attribute(when, "Condition").and_then(|condition| {
                directory_build::decision_from_certain_inputs(self, &condition, &entry_dir)
            });
            if decision == Some(false) {
                continue;
            }
            if walked != Some(index) {
                branches.push(when);
            }
            if decision == Some(true) {
                return branches;
            }
        }
        if walked != Some(count) {
            branches.extend(
                choose
                    .children()
                    .find(|child| child.is_element() && child.tag_name().name() == "Otherwise"),
            );
        }
        branches
    }

    /// Whether `node`'s gate is false whatever the names the walk is not
    /// certain of hold, `dir` resolving its `Exists`.
    fn ruled_out(&self, node: Node<'_, '_>, dir: &Path) -> bool {
        attribute(node, "Condition").is_some_and(|condition| {
            directory_build::decision_from_certain_inputs(self, &condition, dir) == Some(false)
        })
    }

    /// Latch the walk opaque for an import gate it could not decide, and
    /// return why the gate is undecided: the root its evaluation just
    /// surfaced, else the gate itself.
    fn latch_undecided_import_gate(
        &mut self,
        node: Node<'_, '_>,
        diagnostics_before: usize,
    ) -> UnpinnedRoot {
        let root = self
            .unpinned_root_from_recent_diagnostics(diagnostics_before)
            .unwrap_or_else(|| {
                UnpinnedRoot::UnsupportedCondition(
                    attribute(node, "Condition")
                        .unwrap_or_default()
                        .as_ref()
                        .into(),
                )
            });
        self.latch_walk_opaque(OpacityCause::Gate(root.clone()), node.range());
        root
    }

    /// The root cause behind the first unpinned property `raw` references,
    /// if any (see [`Trust::unpinned`]).
    fn unpinned_root_for_raw(&self, raw: &str) -> Option<UnpinnedRoot> {
        self.trust_for_raw(raw).unpinned().cloned()
    }

    /// The [`ParsedProject::target_name`] verdict: the output file's base
    /// name is `$(TargetName)`, defaulting to `$(AssemblyName)` (the common
    /// targets' `<TargetName Condition="'$(TargetName)' == ''">` write —
    /// probed, dotnet 10.0.301: an explicit `TargetName` beats
    /// `AssemblyName` in the output filename). Each candidate in turn:
    /// untrusted provenance, a value the real build holds and the walk does
    /// not (a refused write, or an environment name it could not promote),
    /// or residual `$(...)` decides `Unknown` (a consumer locating an output
    /// DLL by a wrong name fabricates);
    /// whitespace-only is `Unknown` too (MSBuild preserves padding in the
    /// filename — probed, ` Padded .dll` — but the default gate compares
    /// `== ''` exactly, so a whitespace-only spelling names the output
    /// file something we refuse to guess); a clean non-empty value wins
    /// **verbatim** (never trimmed); empty/unset falls to the next
    /// candidate. Neither set is `Known(None)`: MSBuild's default
    /// (`$(MSBuildProjectName)`, the project-file stem) applies.
    fn target_name_verdict(&self) -> ItemMetadataValue {
        for name in ["TargetName", "AssemblyName"] {
            match self.read_property(name) {
                // A value held from before content the walk could not see
                // reads as untrusted, and that content may define a name the
                // walk holds unset.
                PropertyRead::Untrusted(_) | PropertyRead::UnsetInexact(_) => {
                    return ItemMetadataValue::Unknown;
                }
                PropertyRead::Value(_) | PropertyRead::Unset => {}
            }
            // The entry's trust is the question just asked.
            match self.lookup.get_ignoring_trust(name) {
                None => continue,
                Some(v) if v.is_empty() => continue,
                Some(v) if v.as_escaped().contains("$(") => return ItemMetadataValue::Unknown,
                Some(v) if v.unescape().trim().is_empty() => return ItemMetadataValue::Unknown,
                Some(v) => return ItemMetadataValue::known(v.unescape()),
            }
        }
        ItemMetadataValue::Known(None)
    }

    /// Whether a node's `Condition` leans on a value that may differ in a
    /// real build — an *unpinned* property (written under a gate we couldn't
    /// evaluate) or an SDK-package-tainted one — making even a cleanly
    /// decided True/False an untrustworthy branch decision. Undefined,
    /// never-written properties are deliberately NOT untrusted: under the
    /// walker's environment model (caller `extra_properties` ARE the
    /// environment) they are genuinely unset, so treating them as empty is
    /// exact — the same commitment the default-fill exemption and the
    /// pinned `'$(NoSuchProp)' == 'on'` reference-mutation cases make.
    ///
    /// "Leans on" is about the *outcome*: see [`Self::condition_trust`].
    ///
    /// A name whose write the walk refused, and which no later write bound,
    /// reads as undefined here, but the real build holds the value it
    /// computed, so a condition that rests on one leans on a value that may
    /// differ too (#780). A refused name a later clean write bound holds a
    /// value computed exactly (the mark outlives the overwrite for the import
    /// points alone; [`Trust::refused`]).
    fn condition_reads_untrusted_value(&self, node: Node<'_, '_>) -> bool {
        attribute(node, "Condition").as_deref().is_some_and(|cond| {
            if self.condition_trust(cond, None).reference_is_untrusted() {
                return true;
            }
            !self.condition_is_decided_exactly(cond, None, &|name| {
                self.undefined_read_is_exact(name)
            }) && properties::property_references(cond)
                .any(|name| !self.lookup.is_bound(name) && self.trust_of(name).refused())
        })
    }

    /// The trust a condition's *decision* carries: certain when the values the
    /// walk holds exactly decide it ([`Self::condition_is_decided_exactly`]),
    /// else the join of the trusts of every property it mentions.
    ///
    /// A condition is a function of the properties it reads, and only the ones
    /// its outcome depends on can move it. The SDK's
    /// `'$(EnablePreviewFeatures)' == 'true' And '$(IsNetCoreAppTargetingLatestTFM)' == 'true'`
    /// is false while `EnablePreviewFeatures` is unset, whatever an untrusted
    /// `TargetFramework` makes of the other operand — so the `LangVersion`
    /// write it guards cannot run, and must not be marked as if it might.
    ///
    /// `exists_dir` is the directory `Exists('…')` resolves against, `None`
    /// where the caller evaluated without a filesystem: an `Exists` leaf is
    /// then outside the grammar, which leaves the decision undecided.
    fn condition_trust(&self, cond: &str, exists_dir: Option<&Path>) -> Trust {
        if self.condition_is_decided_exactly(cond, exists_dir, &|name| {
            self.undefined_read_is_exact(name)
        }) {
            Trust::of_exact_decision()
        } else {
            self.trust_for_raw(cond)
        }
    }

    /// Whether `cond`'s outcome is fixed by values the walk holds exactly: no
    /// property it mentions is unknown, or the known ones decide it alone
    /// ([`condition::decide_without`]).
    ///
    /// A name is unknown when its reference is untrusted, or when it is
    /// undefined to us and `exact_undefined` cannot vouch that it is undefined
    /// to the real build too. That is judged for **every** name the condition
    /// mentions, not only the ones a short-circuiting evaluation happened to
    /// visit: the real build may reach an operand ours skipped.
    fn condition_is_decided_exactly(
        &self,
        cond: &str,
        exists_dir: Option<&Path>,
        exact_undefined: &dyn Fn(&str) -> bool,
    ) -> bool {
        let unknown = |name: &str| {
            self.trust_of(name).reference_is_untrusted()
                || (!self.lookup.is_bound(name) && !exact_undefined(name))
        };
        if !properties::property_references(cond).any(&unknown) {
            return true;
        }
        // Once the walk has passed content it could not see, any value it holds
        // may have been rewritten there. Such a value is trusted when a
        // condition reads nothing worse (a deliberate trade-off — see
        // [`Trust::stale`]), but it cannot be the operand that settles an
        // unknown one: that would decide a branch the base rule leaves open.
        // Telling a rewritable value from a current one is what
        // [`Trust::stale`] records; this decision does not consume it,
        // so nothing settles an unknown operand after opacity. Measured on the
        // corpus, this keeps every decline the decision recovers.
        if self.walk_opaque.is_some() {
            return false;
        }
        let observer = self.observer;
        let exists = exists_dir.map(|dir| move |path: &str| condition_exists(observer, path, dir));
        let probes = match (&exists, self.follow_imports) {
            (Some(exists), true) => Some(condition::Probes { exists, observer }),
            _ => None,
        };
        matches!(
            condition::decide_without(cond, &self.lookup, probes, self.condition_site(), &unknown),
            condition::Decision::Decided(_)
        )
    }

    /// The [`UnpinnedRoot`] to record for a write gated on a condition the
    /// property pass could not pin down: the root cause the condition's
    /// evaluation just surfaced as diagnostics (scanned from
    /// `diagnostics[since..]`), preferring an undefined property name over
    /// an unsupported-condition report.
    fn unpinned_root_from_recent_diagnostics(&self, since: usize) -> Option<UnpinnedRoot> {
        let recent = || self.diagnostics.iter().enumerate().skip(since);
        let (index, diagnostic) = recent()
            .find(|(_, d)| matches!(d.kind, DiagnosticKind::UndefinedProperty { .. }))
            .or_else(|| {
                recent()
                    .find(|(_, d)| matches!(d.kind, DiagnosticKind::UnsupportedCondition { .. }))
            })?;
        Some(
            match (self.diagnostic_roots.get(&index), &diagnostic.kind) {
                (Some(root), _) => root.clone(),
                // Not pushed as a root: a read made now, so `name`'s current root
                // is the one in force.
                (None, DiagnosticKind::UndefinedProperty { name }) => {
                    self.root_for_undefined_read(name)
                }
                (None, DiagnosticKind::UnsupportedCondition { condition }) => {
                    UnpinnedRoot::UnsupportedCondition(condition.as_str().into())
                }
                (None, _) => unreachable!("only the two kinds are selected above"),
            },
        )
    }

    /// Surface `root` as its diagnostic, remembering the root itself.
    fn push_root(&mut self, root: UnpinnedRoot, span: Range<usize>) {
        let index = self.diagnostics.len();
        self.push(root.to_diagnostic(), span);
        self.diagnostic_roots.insert(index, root);
    }

    /// Surface a read of `name` while undefined, remembering the root in force
    /// now. Says what the diagnostic did to the define axis.
    fn push_undefined_read(&mut self, name: String, span: Range<usize>) -> DefineAxis {
        let root = self.root_for_undefined_read(&name);
        let index = self.diagnostics.len();
        // A `<DefineConstants>` value reading `$(DefineConstants)` itself is
        // the append idiom ([`is_define_self_reference`]). The exemption is
        // decided here, on the name this read substituted, and nowhere else:
        // a root re-surfaced from another property ([`Self::push_root`]) is one
        // witness of that value's doubt, and an independent cause may have
        // lost the race to be it. It holds only while the read is undefined
        // for want of the SDK's own defines alone
        // ([`Self::self_append_reads_the_sdk_free_view`]).
        let define_axis = if self.in_define_value
            && is_define_self_reference(&name)
            && self.self_append_reads_the_sdk_free_view()
        {
            DefineAxis::SelfAppend
        } else {
            DefineAxis::Doubts
        };
        self.push_on_define_axis(
            DiagnosticKind::UndefinedProperty { name },
            span,
            define_axis,
        );
        self.diagnostic_roots.insert(index, root);
        define_axis
    }

    /// Whether an undefined `$(DefineConstants)` read is undefined only in
    /// the view the define set is published in: the project's own, without
    /// the defines the SDK adds ([`crate::ParsedProject::define_constants_uncertain`]).
    /// Not once the walk has passed content it did not see, which may have
    /// written it (#843), nor when the environment names it in spellings
    /// promotion skipped, where MSBuild holds one of their values. A write the
    /// walk refused does not end the view: in a user's file that write raised
    /// the flag itself, and in an SDK file it is the SDK's own define.
    fn self_append_reads_the_sdk_free_view(&self) -> bool {
        self.walk_opaque.is_none() && !self.env_property_names.contains("defineconstants")
    }

    fn note_package_uncertain_from_sdk_property_taint(&mut self, raw: &str) {
        let Some(taint) = self.sdk_package_taint_for_raw(raw) else {
            return;
        };
        self.package_references_uncertain = true;
        self.package_reference_uncertainties
            .push(PackageReferenceUncertaintyCause {
                kind: PackageReferenceUncertaintyCauseKind::SdkDependencyItemPropertyEvaluation,
                span: taint.span,
                origin: taint.origin,
            });
    }

    fn note_package_uncertain_if_condition_uses_sdk_taint(&mut self, node: Node<'_, '_>) {
        if let Some(condition) = attribute(node, "Condition").as_deref() {
            self.note_package_uncertain_from_sdk_property_taint(condition);
        }
    }

    /// Override `span` with `import_site_span` if we're currently
    /// walking an imported file. Callers pass `node.range()` from
    /// whatever XML buffer they're walking; while inside an external
    /// file those offsets are not valid for the entry-project source
    /// the caller will eventually consult — see [`Self::import_site_span`].
    fn effective_span(&self, span: Range<usize>) -> Range<usize> {
        self.import_site_span.clone().unwrap_or(span)
    }

    /// Substitute `$(...)` in `raw` and push any issues as diagnostics
    /// attributed to `span`. The returned [`Expansion`] separates
    /// undefined-reference issues (safe — value is empty but well-formed)
    /// from unsupported-expression issues (unsafe — value contains
    /// residual `$(...)` literal text) so callers can take different
    /// actions for each.
    fn expand(&mut self, raw: &str, span: Range<usize>) -> Expansion {
        self.expand_inner(raw, span, None)
    }

    /// Expand a property-pass value.
    /// `writing_property` is the destination name: an unpinned
    /// self-reference (the `$(OtherFlags) --flag` accumulator idiom) still
    /// propagates the pin state but is not re-surfaced as a diagnostic —
    /// the root was already reported when the property first became
    /// unpinned, and each append hop adds no new information.
    fn expand_property_pass_value(
        &mut self,
        raw: &str,
        span: Range<usize>,
        writing_property: &str,
    ) -> Expansion {
        self.expand_inner(raw, span, Some(writing_property))
    }

    fn expand_inner(
        &mut self,
        raw: &str,
        span: Range<usize>,
        writing_property: Option<&str>,
    ) -> Expansion {
        // FS-probing property functions are with-imports-only; the pure
        // surface documents "no filesystem access".
        let (value, issues) = if self.follow_imports {
            properties::substitute_with_fs(raw, &self.lookup, self.observer)
        } else {
            properties::substitute(raw, &self.lookup)
        };
        let mut had_undefined = false;
        let mut had_unsupported = false;
        let throws = rejection::throws_in(&issues);
        let mut direct_undefined: Vec<String> = Vec::new();
        // The direct reads whose diagnostic doubted on every axis: the self-
        // append's own read did not doubt the define axis, so a root naming
        // `DefineConstants` is not already reported by it.
        let mut direct_doubted: Vec<String> = Vec::new();
        for issue in issues {
            let kind = match issue {
                Issue::Undefined { name } => {
                    // An undefined read the walk can prove is undefined
                    // in the real build too is *exactly* the empty
                    // string MSBuild substitutes — not a divergence, so
                    // no diagnostic and no unpinning (C.2b).
                    if self.undefined_read_is_exact(&name) {
                        continue;
                    }
                    had_undefined = true;
                    direct_undefined.push(name.clone());
                    if self.push_undefined_read(name.clone(), span.clone()) == DefineAxis::Doubts {
                        direct_doubted.push(name);
                    }
                    continue;
                }
                Issue::Unsupported { expression }
                | Issue::ReturnsBoolean { expression }
                | Issue::ReturnsValue { expression }
                | Issue::Throws { expression, .. } => {
                    had_unsupported = true;
                    DiagnosticKind::UnsupportedPropertyExpression { expression }
                }
                Issue::PathAdjustmentUndecided { value } => {
                    had_unsupported = true;
                    DiagnosticKind::PathAdjustmentUndecided { value }
                }
            };
            self.push(kind, span.clone());
        }
        // A reference to an *unpinned* property (its stored value leaned on
        // an undefined name or an unevaluable gate — see [`Trust::unpinned`])
        // carries the same divergence risk as a direct undefined reference,
        // but plain substitution cannot see it: the property IS defined.
        // Re-surface each root here so every read — property-pass or
        // item-pass — reports it under the active contexts, exactly like the
        // direct case.
        let mut unpinned_root = direct_undefined
            .first()
            .map(|name| self.root_for_undefined_read(name));
        let mut surfaced: Vec<UnpinnedRoot> = Vec::new();
        for reference in properties::property_references(raw) {
            let Some(root) = self.trust_of(reference).unpinned().cloned() else {
                continue;
            };
            if unpinned_root.is_none() {
                unpinned_root = Some(root.clone());
            }
            if writing_property.is_some_and(|dest| dest.eq_ignore_ascii_case(reference)) {
                // Self-append accumulator idiom: propagate the pin state
                // (done just above) without re-reporting the root at every
                // hop.
                continue;
            }
            if let Some(name) = root.undefined_name()
                && direct_doubted.iter().any(|n| n.eq_ignore_ascii_case(name))
            {
                // The same diagnostic already surfaced as a direct issue above.
                continue;
            }
            if surfaced
                .iter()
                .any(|seen| seen.to_diagnostic() == root.to_diagnostic())
            {
                continue;
            }
            self.push_root(root.clone(), span.clone());
            surfaced.push(root);
        }
        self.assert_scan_holds_the_reads(
            raw,
            value.trust(),
            unpinned_root.as_ref(),
            had_unsupported,
        );
        // A value deciding the Compile set that rests on one hidden content may
        // have rewritten ([`Trust::stale`]) leaves the set uncertain, as an
        // unpinned read would. Measured at zero cost on the crate suite, the F#
        // corpus and the LSP project corpus.
        if self.compile_context
            && let Some(stale) = value.trust().stale()
        {
            self.items_uncertain = true;
            self.record_compile_item_uncertainty(
                CompileItemUncertaintyCauseKind::StaleValue {
                    reference: raw.to_string(),
                    hidden_by: crate::UntrustedCause::of_opacity(stale),
                },
                span,
            );
        }
        Expansion {
            value,
            had_undefined,
            had_unsupported,
            unpinned_root,
            throws,
        }
    }

    /// The checked mirror between the two ways the walk knows what a value
    /// rests on: the *scan* of its text ([`properties::property_references`]),
    /// which every write verdict is computed from, and the *reads* its
    /// expansion actually made, whose trust the value carries. The scan must
    /// hold every doubt the reads carried — an unpinned or SDK-tainted read
    /// the scan missed is a value whose verdict claims more than its inputs
    /// allow (P0 property A of `docs/msbuild-value-carried-provenance-plan.md`,
    /// checked on every expansion of every test rather than on a sample).
    /// The refused channel is not compared ([`Trust::is_held_by`] says why).
    /// An expansion that hit an unsupported expression is refused whole, so it
    /// is exempt.
    fn assert_scan_holds_the_reads(
        &self,
        raw: &str,
        carried: &Trust,
        unpinned_root: Option<&UnpinnedRoot>,
        had_unsupported: bool,
    ) {
        if !cfg!(debug_assertions) || had_unsupported {
            return;
        }
        let scanned = self.trust_for_raw(raw);
        debug_assert!(
            (carried.unpinned().is_none() || unpinned_root.is_some())
                && (carried.sdk_package().is_none() || scanned.sdk_package().is_some())
                && (carried.stale().is_none() || scanned.stale().is_some()),
            "the reference scan of {raw:?} holds less doubt than the expansion's reads: \
             carried {carried:?}, scanned root {unpinned_root:?}, scanned {scanned:?}"
        );
    }

    /// Rebind the `MSBuildThisFile*` family to the imported file. MSBuild
    /// rebinds these for the duration of the import; references like
    /// `$(MSBuildThisFileDirectory)foo.props` in a `Directory.Build.props`
    /// should resolve against *that* file's directory, not the entry
    /// project's.
    ///
    /// Every name is seeded by [`properties::well_known`], so the saved
    /// values are always present; the [`ThisFileFrame`] just records them
    /// verbatim for [`Self::exit_this_file`] to restore.
    /// Record the name a `<UsingTask>` binds a task under
    /// ([`Self::using_task_names`]), `$(MSBuildThisFileName)` read as the
    /// file being walked (MSBuild expands the name when it registers it).
    /// MSBuild's own registration of a built-in, `Microsoft.Build.Tasks.<Task>`
    /// in its tasks assembly (`Microsoft.Common.tasks`), is the binding the
    /// executor models, so it binds nothing new.
    #[cfg(any(test, feature = "test-support"))]
    fn record_using_task(&mut self, node: Node<'_, '_>) {
        let name = attribute(node, "TaskName").unwrap_or_default();
        let built_in = name
            .strip_prefix("Microsoft.Build.Tasks.")
            .is_some_and(|task| {
                !task.is_empty() && task.bytes().all(|b| b.is_ascii_alphanumeric())
            })
            && attribute(node, "AssemblyName").as_deref() == Some(MSBUILD_TASKS_ASSEMBLY)
            && node
                .attributes()
                .all(|a| matches!(a.name(), "TaskName" | "AssemblyName" | "Condition"))
            && !node.children().any(|c| c.is_element());
        if built_in {
            return;
        }
        // A reserved name, which no project can write.
        let name = match self.lookup.get_ignoring_trust("MSBuildThisFileName") {
            Some(file) => name.replace(
                "$(MSBuildThisFileName)",
                &properties::escaping::unescape(file.as_escaped()),
            ),
            None => name.into_owned(),
        };
        self.using_task_names.push(name);
    }

    /// Record a `<Target>` element in the file being walked
    /// ([`Self::target_definitions`]).
    #[cfg(any(test, feature = "test-support"))]
    fn record_target_definition(&mut self, node: Node<'_, '_>) {
        let file = match &self.current_file {
            CurrentFile::Entry => self.entry_project_path.clone(),
            CurrentFile::Imported { path, .. } => path.clone(),
        };
        let name = attribute(node, "Name").unwrap_or_default().into_owned();
        self.target_definitions.push((
            name,
            reads::TargetDefinition {
                file,
                range: node.range(),
                xml: node.document().input_text()[node.range()].to_owned(),
            },
        ));
    }

    fn enter_this_file(&mut self, file_path: &Path) -> ThisFileFrame {
        let seeds = properties::this_file_seeds(file_path);
        let saved = seeds
            .iter()
            // Reserved names, which no project can write: the frame saves and
            // restores their values, and their trust is certain throughout.
            .map(|(name, _)| {
                let value = self.lookup.get_ignoring_trust(name).cloned();
                (*name, value.unwrap_or_default())
            })
            .collect();
        for (name, value) in seeds {
            self.lookup.insert_escaped(name, value);
        }
        ThisFileFrame { saved }
    }

    fn exit_this_file(&mut self, frame: ThisFileFrame) {
        for (name, value) in frame.saved {
            self.lookup.insert_escaped(name, value);
        }
    }
}

/// Apply the CPM subset that is exact from already-captured items:
/// NuGet-marked Central Package Management, unique inline `PackageVersion`
/// items, no local `PackageReference Version` metadata, no central-version
/// mutations, and no global implicit refs. (`Update` items have already been
/// folded into their `Include` by the item pass's
/// `finalize_package_references`, so a version an `Update` supplied is seen
/// here as the `Include`'s own.)
/// `VersionOverride` is applied only when NuGet's override switch permits it.
/// Anything outside that envelope leaves the existing uncertainty causes in
/// place so the NuGet resolver still declines rather than guessing.
fn apply_inline_cpm_versions(
    central_package_management_enabled: bool,
    package_references: &mut [PackageReference],
    package_versions: &[PackageVersion],
    package_versions_untracked: bool,
    global_package_references: &[GlobalPackageReference],
    central_package_version_override_enabled: bool,
    package_reference_uncertainties: &mut Vec<PackageReferenceUncertaintyCause>,
) {
    if !central_package_management_enabled
        || package_versions_untracked
        || !global_package_references.is_empty()
    {
        return;
    }
    let Some(central_versions) = unique_central_versions(package_versions) else {
        return;
    };

    let mut all_includes_resolved = true;
    for reference in package_references.iter_mut() {
        if reference.version.is_some() {
            all_includes_resolved = false;
            continue;
        }
        let key = reference.id.to_ascii_lowercase();
        if let Some(version_override) = &reference.version_override {
            if central_package_version_override_enabled {
                reference.version = Some(version_override.clone());
            } else {
                all_includes_resolved = false;
            }
            continue;
        }
        if let Some(version) = central_versions.get(&key) {
            reference.version = Some(version.clone());
            continue;
        }
        if reference.version.is_none() {
            all_includes_resolved = false;
        }
    }

    if all_includes_resolved {
        package_reference_uncertainties
            .retain(|cause| !is_discharged_inline_cpm_uncertainty(&cause.kind));
    }
}

fn unique_central_versions(package_versions: &[PackageVersion]) -> Option<HashMap<String, String>> {
    let mut central_versions = HashMap::new();
    for package_version in package_versions {
        let key = package_version.id.to_ascii_lowercase();
        if central_versions.contains_key(&key) {
            return None;
        }
        let version = package_version.version.clone()?;
        central_versions.insert(key, version);
    }
    Some(central_versions)
}

fn is_discharged_inline_cpm_uncertainty(kind: &PackageReferenceUncertaintyCauseKind) -> bool {
    matches!(
        kind,
        PackageReferenceUncertaintyCauseKind::ManagePackageVersionsCentrally
            | PackageReferenceUncertaintyCauseKind::PackageVersion
            | PackageReferenceUncertaintyCauseKind::VersionlessPackageReference { .. }
    )
}

/// Saved values for [`State::exit_this_file`] to restore after an
/// imported file's body has been walked. See [`State::enter_this_file`].
struct ThisFileFrame {
    /// Saved **escaped**, and restored escaped: the values never leave the
    /// domain, because `escape(unescape(s))` is not `s` in general — a
    /// round-trip through the unescaped form would corrupt a path containing
    /// any reserved character.
    saved: Vec<(&'static str, Escaped)>,
}
fn walk_top_level(node: Node<'_, '_>, current_file_dir: &Path, state: &mut State<'_>) {
    match node.tag_name().name() {
        // Items belong to a later evaluation pass than properties: MSBuild
        // finalises every property (across the whole import graph) before
        // evaluating any `<ItemGroup>`. Record the group; the item pass
        // ([`replay_deferred_item_groups`]) evaluates it against the final
        // property table once the property pass has fully completed.
        "ItemGroup" => state.defer_item_group(node, DeferredGroupKind::ItemGroup),
        "PropertyGroup" => {
            // Plan D5: an unsupported condition treats the containing
            // group as *excluded*. We never silently include items —
            // but the same logic, applied to property writes, would
            // mark every project partial for the standard
            // "default-if-empty" idiom:
            //   <PropertyGroup Condition="'$(Configuration)' == ''">
            //     <Configuration>Debug</Configuration>
            //   </PropertyGroup>
            // When every child writes to a protected name, the writes
            // are already silently discarded regardless of the
            // condition; the group is effectively a no-op whether the
            // condition fires or not. Suppress diagnostics and skip
            // walking in that case — there's nothing the condition
            // could affect. (Empty groups trivially satisfy this.)
            let all_protected = node.children().filter(Node::is_element).all(|c| {
                state
                    .protected
                    .contains(&c.tag_name().name().to_ascii_lowercase())
            });
            if all_protected {
                // MSBuild still evaluates the group's own condition, though it
                // discards each write unevaluated.
                if attribute(node, "Condition").is_some() {
                    let reached = rejection::reach_is_certain(state);
                    rejection::judge_unwalked_gate(node, current_file_dir, reached, state);
                }
                return;
            }
            // A group that writes `<DefineConstants>` makes its own condition
            // *preprocessor-affecting*: an undefined/unmodeled condition here
            // (e.g. `'$(TargetFramework)' == 'net6.0'` in a multi-targeted
            // project) decides whether those defines apply. Mirror the
            // `compile_context` discipline (entry/user files only). Children
            // each manage their own context in `walk_property_child`.
            let prev = state.define_context;
            state.define_context =
                prev || (!state.in_sdk_subtree && property_group_writes_define_constants(node));
            // The same discipline for a group writing a CPM flag: its condition
            // decides whether Central Package Management turns on, or whether
            // the central versions import marker can be trusted. Setting
            // `package_context` across the evaluation makes an undefined /
            // unsupported condition flip `package_references_uncertain` via
            // `push` (a clean, defined-property condition raises no diagnostic,
            // so a genuinely-off opt-in stays certain). Reused rather than a
            // bespoke flag — `package_context` is exactly "a package decision
            // hangs on this". Reset before walking children (the write itself is
            // handled by the final-value check in `into_project`).
            let prev_pkg = state.package_context;
            let writes_cpm_flag = property_group_writes_cpm_flag(node);
            state.package_context = prev_pkg || writes_cpm_flag;
            if writes_cpm_flag {
                // A condition depending on an SDK property may evaluate cleanly
                // (no diagnostic) to false in this document-order walk, while
                // MSBuild's property pass would make it true before items run.
                state.note_package_uncertain_if_condition_uses_sdk_taint(node);
            }
            let group_condition_uses_sdk_taint = attribute(node, "Condition")
                .as_deref()
                .is_some_and(|condition| {
                    state
                        .condition_trust(condition, Some(current_file_dir))
                        .sdk_package()
                        .is_some()
                });
            // Whether MSBuild evaluates what the group holds exactly when the walk
            // does ([`rejection`]): asked before the gate's evaluation, of the
            // values it reads.
            let gate_certain = attribute(node, "Condition").is_none_or(|condition| {
                directory_build::decided_from_certain_inputs(state, &condition, current_file_dir)
            });
            let diagnostics_before_condition = state.diagnostics.len();
            let gate = evaluate_property_group_condition(node, current_file_dir, state);
            let group_condition_maybe_wrong = state.diagnostics.len()
                != diagnostics_before_condition
                || matches!(&gate, CondGate::Unsupported);
            let sdk_group_condition_taint = group_condition_uses_sdk_taint
                || (state.in_sdk_subtree && group_condition_maybe_wrong);
            // The root cause behind an unpinnable group gate — surfaced by
            // the condition evaluation just above — recorded against every
            // property the group writes (Run: the write may not happen in a
            // real build; Skip: it may).
            let group_unpinned_root = if group_condition_maybe_wrong {
                state
                    .unpinned_root_from_recent_diagnostics(diagnostics_before_condition)
                    .or_else(|| {
                        attribute(node, "Condition")
                            .as_deref()
                            .map(|c| UnpinnedRoot::UnsupportedCondition(c.into()))
                    })
            } else {
                None
            };
            match gate {
                CondGate::Run => {
                    state.define_context = prev;
                    state.package_context = prev_pkg;
                    let group_stale = attribute(node, "Condition")
                        .and_then(|condition| state.trust_for_raw(&condition).stale().cloned());
                    let saved_stale = state.enclosing_condition_stale.clone();
                    if state.enclosing_condition_stale.is_none() {
                        state.enclosing_condition_stale = group_stale;
                    }
                    state.reach_doubted += usize::from(!gate_certain);
                    for child in node.children().filter(Node::is_element) {
                        walk_property_child(
                            child,
                            sdk_group_condition_taint,
                            group_condition_maybe_wrong,
                            group_unpinned_root.as_ref(),
                            state,
                        );
                    }
                    state.reach_doubted -= usize::from(!gate_certain);
                    state.enclosing_condition_stale = saved_stale;
                }
                CondGate::Skip => {
                    // MSBuild may take the group, and evaluate its writes.
                    if !gate_certain {
                        rejection::judge_properties(node, false, state);
                    }
                    if group_condition_maybe_wrong || sdk_group_condition_taint {
                        // The gate could not be pinned down, so the group's
                        // writes may actually run in the real build — the
                        // written properties' final values are untrustworthy
                        // for package metadata. Taint them for the item
                        // pass's package reads, and unpin them so every
                        // item-pass read re-surfaces the root cause.
                        mark_property_group_children_provenance(
                            node,
                            group_unpinned_root.as_ref(),
                            state,
                        );
                    }
                    // A gate decided on a stale value may hold in the real
                    // build, which then runs every write a child's own gate
                    // does not rule out.
                    if let Some(cause) = state.stale_gate_cause(node, gate_certain) {
                        for child in node.children().filter(Node::is_element) {
                            if property_child_could_write(child, state) {
                                state.mark_skipped_write_stale(child.tag_name().name(), &cause);
                            }
                        }
                    }
                    state.define_context = prev;
                    state.package_context = prev_pkg;
                }
                CondGate::Unsupported => {
                    mark_property_group_children_provenance(
                        node,
                        group_unpinned_root.as_ref(),
                        state,
                    );
                    rejection::judge_properties(node, false, state);
                    emit_unsupported_condition(node, state);
                    state.define_context = prev;
                    state.package_context = prev_pkg;
                }
            }
        }
        "Import" => handle_import(node, current_file_dir, state),
        "ImportGroup" => {
            // The group's `Condition` gates its imports; an untrusted one may
            // hide imports that carry Compile or dependency items, in an SDK
            // file as in a user's (same as a bare `<Import>` condition).
            let route_decided = directory_build::gate_is_decided(node, current_file_dir, state);
            let prev_gate = state.import_gate_context;
            let prev_pkg_gate = state.package_import_gate_context;
            state.import_gate_context = true;
            state.package_import_gate_context = true;
            let diagnostics_before_gate = state.diagnostics.len();
            let gate = evaluate_condition(node, current_file_dir, state);
            state.note_package_uncertain_if_condition_uses_sdk_taint(node);
            // Same reference-list rule as a bare `<Import>`'s own gate: an
            // untrusted decision here hides (or phantom-includes) whatever
            // the group's imports carry, `<ProjectReference>` mutations
            // included.
            if state.condition_reads_untrusted_value(node) {
                state.project_references_uncertain = true;
            }
            // Same rule as `follow_explicit_import`: an undecided group
            // gate may bring in or omit whole files of property writes.
            let gate_raised_doubt = state.diagnostics.len() != diagnostics_before_gate
                || matches!(gate, CondGate::Unsupported);
            let undecided = gate_raised_doubt
                .then(|| state.latch_undecided_import_gate(node, diagnostics_before_gate));
            // A gate decided on a stale value may go the other way in the
            // real build, as an undecided one may (#1037).
            let stale_gate = if gate_raised_doubt {
                None
            } else {
                state.stale_gate_cause(node, route_decided)
            };
            match gate {
                CondGate::Run => {
                    state.import_gate_context = prev_gate;
                    state.package_import_gate_context = prev_pkg_gate;
                    // MSBuild lets imports nest inside an <ImportGroup
                    // Condition="..."> wrapper. The group adds gating but
                    // nothing else we model — every Import inside still
                    // routes through `handle_import`.
                    directory_build::within_route(route_decided, state, |state| {
                        directory_build::within_followed_import(undecided, state, |state| {
                            for child in node.children().filter(Node::is_element) {
                                if child.tag_name().name() == "Import" {
                                    handle_import(child, current_file_dir, state);
                                } else {
                                    state.push(
                                        DiagnosticKind::UnsupportedConstruct {
                                            element: child.tag_name().name().to_string(),
                                        },
                                        child.range(),
                                    );
                                }
                            }
                        });
                    });
                }
                CondGate::Skip => {
                    state.import_gate_context = prev_gate;
                    state.package_import_gate_context = prev_pkg_gate;
                    // As for a bare `<Import>` (#820).
                    if gate_raised_doubt || !route_decided {
                        rejection::judge_imports(node, current_file_dir, false, state);
                        rejection::undecided_import_group(node, current_file_dir, state);
                    }
                    // The imports the walk did not see may run, unless each
                    // one's own gate fails whatever the uncertain names hold.
                    if let Some(cause) = stale_gate {
                        let any_may_run = node
                            .children()
                            .filter(|child| {
                                child.is_element() && child.tag_name().name() == "Import"
                            })
                            .any(|import| !state.ruled_out(import, current_file_dir));
                        if any_may_run {
                            state.latch_walk_opaque((*cause).clone(), node.range());
                        }
                    }
                }
                CondGate::Unsupported => {
                    emit_unsupported_condition(node, state);
                    state.import_gate_context = prev_gate;
                    state.package_import_gate_context = prev_pkg_gate;
                    rejection::judge_imports(node, current_file_dir, false, state);
                    rejection::undecided_import_group(node, current_file_dir, state);
                }
            }
        }
        "Choose" => handle_choose(node, current_file_dir, state),
        // Item definitions belong to MSBuild's pass 2 — after every property
        // (pass 1), before any item (pass 3). Defer alongside `<ItemGroup>`s;
        // the replay runs all definition groups before any item group.
        "ItemDefinitionGroup" => {
            state.defer_item_group(node, DeferredGroupKind::ItemDefinitionGroup)
        }
        "Target" | "UsingTask" => {
            // Neither contributes to the *static* Compile item set —
            // `<Target>` items are build-time, `<UsingTask>` declares a
            // task. They flip `is_partial` only.
            #[cfg(any(test, feature = "test-support"))]
            if node.tag_name().name() == "Target" {
                state.record_target_definition(node);
            } else {
                state.record_using_task(node);
            }
            // MSBuild evaluates a `<UsingTask>`'s condition after every item,
            // and never a `<Target>`'s in evaluation.
            if node.tag_name().name() == "UsingTask" {
                state.defer_item_group(node, DeferredGroupKind::UsingTask);
            }
            state.push(
                DiagnosticKind::UnsupportedConstruct {
                    element: node.tag_name().name().to_string(),
                },
                node.range(),
            );
        }
        _ => {
            // Unknown top-level element: silently ignore. The MSBuild schema
            // is open; unknown extensions almost never affect Compile order.
            // (The top-level `<Sdk>` element is not one of these — the
            // pre-scan in [`walk_doc_body`] degrades it before any child
            // walks.)
        }
    }
}

/// `<Choose>`: a first-match-wins chain of condition-gated branches.
///
/// Semantics pinned against `dotnet msbuild` with per-case stub projects
/// (2026-07-09; docs/completed/sdk-chain-exactness-plan.md, Stage A):
///
///   * `<When>` conditions evaluate during the **property pass**, in
///     document order, against the table as it stands at the `<Choose>`'s
///     position. The first true gate wins; conditions after the match are
///     never evaluated (an MSBuild-illegal condition there does not even
///     error).
///   * The branch decision is **reused by the item pass**: the chosen
///     branch's `<ItemGroup>`s defer exactly like body groups (each still
///     evaluating its own `Condition` against the final table); the other
///     branches' contents are never looked at, and their writes never
///     land.
///   * A malformed shape — a `<When>` without `Condition` (MSB4035), an
///     `<Otherwise>` out of last position, multiple `<Otherwise>`s, a
///     stray child of the `<Choose>`, no `<When>` at all, or a
///     schema-illegal element *anywhere inside any branch* (MSB4067,
///     even a branch that would never be chosen — MSBuild validates the
///     whole tree at load time, pinned with stub projects) — fails the
///     real evaluation before anything runs; we degrade conservatively
///     without evaluating any part of the `<Choose>`.
///
/// A *reached* gate we cannot pin down (unsupported grammar, a read of an
/// undefined or tainted property) makes the decision itself
/// untrustworthy: nothing from that point on is descended. Every
/// still-possible branch's property writes are tainted/unpinned (any of
/// them may run in a real build), and each item list a still-possible
/// branch names is marked on its own axis
/// ([`item_pass::UndecidedChooseItems`]): a Compile item makes the Compile
/// set uncertain, a package item the package set, a `<ProjectReference>`
/// the reference list, and any other type taints that helper list. That is
/// all such a branch can do, so the walk does not go opaque: a
/// properties-only `<Choose>` (the SDK's pervasive `DefineConstants`
/// default-fill in `Microsoft.FSharp.NetSdk.props`), or one holding only
/// `<None>` items, leaves every other value exactly as trusted as before.
fn handle_choose(node: Node<'_, '_>, current_file_dir: &Path, state: &mut State<'_>) {
    // Full-tree shape validation up front: MSBuild rejects a malformed
    // `<Choose>` at *load* time — before any evaluation, and regardless
    // of which branch would be chosen — so nothing from this element may
    // land when any part of it is malformed.
    if !choose_shape_is_valid(node) {
        state.push(
            DiagnosticKind::UnsupportedConstruct {
                element: "Choose".to_string(),
            },
            node.range(),
        );
        state.mark_structural_skip(
            StructuralCompileItemUncertainty::UnsupportedChoose,
            node.range(),
        );
        // A malformed Choose fails MSBuild's whole evaluation at load time —
        // there is no build for the captured reference list to describe,
        // whichever file holds it. The UnsupportedChoose carve-out in
        // `mark_structural_skip` defers to the undecided-branch mutation scan,
        // which never runs on this path, so set the flag here.
        state.project_references_uncertain = true;
        return;
    }
    let whens: Vec<Node<'_, '_>> = node
        .children()
        .filter(Node::is_element)
        .filter(|c| c.tag_name().name() == "When")
        .collect();
    let otherwise: Option<Node<'_, '_>> = node
        .children()
        .filter(Node::is_element)
        .find(|c| c.tag_name().name() == "Otherwise");

    // Mirror the `<PropertyGroup>` gate discipline while the `<When>`
    // conditions evaluate: a branch write to `DefineConstants` (or a CPM
    // flag) makes a gate preprocessor-/package-affecting, so `push`
    // attributes an undecidable gate's diagnostics to those axes. The
    // scan is recursive — a write inside a *nested* Choose is just as
    // much decided by this gate as a direct child's — and per-gate: by
    // the time gate `i` evaluates, branches before `i` were *cleanly
    // false*, so only writes in the still-possible branches (`i..` plus
    // `<Otherwise>`) can hang on it. Suffix-OR over per-branch scans.
    let writes_after = |pred: &dyn Fn(Node<'_, '_>) -> bool| -> Vec<bool> {
        let otherwise_writes = otherwise.is_some_and(|o| choose_branch_writes(o, pred));
        let mut suffix = vec![false; whens.len()];
        let mut acc = otherwise_writes;
        for (slot, when) in suffix.iter_mut().zip(&whens).rev() {
            acc = acc || choose_branch_writes(*when, pred);
            *slot = acc;
        }
        suffix
    };
    let defines_still_possible = writes_after(&property_group_writes_define_constants);
    let cpm_still_possible = writes_after(&property_group_writes_cpm_flag);
    let prev_define = state.define_context;
    let prev_package = state.package_context;

    let mut chosen: Option<(usize, Node<'_, '_>)> = None;
    // The first `<When>` the walk did not decide from certain inputs: from it
    // on, MSBuild may choose another branch than the walk, so what the walk
    // reaches there it does not reach for certain ([`rejection`]).
    let mut first_unsure: Option<usize> = None;
    let mut chosen_is_certain = true;
    let mut undecided: Option<(usize, Option<UnpinnedRoot>)> = None;
    let mut choice_stale: Option<properties::trust::StaleCause> = None;
    // A `<When>` resolves `Exists` against the entry project, wherever the
    // `<Choose>` is: MSBuild's `GetCurrentDirectoryForConditionEvaluation`
    // gives the containing file's directory only to a property group, an
    // import and an import group.
    let exists_dir = state.entry_project_dir.clone();
    for (index, when) in whens.iter().enumerate() {
        if choice_stale.is_none() {
            choice_stale = attribute(*when, "Condition")
                .and_then(|condition| state.trust_for_raw(&condition).stale().cloned());
        }
        state.define_context =
            prev_define || (!state.in_sdk_subtree && defines_still_possible[index]);
        state.package_context = prev_package || cpm_still_possible[index];
        if cpm_still_possible[index] {
            state.note_package_uncertain_if_condition_uses_sdk_taint(*when);
        }
        let uses_sdk_taint = attribute(*when, "Condition")
            .as_deref()
            .is_some_and(|condition| {
                state
                    .condition_trust(condition, Some(&exists_dir))
                    .sdk_package()
                    .is_some()
            });
        let certain = attribute(*when, "Condition").is_none_or(|condition| {
            directory_build::decided_from_certain_inputs(state, &condition, &exists_dir)
        });
        let diagnostics_before = state.diagnostics.len();
        let gate = evaluate_condition(*when, &exists_dir, state);
        if !certain && first_unsure.is_none() {
            first_unsure = Some(index);
            state.reach_doubted += 1;
        }
        let maybe_wrong =
            state.diagnostics.len() != diagnostics_before || matches!(gate, CondGate::Unsupported);
        if maybe_wrong || uses_sdk_taint {
            if matches!(gate, CondGate::Unsupported) {
                emit_unsupported_condition(*when, state);
            }
            let unpinned_root = state
                .unpinned_root_from_recent_diagnostics(diagnostics_before)
                .or_else(|| {
                    attribute(*when, "Condition")
                        .as_deref()
                        .map(|c| UnpinnedRoot::UnsupportedCondition(c.into()))
                });
            undecided = Some((index, unpinned_root));
            break;
        }
        if matches!(gate, CondGate::Run) {
            chosen = Some((index, *when));
            chosen_is_certain = certain;
            break;
        }
        // A cleanly-false gate: MSBuild skips this branch too; keep going.
    }
    state.define_context = prev_define;
    state.package_context = prev_package;

    if let Some((from, unpinned_root)) = undecided {
        // Branches from the first unpinnable gate on may or may not run in
        // a real build. (Branches before it were cleanly false — MSBuild
        // skips those too, so leaving them untouched is exact.)
        // The branches before the undecided gate, from the first the walk
        // decided on a stale value, may be the one MSBuild takes: judged
        // from the state before the `<Choose>`, as the later ones are, and
        // marked with them.
        let before_undecided = match (first_unsure, choice_stale.clone()) {
            (Some(first), Some(cause)) => {
                let branches: Vec<Node<'_, '_>> = whens[first..from]
                    .iter()
                    .copied()
                    .filter(|branch| !state.ruled_out(*branch, &exists_dir))
                    .collect();
                let written = state.skipped_branch_writes(&branches, current_file_dir, &cause);
                Some((written, cause))
            }
            _ => None,
        };
        // MSBuild may choose any of those branches, and evaluate the gates
        // after this one: against the state before the `<Choose>`, as no
        // branch has run when it does, so before the branches' writes are
        // marked below. A later gate false whatever the uncertain names hold
        // there rules its branch out, which a gate read after the marks would
        // not.
        for branch in &whens[first_unsure.unwrap_or(from)..=from] {
            rejection::judge_branch(*branch, current_file_dir, false, state);
        }
        rejection::judge_whens(node, from + 1, current_file_dir, false, state);
        // The branches MSBuild may take: every one but those a gate false
        // whatever the uncertain names hold rules out, and those after one
        // whose gate holds whatever they hold, each decided on the state
        // before the `<Choose>`, which is MSBuild's state when it evaluates
        // the gates (so before any branch's writes are marked below). Decided
        // with no file system: MSBuild may evaluate none of these gates, so
        // asking probes nothing, and an `Exists` decides nothing.
        let live: Vec<Node<'_, '_>> = {
            let mut live = vec![whens[from]];
            let mut taken = false;
            for branch in whens[from + 1..].iter().copied() {
                let decision = attribute(branch, "Condition").and_then(|condition| {
                    match condition::decide_without(
                        &condition,
                        &state.lookup,
                        None,
                        state.condition_site(),
                        &|name| !directory_build::is_certain(state, name),
                    ) {
                        condition::Decision::Decided(value) => Some(value),
                        _ => None,
                    }
                });
                if decision != Some(false) {
                    live.push(branch);
                }
                if decision == Some(true) {
                    taken = true;
                    break;
                }
            }
            if !taken {
                live.extend(otherwise);
            }
            live
        };
        let mut items = item_pass::UndecidedChooseItems::default();
        for branch in live {
            scan_undecided_choose_branch(branch, unpinned_root.as_ref(), state, &mut items);
        }
        items.apply(node.range(), state);
        if let Some((written, cause)) = before_undecided {
            for name in written {
                state.mark_skipped_write_stale(&name, &cause);
            }
        }
        state.reach_doubted -= usize::from(first_unsure.is_some());
        return;
    }

    // From the first gate the walk did not decide from certain inputs, MSBuild
    // may choose a branch before the walk's, and evaluate the gates after the
    // walk's while that one is among them.
    let walked = chosen.map_or(whens.len(), |(index, _)| index);
    if let Some(first) = first_unsure {
        for branch in &whens[first..walked] {
            rejection::judge_branch(*branch, current_file_dir, false, state);
        }
    }
    if !chosen_is_certain {
        rejection::judge_whens(node, walked + 1, current_file_dir, false, state);
    }
    state.arm_decisions.remove(&rejection::choose_key(node));
    // From the first gate the walk decided on a stale value, MSBuild may take
    // any branch but the walk's up to the first whose gate holds whatever the
    // uncertain names hold (and `<Otherwise>` only if none does), skipping
    // those whose gate fails whatever they hold: what each writes, the real
    // build may hold. The branch the walk takes is walked under that gate's
    // staleness below.
    // Each is judged from the state before the `<Choose>`, as is the walk's,
    // and marked once the walk's is walked.
    let alternatives = match (first_unsure, choice_stale.clone()) {
        (Some(first), Some(cause)) => {
            let untaken = state.choose_branches_from(node, first, Some(walked));
            let written = state.skipped_branch_writes(&untaken, current_file_dir, &cause);
            Some((written, cause))
        }
        _ => None,
    };
    let mark_alternatives = |state: &mut State<'_>| {
        if let Some((written, cause)) = &alternatives {
            for name in written {
                state.mark_skipped_write_stale(name, cause);
            }
        }
    };
    let Some(branch) = chosen.map(|(_, when)| when).or(otherwise) else {
        // Every gate cleanly false and no <Otherwise>: an exact no-op, but
        // for the branches MSBuild may take instead.
        mark_alternatives(state);
        state.reach_doubted -= usize::from(first_unsure.is_some());
        return;
    };
    let saved_stale = state.enclosing_condition_stale.clone();
    if state.enclosing_condition_stale.is_none() {
        state.enclosing_condition_stale = choice_stale;
    }
    for child in branch.children().filter(Node::is_element) {
        // `choose_shape_is_valid` guaranteed every branch child is a
        // `PropertyGroup`, `ItemGroup`, or nested `Choose`; each evaluates
        // exactly as if it appeared at the Choose's position.
        walk_top_level(child, current_file_dir, state);
    }
    state.enclosing_condition_stale = saved_stale;
    mark_alternatives(state);
    state.reach_doubted -= usize::from(first_unsure.is_some());
}

/// Whether a `<Choose>` subtree is shaped the way MSBuild's loader
/// requires: one or more `<When>`s each with a non-empty `Condition`
/// (MSB4035 calls an empty one out explicitly; a blank one loads, and
/// MSBuild throws on it only where it evaluates it, MSB4092), at most one
/// `<Otherwise>` and only in last position, no attribute beyond the
/// recognized set (`<Choose>` and `<Otherwise>` take *none* — even
/// `Label` is MSB4066 there, pinned; `<When>` takes `Condition` and
/// `Label`), and branch children drawn exclusively from
/// `PropertyGroup` / `ItemGroup` / nested `Choose` (anything else is
/// MSB4067) — with nested `Choose`s held to the same rules, and nested
/// no deeper than [`MAXIMUM_CHOOSE_NESTING`]. MSBuild enforces all of
/// this at load time, before evaluating anything, so one violation
/// anywhere invalidates the whole element.
///
/// The nesting ceiling is also what bounds every recursion through
/// `<Choose>` — this check, [`handle_choose`] by way of
/// [`walk_top_level`], [`choose_branch_writes`] and
/// [`scan_undecided_choose_branch`] — so that a deeply nested
/// `<Choose>` in a file the user does not control cannot overflow the
/// stack. Each of those runs only on a `<Choose>` this check passed,
/// and this check stops descending at the ceiling.
///
/// Deliberately *not* validated: attributes on the branch children
/// themselves, and anything else of MSBuild's load-time schema, which
/// the loader port judges for the whole file as the walk enters it
/// (`loader`, `rejection::judge_load_time`). This check only decides
/// whether the walk models a `<Choose>`, and is stricter than the
/// loader where the walk declines a shape MSBuild loads.
fn choose_shape_is_valid(node: Node<'_, '_>) -> bool {
    choose_shape_is_valid_at(node, 1)
}

/// The deepest `<Choose>` nesting MSBuild loads: a `<Choose>` with this
/// many `<Choose>` elements on its path (itself included) loads, one
/// more is `ChooseOverflow` (`ProjectParser.MaximumChooseNesting`).
const MAXIMUM_CHOOSE_NESTING: usize = 50;

/// [`choose_shape_is_valid`] for a `<Choose>` with `nesting` `<Choose>`
/// elements on its path within the file, itself included.
fn choose_shape_is_valid_at(node: Node<'_, '_>, nesting: usize) -> bool {
    if nesting > MAXIMUM_CHOOSE_NESTING {
        return false;
    }
    // `<When>` recognizes `Condition` and `Label`; `<Choose>` and
    // `<Otherwise>` recognize no attributes at all.
    let attrs_ok = |element: Node<'_, '_>, is_when: bool| {
        element
            .attributes()
            .all(|a| is_when && (a.name() == "Label" || a.name() == "Condition"))
    };
    if !attrs_ok(node, false) {
        return false;
    }
    let mut saw_when = false;
    let mut saw_otherwise = false;
    for child in node.children().filter(Node::is_element) {
        let branch = match child.tag_name().name() {
            "When" => {
                if saw_otherwise
                    || !attrs_ok(child, true)
                    || attribute(child, "Condition")
                        .as_deref()
                        .is_none_or(|c| c.is_empty())
                {
                    return false;
                }
                saw_when = true;
                child
            }
            "Otherwise" => {
                if saw_otherwise || !attrs_ok(child, false) {
                    return false;
                }
                saw_otherwise = true;
                child
            }
            _ => return false,
        };
        for grandchild in branch.children().filter(Node::is_element) {
            match grandchild.tag_name().name() {
                "PropertyGroup" | "ItemGroup" => {}
                "Choose" => {
                    if !choose_shape_is_valid_at(grandchild, nesting + 1) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
    }
    saw_when
}

/// Whether any `<PropertyGroup>` reachable in this branch — directly or
/// through nested `<Choose>` branches — satisfies `pred`. Used to decide
/// whether a `<When>` gate is preprocessor- or package-affecting.
fn choose_branch_writes(branch: Node<'_, '_>, pred: &dyn Fn(Node<'_, '_>) -> bool) -> bool {
    branch
        .children()
        .filter(Node::is_element)
        .any(|child| match child.tag_name().name() {
            "PropertyGroup" => pred(child),
            "Choose" => child
                .children()
                .filter(Node::is_element)
                .any(|nested| choose_branch_writes(nested, pred)),
            _ => false,
        })
}

/// Taint every property write in an undecided `<Choose>` branch (the
/// write may or may not land in a real build, so its stored value — and
/// its absence — are both untrustworthy) and record in `items` what its
/// item operations could reach.
///
/// Between them these are everything the branch can do, which is why an
/// undecided `<Choose>` does not make the walk opaque: a property write is
/// enumerated by name here, and an item writes no property.
fn scan_undecided_choose_branch(
    branch: Node<'_, '_>,
    unpinned_root: Option<&UnpinnedRoot>,
    state: &mut State<'_>,
    items: &mut item_pass::UndecidedChooseItems,
) {
    for child in branch.children().filter(Node::is_element) {
        match child.tag_name().name() {
            "PropertyGroup" => {
                mark_property_group_children_provenance(child, unpinned_root, state);
            }
            "ItemGroup" => items.note_item_group(child),
            "Choose" => {
                // A nested Choose's branches are all undecided too.
                for nested in child.children().filter(Node::is_element) {
                    scan_undecided_choose_branch(nested, unpinned_root, state, items);
                }
            }
            other => unreachable!(
                "choose_shape_is_valid admits only PropertyGroup, ItemGroup and Choose \
                 in a branch, not {other}"
            ),
        }
    }
}

fn walk_property_child(
    node: Node<'_, '_>,
    inherited_sdk_package_taint: bool,
    inherited_condition_maybe_wrong: bool,
    inherited_unpinned_root: Option<&UnpinnedRoot>,
    state: &mut State<'_>,
) {
    let name = node.tag_name().name().to_string();
    let lower = name.to_ascii_lowercase();
    if state.protected.contains(&lower) {
        // Reserved (well-known) or caller-supplied (extra_properties) name.
        // MSBuild forbids the project from rebinding these — and crucially,
        // it discards the whole assignment *without* evaluating the
        // Condition or the value. Mirror that: emit no diagnostics for
        // either, since the project is using a standard idiom (e.g.
        // `<Configuration Condition="'$(Configuration)' == ''">Debug</…>`)
        // that we'd otherwise misreport as a partial-evaluation failure.
        return;
    }
    // A `<DefineConstants>` write feeds the `#if` symbol set, via both its
    // condition (which branch applies) and its value. Scope `define_context` to
    // the whole element (entry/user files only); `push` then flags any
    // uncertainty here — an unresolvable condition, an unsupported/item/metadata
    // value reference — except the `$(DefineConstants)` self-append, which
    // matches MSBuild (see `is_define_self_reference`). Single restore.
    let prev_define = state.define_context;
    state.define_context = prev_define || (lower == "defineconstants" && !state.in_sdk_subtree);
    // A CPM flag's own Condition and value are package-affecting for the same
    // reason as its containing group's Condition: if either is only evaluated by
    // treating unknown input as empty, the later inline CPM pass must retain a
    // non-CPM-specific cause after discharging `PackageVersion` / versionless
    // reference uncertainty.
    let prev_package = state.package_context;
    state.package_context = prev_package || is_cpm_flag_property_name(&name);
    walk_property_child_inner(
        node,
        name,
        lower,
        inherited_sdk_package_taint,
        inherited_condition_maybe_wrong,
        inherited_unpinned_root,
        state,
    );
    state.package_context = prev_package;
    state.define_context = prev_define;
}

fn walk_property_child_inner(
    node: Node<'_, '_>,
    name: String,
    lower: String,
    inherited_sdk_package_taint: bool,
    inherited_condition_maybe_wrong: bool,
    inherited_unpinned_root: Option<&UnpinnedRoot>,
    state: &mut State<'_>,
) {
    let had_prior_sdk_package_taint = state.sdk_package_property_is_tainted(&name);
    // Property-element conditions resolve `Exists` against the entry project
    // (see `evaluate_property_condition`).
    let entry_dir = state.entry_project_dir.clone();
    let condition_uses_sdk_taint =
        attribute(node, "Condition")
            .as_deref()
            .is_some_and(|condition| {
                state
                    .condition_trust(condition, Some(&entry_dir))
                    .sdk_package()
                    .is_some()
            });
    // Asked of the values the gate reads before its evaluation, and only of a
    // gate that reads a stale one: nothing else needs it.
    let own_gate_decided = attribute(node, "Condition").is_none_or(|condition| {
        state.trust_for_raw(&condition).stale().is_none()
            || directory_build::decided_from_certain_inputs(state, &condition, &entry_dir)
    });
    // Whether MSBuild evaluates the body exactly when the walk does
    // ([`rejection`]), asked of the values the gate reads: only for a body
    // that throws, or one the walk skips.
    // `None` where the gate reads a value that may decide it otherwise.
    let own_gate = |state: &State<'_>| match attribute(node, "Condition") {
        None => Some(true),
        Some(condition) => {
            directory_build::decision_from_certain_inputs(state, &condition, &entry_dir)
        }
    };
    let diagnostics_before_condition = state.diagnostics.len();
    let gate = evaluate_property_condition(node, state);
    let own_condition_maybe_wrong = state.diagnostics.len() != diagnostics_before_condition
        || matches!(&gate, CondGate::Unsupported);
    // MSBuild may take a write the walk skips, and evaluate its body: one
    // whose gate holds whatever the walk could not evaluate in it (`… Or
    // true`) it takes wherever the walk reaches it.
    if !matches!(gate, CondGate::Run) {
        match own_gate(state) {
            Some(false) => {}
            Some(true) => {
                let reached = rejection::reach_is_certain(state);
                rejection::judge_unwalked_body(node, reached, state);
            }
            None => rejection::judge_unwalked_body(node, false, state),
        }
    }
    let write_condition_maybe_wrong = inherited_condition_maybe_wrong || own_condition_maybe_wrong;
    let condition_taints_property = inherited_sdk_package_taint
        || condition_uses_sdk_taint
        || (state.in_sdk_subtree && own_condition_maybe_wrong);
    match gate {
        CondGate::Run => {}
        CondGate::Skip => {
            // A write skipped under a gate our property pass could not pin
            // down (an undefined property the real build may supply, an
            // unsupported condition, or SDK-tainted input) may actually run
            // in the real build — so the property's final value is not
            // trustworthy. Taint it for package reads, and unpin it so every
            // item-pass read re-surfaces the gate's root cause.
            let taint = if condition_taints_property || own_condition_maybe_wrong {
                TaintOutcome::Set(node.range())
            } else {
                TaintOutcome::Keep
            };
            let unpinned = if own_condition_maybe_wrong {
                match state
                    .unpinned_root_from_recent_diagnostics(diagnostics_before_condition)
                    .or_else(|| {
                        attribute(node, "Condition")
                            .as_deref()
                            .map(|c| UnpinnedRoot::UnsupportedCondition(c.into()))
                    }) {
                    Some(root) => UnpinnedOutcome::Set(root),
                    None => UnpinnedOutcome::Keep,
                }
            } else {
                UnpinnedOutcome::Keep
            };
            // A gate decided on a stale value may hold in the real build.
            let stale = match state.stale_gate_cause(node, own_gate_decided) {
                Some(cause) if state.skipped_write_needs_mark(&name) => StaleOutcome::Set(cause),
                _ => StaleOutcome::Keep,
            };
            state.apply_property_provenance(
                &name,
                PropertyProvenance {
                    taint,
                    unpinned,
                    // The write may or may not have happened; either way we
                    // refused no value of our own.
                    refused: RefusedOutcome::Keep,
                    stale,
                },
            );
            return;
        }
        CondGate::Unsupported => {
            let unpinned = match attribute(node, "Condition").as_deref() {
                Some(condition) => {
                    UnpinnedOutcome::Set(UnpinnedRoot::UnsupportedCondition(condition.into()))
                }
                None => UnpinnedOutcome::Keep,
            };
            state.apply_property_provenance(
                &name,
                PropertyProvenance {
                    taint: TaintOutcome::Set(node.range()),
                    unpinned,
                    refused: RefusedOutcome::Keep,
                    stale: StaleOutcome::Keep,
                },
            );
            emit_unsupported_condition(node, state);
            return;
        }
    }
    // The element's value is its *full inner text* with literal-whitespace-only
    // text children dropped as insignificant — both rules, and the two shapes
    // whose value we cannot derive, live in [`collect_element_text`]. Empty
    // content (`<Foo/>`, `<Foo></Foo>`, `<Foo> </Foo>`) yields the empty string
    // — distinct from "undefined", and used in real projects to clear an
    // inherited value.
    let Some(raw) = collect_element_text(node) else {
        // MSBuild expands the body as it reads it, its inner XML included,
        // and may throw on an expression there.
        let reached = rejection::reach_is_certain(state) && own_gate(state) == Some(true);
        rejection::judge_unwalked_body(node, reached, state);
        // A body we cannot model (an element or processing instruction). Same
        // treatment as an unevaluable expansion below: drop any prior binding
        // rather than let a stale value stand in for a write whose result we
        // don't know, and unpin the name so every later read re-surfaces it.
        state.push(
            DiagnosticKind::UnsupportedPropertyExpression {
                expression: format!("<{name}> body"),
            },
            node.range(),
        );
        state.lookup.unbind(&name);
        state.written.remove(&lower);
        state.apply_property_provenance(
            &name,
            PropertyProvenance {
                taint: TaintOutcome::Set(node.range()),
                unpinned: UnpinnedOutcome::Set(UnpinnedRoot::UnsupportedCondition(
                    format!("<{name}> body").into(),
                )),
                // The unpinned root above carries this refusal, and carries it
                // with the *right lifetime*: a later clean unconditional
                // overwrite discharges it, because the final value is then one
                // we computed from ordinary text and the two sides agree.
                // Recording it in the refused channel as well would outlive
                // that discharge (see [`RefusedOutcome::Keep`] at the
                // clean-write site) and decline an import point MSBuild decides
                // the same way — the mark there answers a different question, about
                // values that may rest on content the walk hid.
                refused: RefusedOutcome::Keep,
                stale: StaleOutcome::Keep,
            },
        );
        return;
    };
    // While `define_context` is set (a user `<DefineConstants>` write), any
    // uncertainty `state.expand`/`push` raises here flags
    // `define_constants_uncertain` — except the value's own undefined read of
    // `$(DefineConstants)` (see `is_define_self_reference`), which is
    // recognised only because `in_define_value` is set: an unsupported
    // expression / item / metadata ref diverges (residual/refused), an
    // undefined non-self ref may be set in the real build, a property that
    // copied `$(DefineConstants)` may carry another doubt behind that root, and
    // an undefined self-ref matches the define set's view.
    let prev_in_value = state.in_define_value;
    state.in_define_value = true;
    let value_uses_sdk_taint = state.raw_uses_sdk_package_taint(&raw);
    let expansion = state.expand_property_pass_value(&raw, node.range(), &name);
    state.in_define_value = prev_in_value;
    if !expansion.throws.is_empty() {
        let reached = rejection::reach_is_certain(state) && own_gate(state) == Some(true);
        let expressions = expansion.throws.clone();
        rejection::judge_throwing_expression(
            state,
            expressions,
            reached,
            node.range(),
            rejection::text_at(node, None),
        );
    }
    let value_taints_property = condition_taints_property
        || value_uses_sdk_taint
        || (state.in_sdk_subtree && expansion.had_issue());
    let preserve_existing_sdk_taint =
        had_prior_sdk_package_taint && (write_condition_maybe_wrong || expansion.had_issue());
    if expansion.had_unsupported {
        // The substituted value contains residual `$(...)` text from an
        // expression we couldn't evaluate. Storing it would smuggle
        // unevaluated MSBuild syntax into downstream paths. But we also
        // can't leave any *prior* binding in place: MSBuild would have
        // overwritten the old value with whatever the new expression
        // produced, never the old value, so trusting the stale entry
        // would diverge from MSBuild just as much as trusting the
        // residual. Remove any existing binding so the next reference
        // emits Undefined, and forget any prior project-side write so
        // the tainted name doesn't appear in `properties`.
        state.lookup.unbind(&name);
        state.written.remove(&lower);
        let taint = TaintOutcome::after_write(
            value_taints_property || state.in_sdk_subtree,
            node.range(),
            preserve_existing_sdk_taint,
        );
        state.apply_property_provenance(
            &name,
            PropertyProvenance {
                taint,
                unpinned: UnpinnedOutcome::Clear,
                // The real build stores the value we refused to compute, so
                // later reads that rest on this name are not exact (C.2b).
                refused: RefusedOutcome::Set,
                stale: StaleOutcome::Keep,
            },
        );
        return;
    }
    // Item-list (`@(Items)`) and metadata (`%(Identity)`) references
    // survive substitution untouched — they're not `$(...)`. The
    // properties map is documented as evaluated project state, so
    // recording an unevaluated `@(...)` here would silently lie. Mirror
    // the diagnostics path used for Include attributes and refuse the
    // write. We diagnose item refs first to match how Include
    // attributes order the checks; the categorisation matters less than
    // emitting *some* diagnostic that flips `is_partial`.
    if contains_item_reference(expansion.value.ignoring_trust().as_escaped()) {
        state.push(
            DiagnosticKind::UnresolvedItemReference {
                reference: expansion.value.ignoring_trust().as_escaped().to_string(),
            },
            node.range(),
        );
        state.lookup.unbind(&name);
        state.written.remove(&lower);
        let taint = TaintOutcome::after_write(
            value_taints_property || state.in_sdk_subtree,
            node.range(),
            true,
        );
        state.apply_property_provenance(
            &name,
            PropertyProvenance {
                taint,
                unpinned: UnpinnedOutcome::Clear,
                // The real build stores the value we refused to compute, so
                // later reads that rest on this name are not exact (C.2b).
                refused: RefusedOutcome::Set,
                stale: StaleOutcome::Keep,
            },
        );
        return;
    }
    if contains_metadata_reference(expansion.value.ignoring_trust().as_escaped()) {
        state.push(
            DiagnosticKind::UnresolvedMetadataReference {
                reference: expansion.value.ignoring_trust().as_escaped().to_string(),
            },
            node.range(),
        );
        state.lookup.unbind(&name);
        state.written.remove(&lower);
        let taint = TaintOutcome::after_write(
            value_taints_property || state.in_sdk_subtree,
            node.range(),
            true,
        );
        state.apply_property_provenance(
            &name,
            PropertyProvenance {
                taint,
                unpinned: UnpinnedOutcome::Clear,
                // The real build stores the value we refused to compute, so
                // later reads that rest on this name are not exact (C.2b).
                refused: RefusedOutcome::Set,
                stale: StaleOutcome::Keep,
            },
        );
        return;
    }
    // Pin bookkeeping: a value that leaned on an undefined reference or an
    // unpinned property records that root; a clean value written under a
    // gate we couldn't pin down (its own, or the containing group's)
    // records the GATE's root — the write may not happen in a real build,
    // leaving a different value live. A clean value under a clean gate
    // re-pins.
    let gate_unpinned_root = if own_condition_maybe_wrong {
        state
            .unpinned_root_from_recent_diagnostics(diagnostics_before_condition)
            .or_else(|| {
                attribute(node, "Condition")
                    .as_deref()
                    .map(|c| UnpinnedRoot::UnsupportedCondition(c.into()))
            })
    } else if inherited_condition_maybe_wrong {
        inherited_unpinned_root.cloned()
    } else {
        None
    };
    let unpinned_by = expansion.unpinned_root.clone().or(gate_unpinned_root);
    let stale_by = expansion.value.trust().stale().cloned().or_else(|| {
        attribute(node, "Condition")
            .and_then(|condition| state.trust_for_raw(&condition).stale().cloned())
            .or_else(|| state.enclosing_condition_stale.clone())
    });
    // Unlike the unevaluable-value paths above, a cleanly-expanded value
    // under a pinned gate is exact even inside an SDK file: the property
    // pass computes the same final value MSBuild would, so plain SDK
    // provenance is not a taint. Only `value_taints_property`'s targeted
    // conditions (an untrusted gate, tainted input, or an expansion issue
    // inside the SDK) poison the write.
    let provenance = PropertyProvenance {
        taint: TaintOutcome::after_write(
            value_taints_property,
            node.range(),
            preserve_existing_sdk_taint,
        ),
        unpinned: UnpinnedOutcome::after_write(unpinned_by, write_condition_maybe_wrong),
        // A clean value under a clean gate re-pins the *unpinned* channel but
        // leaves a prior refusal standing. Its reader, a `Directory.Build.*`
        // import point ([`directory_build`]), consumes the mark mid-walk, so a
        // discharge here is sound only if that reader sees every way the new
        // value may rest on content the walk hid — which is what the stale
        // channel below records. Discharging on that basis is a separate
        // change, not made here.
        refused: RefusedOutcome::Keep,
        // A value computed from a stale one is stale; so is one whose own
        // condition read one (the scan, since a condition short-circuits), or
        // an enclosing group's or `<Choose>`'s that let it run. The reader is
        // a `Directory.Build.*` import point ([`directory_build`]).
        stale: StaleOutcome::after_write(stale_by, write_condition_maybe_wrong),
    };
    // A rewrite of a refused name whose value is the project's own
    // (`State::rewritten_after_refusal`): clean, and reading no name whose
    // refusal no such rewrite discharged (a toolset seed in a refused slot,
    // the name itself before this write).
    let rewrites_a_refusal = state.lookup.trust(&name).refused()
        && !provenance.is_doubtful()
        && !properties::property_references(&raw).any(|read| {
            state.lookup.trust(read).refused()
                && !state
                    .rewritten_after_refusal
                    .contains(&read.to_ascii_lowercase())
        });
    let (value, carried) = expansion.value.into_parts();
    state.write_property(&name, value, provenance);
    // The mark describes the name's binding now: a later write that does not
    // qualify (a copy of a seed over the rewrite) takes it away.
    if rewrites_a_refusal {
        state.rewritten_after_refusal.insert(lower.clone());
    } else {
        state.rewritten_after_refusal.remove(&lower);
    }
    // The verdict above is computed from the value's text (the reference
    // scan) and the write's gate; the value itself carries the trust of what
    // its expansion actually read. The stored trust must hold everything the
    // reads carried — a checked mirror of the scan against the expansion.
    debug_assert!(
        carried.is_held_by(state.trust_of(&name)),
        "the write of {name} stores less doubt than its value carried: \
         carried {carried:?}, stored {:?}",
        state.trust_of(&name)
    );
    state.written.insert(lower.clone(), name.clone());
}

/// Result of evaluating a node's `Condition` attribute.
enum CondGate {
    /// No condition, or a condition that evaluated to true. Walk the
    /// node's contents.
    Run,
    /// Condition evaluated to false. Skip the node silently — MSBuild
    /// would have done the same, and a "successful exclusion" is not
    /// a divergence to report.
    Skip,
    /// Condition couldn't be evaluated within our grammar (plan D5
    /// "fail loudly"). Caller must emit
    /// [`DiagnosticKind::UnsupportedCondition`] AND skip the node —
    /// proceeding as if true would silently leak items / properties
    /// MSBuild might have excluded.
    Unsupported,
}

fn evaluate_condition(
    node: Node<'_, '_>,
    current_file_dir: &Path,
    state: &mut State<'_>,
) -> CondGate {
    evaluate_condition_with_exemptions(node, current_file_dir, state, &[])
}

/// The `<PropertyGroup>` variant of [`evaluate_condition`]: the names the
/// group's children write are default-fill exempt in the group's own
/// condition — see [`evaluate_condition_with_exemptions`].
fn evaluate_property_group_condition(
    node: Node<'_, '_>,
    current_file_dir: &Path,
    state: &mut State<'_>,
) -> CondGate {
    let written_names: Vec<String> = node
        .children()
        .filter(Node::is_element)
        .map(|child| child.tag_name().name().to_string())
        .collect();
    evaluate_condition_with_exemptions(node, current_file_dir, state, &written_names)
}

/// `self_default_names`: property names whose *undefined* reads in this
/// condition are the MSBuild default-fill idiom —
/// `<X Condition="'$(X)' == ''">default</X>` (or the group-level
/// `<PropertyGroup Condition="'$(Configuration)' == ''">` variant) — and
/// therefore deterministic rather than a divergence risk: under this
/// walker's environment model (caller `extra_properties` ARE the
/// environment; a name absent from them and never written is genuinely
/// unset) an undefined self-name means the default
/// fires, exactly as in a real build. Only the *undefined* case is
/// exempt: a defined-but-unpinned self-name still re-surfaces its root
/// below, because there the stored value itself is untrustworthy.
/// The SDK relies on this idiom pervasively (`NuGet.props` gates every
/// `Directory.Packages.props` discovery property with it), and flagging
/// it would leave those writes unpinned and the central import refused.
///
/// "Never written" is a precondition, not a description of the shape, so a
/// name whose write the walk *refused* ([`Trust::refused`]) is not
/// exempt: there the emptiness is our failure to compute a value rather than a
/// fact about the real build, and MSBuild — holding the value it did compute —
/// takes the opposite branch of the very condition the exemption calls
/// deterministic. Nor is any name once the walk has passed content it could
/// not see ([`State::walk_opaque`]), which may have written it;
/// [`State::self_default_absence_is_a_fact`] is the whole precondition.
fn evaluate_condition_with_exemptions(
    node: Node<'_, '_>,
    current_file_dir: &Path,
    state: &mut State<'_>,
    self_default_names: &[String],
) -> CondGate {
    let cond = attribute(node, "Condition");
    let Some(cond) = cond.as_deref() else {
        return CondGate::Run;
    };
    let mut eval = if state.follow_imports {
        let exists = |path: &str| condition_exists(state.observer, path, current_file_dir);
        condition::evaluate_at(
            cond,
            &state.lookup,
            Some(condition::Probes {
                exists: &exists,
                observer: state.observer,
            }),
            state.condition_site(),
        )
    } else {
        condition::evaluate_at(cond, &state.lookup, None, state.condition_site())
    };
    // The undefined names the evaluation visited, before the exemptions below
    // vouch for some of them.
    let visited_undefined = eval.undefined_properties.clone();
    // Two carve-outs from the exemption. `DefineConstants`: the define
    // machinery deliberately does not model the SDK's own define
    // manipulation, so an undefined `$(DefineConstants)` here does NOT
    // mean "empty in a real build" (the SDK sets e.g. DEBUG) — see
    // `define_constants_self_reference_in_a_condition_is_uncertain`.
    // And any occurrence *outside* an empty-literal comparison
    // (`'$(X)' != 'bar'`, `Exists('$(X)')`, …): only the is-it-set shape
    // is the default-fill idiom; everything else is a genuine branch
    // decision on the unknown value.
    let outside_empty_comparison = eval.undefined_outside_empty_comparison.clone();
    eval.undefined_properties.retain(|name| {
        name.eq_ignore_ascii_case("DefineConstants")
            || outside_empty_comparison
                .iter()
                .any(|n| n.eq_ignore_ascii_case(name))
            || !self_default_names
                .iter()
                .any(|written| written.eq_ignore_ascii_case(name))
            || !state.self_default_absence_is_a_fact(name)
    });
    // C.2b: an undefined name the walk can prove is undefined in the
    // real build too substitutes to exactly the "" the evaluation used —
    // the True/False outcome is exact, not a divergence. Drop such names
    // before the carve-outs and diagnostics below so the gate reads as
    // trusted. (`DefineConstants` and `TargetFramework` never pass the
    // guard — see `undefined_read_is_exact`'s carve-outs.)
    eval.undefined_properties
        .retain(|name| !state.undefined_read_is_exact(name));
    // A condition reading an *unpinned* property (see [`Trust::unpinned`])
    // may take the other branch in a real build — the same risk as a direct
    // undefined reference, invisible to `condition::evaluate` because the
    // property is defined. Collect the roots first so both the diagnostics
    // and the compile carve-outs below see them; downstream maybe-wrong
    // detection (which watches the diagnostics emitted here) then treats the
    // gate accordingly.
    let mut unpinned_roots: Vec<UnpinnedRoot> = Vec::new();
    for reference in properties::property_references(cond) {
        let Some(root) = state.trust_of(reference).unpinned().cloned() else {
            continue;
        };
        if let Some(name) = root.undefined_name()
            && eval
                .undefined_properties
                .iter()
                .any(|n| n.eq_ignore_ascii_case(name))
        {
            continue;
        }
        if !unpinned_roots
            .iter()
            .any(|seen| seen.to_diagnostic() == root.to_diagnostic())
        {
            unpinned_roots.push(root);
        }
    }
    // Neither kind of unknown matters to a condition the values held exactly
    // decide on their own: no value of the unknowns can move it, so there is
    // no divergence to report (see `State::condition_trust`).
    if matches!(
        eval.outcome,
        condition::Outcome::True | condition::Outcome::False
    ) && state.condition_is_decided_exactly(cond, Some(current_file_dir), &|name| {
        // A visited name is exact exactly when an exemption above removed it;
        // an unvisited one gets the plain test (the self-default exemption is
        // only ever granted to a read the evaluation actually made).
        if visited_undefined
            .iter()
            .any(|n| n.eq_ignore_ascii_case(name))
        {
            !eval
                .undefined_properties
                .iter()
                .any(|n| n.eq_ignore_ascii_case(name))
        } else {
            state.undefined_read_is_exact(name)
        }
    }) {
        unpinned_roots.clear();
        eval.undefined_properties.clear();
    }
    // Inside a Compile context this condition decides whether source files
    // compile, and it only resolved by treating unknown properties as "" (or
    // leaning on an unpinned value) — so the include/exclude verdict may be
    // wrong. Record the correctness carve-out (separately surfaceable, e.g.
    // by the LSP's compile-uncertainty warning) *before* the flat
    // per-property diagnostics below.
    if state.compile_context {
        let mut undefined_names = eval.undefined_properties.clone();
        let mut unpinned_unsupported = false;
        for root in &unpinned_roots {
            match root {
                UnpinnedRoot::Undefined { name, .. } => undefined_names.push(name.to_string()),
                UnpinnedRoot::UnsupportedCondition(_) => unpinned_unsupported = true,
            }
        }
        if !undefined_names.is_empty() {
            state.record_compile_condition_uncertainty(
                cond,
                CompileConditionReason::UndefinedProperties(undefined_names),
                node.range(),
            );
        }
        if unpinned_unsupported {
            state.record_compile_condition_uncertainty(
                cond,
                CompileConditionReason::Unsupported,
                node.range(),
            );
        }
        // A condition reading a value hidden content may have rewritten
        // ([`Trust::stale`]) may take the other branch in the real build, as
        // the `Include` reading one may name other files (`expand_inner`).
        // Nothing decides such a condition exactly: a stale value exists only
        // once the walk is opaque, where `condition_is_decided_exactly` vouches
        // for nothing.
        let stale = properties::property_references(cond)
            .find_map(|reference| state.trust_of(reference).stale().cloned());
        if let Some(stale) = stale {
            state.items_uncertain = true;
            state.record_compile_item_uncertainty(
                CompileItemUncertaintyCauseKind::StaleValue {
                    reference: cond.to_string(),
                    hidden_by: crate::UntrustedCause::of_opacity(&stale),
                },
                node.range(),
            );
        }
    }
    // Surface every undefined `$(...)` reference the condition relied
    // on as an UndefinedProperty diagnostic. Plan D5: a condition we
    // *could* evaluate but only by treating an unknown property as ""
    // is a divergence risk — MSBuild may have the value, we don't —
    // and the user needs to know. We only emit these for True/False;
    // for Unsupported the `condition::evaluate` contract guarantees
    // an empty list, since the caller is about to emit
    // UnsupportedCondition which subsumes the per-property concern.
    // Unpinned roots surface alongside, for the same reason.
    for root in unpinned_roots {
        state.push_root(root, node.range());
    }
    for name in eval.undefined_properties {
        state.push_undefined_read(name, node.range());
    }
    // MSBuild throws on an illegal condition it evaluates, and the whole
    // project with it. The item pass judges its conditions group by group
    // instead ([`rejection::judge_deferred`]): MSBuild evaluates some the walk
    // does not.
    if state.item_pass.is_none() {
        let reached = rejection::reach_is_certain(state);
        rejection::judge_condition_rejection(
            state,
            cond,
            eval.outcome,
            current_file_dir,
            reached,
            node.range(),
            rejection::text_at(node, Some("Condition")),
        );
    }
    match eval.outcome {
        condition::Outcome::True => CondGate::Run,
        condition::Outcome::False => CondGate::Skip,
        // An illegal condition is judged above as a rejection, which withdraws
        // what the walk publishes; the walk carries on past it as past an
        // unmodelled one, for the read set and the diagnostics.
        condition::Outcome::Illegal | condition::Outcome::Unsupported => CondGate::Unsupported,
    }
}

fn evaluate_property_condition(node: Node<'_, '_>, state: &mut State<'_>) -> CondGate {
    // MSBuild evaluates individual property-element conditions relative to the
    // entry project directory, even when the property was declared in an
    // imported props/targets file. This is deliberately not the same as the
    // containing `PropertyGroup` condition.
    let base_dir = state.entry_project_dir.clone();
    // The element's own name is default-fill exempt in its own condition
    // (`<X Condition="'$(X)' == ''">…`) — see
    // `evaluate_condition_with_exemptions`.
    let self_name = [node.tag_name().name().to_string()];
    evaluate_condition_with_exemptions(node, &base_dir, state, &self_name)
}

/// `Exists('…')` for one entry of its argument (decoded and trimmed), resolved
/// against `current_file_dir` as MSBuild resolves it
/// (`FunctionCallExpressionNode.ExpandArgumentAsFileList`): a `\` is a
/// separator, an unrooted entry is `Path.GetFullPath(Path.Combine(dir,
/// entry))`, and existence is .NET's ([`dotnet_io::file_or_directory_exists`]),
/// which collapses `..` as text and counts a dangling symlink.
pub(crate) fn condition_exists(observer: &Observer, path: &str, current_file_dir: &Path) -> bool {
    if path.is_empty() {
        return false;
    }
    let normalised = path.replace('\\', "/");
    let path = Path::new(&normalised);
    let resolved = if path.has_root() {
        path.to_path_buf()
    } else {
        current_file_dir.join(path)
    };
    dotnet_io::file_or_directory_exists(observer, &resolved)
}

fn emit_unsupported_condition(node: Node<'_, '_>, state: &mut State<'_>) {
    // The diagnostic carries the raw condition text so callers can
    // surface it to users without re-parsing — see
    // `DiagnosticKind::UnsupportedCondition`. We only reach this
    // path when `evaluate_condition` returned `Unsupported`, so the
    // attribute is present by construction.
    let cond = attribute(node, "Condition").unwrap_or_default();
    let cond: &str = &cond;
    // In a Compile context the unmodeled condition was treated as exclusionary,
    // so any gated Compile items were dropped — possibly wrongly. Record the
    // carve-out so a consumer can surface *why* the Compile set is incomplete.
    if state.compile_context {
        state.record_compile_condition_uncertainty(
            cond,
            CompileConditionReason::Unsupported,
            node.range(),
        );
    }
    state.push(
        DiagnosticKind::UnsupportedCondition {
            condition: cond.to_string(),
        },
        node.range(),
    );
}

/// Names MSBuild defines *before* evaluation starts from toolset or host
/// facts we don't model, so "undefined in our walk" never means "empty in
/// the real build". The `msbuild` prefix covers the whole reserved +
/// toolset + behavioural-variable family (`MSBuildBinPath`,
/// `MSBuildUserExtensionsPath`, `MSBUILDDISABLEFEATURESFROMVERSION`, …) —
/// over-matching a user property that merely starts with "msbuild" costs
/// a spurious degrade, never a wrong commit. `OS` is here for non-unix
/// hosts only (unix seeds it exactly); `DOTNET_HOST_PATH` is injected by
/// the dotnet muxer for its children, so a build run via `dotnet` sees it
/// even when the caller's snapshot lacks it; `LocalAppData` MSBuild seeds
/// from the profile when the environment lacks it
/// (`Utilities.GetEnvironmentProperties`), the one name it so seeds that
/// the prefix does not cover.
///
/// One pinned exception to the prefix: `MSBuildIsRestoring` (probed:
/// `[$(MSBuildIsRestoring)]` on the build/`-getProperty` entrypoint reads
/// empty under a scrubbed environment). NuGet's *restore* entrypoint
/// injects it as a global, but this walker models the build-time
/// evaluation — the same one the `-getItem` differential oracle sees —
/// where the name is genuinely undefined. `NuGet.props` gates early
/// import groups on it, so keeping it conservative would latch
/// [`State::walk_opaque`] at the top of every real SDK chain and blind
/// the entire downstream walk.
pub(crate) fn is_toolset_initial_property_name(lower: &str) -> bool {
    if lower == "msbuildisrestoring" {
        return false;
    }
    lower.starts_with("msbuild")
        || matches!(
            lower,
            "visualstudioversion"
                | "roslyntargetspath"
                | "os"
                | "dotnet_host_path"
                | "localappdata"
        )
}

/// What the caller's environment snapshot said about `MSBuildExtensionsPath`
/// (see [`State::env_extensions_path`]). MSBuild promotes the name from the
/// environment, so it is *not* in [`is_env_ignored_toolset_name`] — but
/// whether the promoted value then survives the toolset depends on the
/// toolset's version, which is unknown until an SDK resolves. So the value is
/// parked here and adjudicated in [`State::seed_toolset_properties`].
enum EnvExtensionsPath {
    /// The snapshot did not bind the name. Every toolset then computes the
    /// property from its own directory, so there is nothing version-specific
    /// to decide.
    Absent,
    /// The snapshot bound it exactly once, to this (escaped-domain) value.
    Value(String),
    /// The snapshot bound it under two or more spellings, and MSBuild's pick
    /// among case-colliding variables is unspecified (probed — see
    /// [`State::new`]). A toolset that overwrites the value makes the
    /// collision moot; one that honours it leaves us unable to say which
    /// value won.
    Unspecified,
}

/// Whether this toolset lets an *environment-supplied* `MSBuildExtensionsPath`
/// stand, keyed on the major version of a canonical .NET SDK version directory
/// (`…/sdk/<version>`). `None` when the directory does not name a version we
/// can read — we then know nothing about the toolset, and both answers would
/// be a guess.
///
/// MSBuild ≤ 17 promotes the environment value and then *overwrites* it with
/// the toolset's own directory before the project is evaluated; MSBuild 18
/// leaves it standing, so it steers the `Sdk.props` import of
/// `$(MSBuildExtensionsPath)\$(MSBuildToolsVersion)\Microsoft.Common.props`.
/// Probed one SDK at a time —
/// `MSBuildExtensionsPath=/SPOOF dotnet msbuild -getProperty:MSBuildExtensionsPath`
/// reads the SDK version directory under 8.0.420 (MSBuild 17.11) and 9.0.315,
/// and `/SPOOF` under 10.0.301 (MSBuild 18.6). Not ChangeWave-gated (probed:
/// `MSBUILDDISABLEFEATURESFROMVERSION=17.0` does not restore the old behaviour
/// on 10.0.301), so the SDK's major version is the whole signal. Newer SDKs
/// are assumed to keep MSBuild 18's behaviour: it is the one that *respects*
/// its input, and a revert would be a breaking change.
///
/// The sibling names are not version-specific — the same sweep found
/// `MSBuildExtensionsPath32`, `MSBuildExtensionsPath64`,
/// `MSBuildUserExtensionsPath`, `MSBuildSDKsPath` and `VisualStudioVersion`
/// honouring the spoof on both 8.0.420 and 10.0.301.
fn toolset_honours_env_extensions_path(version_dir: &Path) -> Option<bool> {
    let major: u32 = version_dir
        .file_name()?
        .to_str()?
        .split('.')
        .next()?
        .parse()
        .ok()?;
    Some(major >= 10)
}

/// The product version compiled into the MSBuild of a canonical .NET SDK
/// version directory: `17.0` for MSBuild 17, `18.0` for MSBuild 18. It is the
/// value of two properties the toolset defines, `VisualStudioVersion`
/// ([`toolset_visual_studio_version`]) and `MSBuildAssemblyVersion`
/// ([`toolset_assembly_version`]). `None` for a directory that does not name
/// a release SDK of a major probed here.
///
/// It is not the version of a file in the directory: `Microsoft.Build.dll`
/// has assembly version `15.1.0.0`, and its file version (`18.9.11` under
/// 10.0.401) is `MSBuildVersion`.
///
/// Probed with `dotnet msbuild -getProperty:` and no `VisualStudioVersion` in
/// the environment. `VisualStudioVersion` reads `17.0` under 6.0.418, 8.0.425,
/// 9.0.200 and 9.0.315, and `18.0` under 10.0.109, 10.0.112, 10.0.300, 10.0.400
/// and 10.0.401. `MSBuildAssemblyVersion` reads `18.0` under 10.0.112 and
/// 10.0.401. A prerelease commits only where its exact version was probed
/// ([`PROBED_PRERELEASE_PRODUCT_VERSIONS`]): a preview SDK can ship the
/// previous MSBuild major (the early .NET 10 previews carried MSBuild 17), and
/// an unprobed major may have moved on.
/// `tests/toolset_visual_studio_version_diff.rs` holds both properties to the
/// MSBuild of every SDK the devshell installs.
fn toolset_product_version(version_dir: &Path) -> Option<&'static str> {
    let name = version_dir.file_name()?.to_str()?;
    if let Some((_, value)) = PROBED_PRERELEASE_PRODUCT_VERSIONS
        .iter()
        .find(|(version, _)| *version == name)
    {
        return Some(value);
    }
    let parts: Vec<&str> = name.split('.').collect();
    let is_release = parts.len() == 3
        && parts
            .iter()
            .all(|part| !part.is_empty() && part.bytes().all(|b| b.is_ascii_digit()));
    if !is_release {
        return None;
    }
    match parts[0].parse::<u32>().ok()? {
        6 | 8 | 9 => Some("17.0"),
        10 => Some("18.0"),
        _ => None,
    }
}

/// Prerelease SDKs whose MSBuild's product version was probed (as for
/// [`toolset_product_version`]): SDK 11.0.100-rc.1.26425.128 ships MSBuild
/// 18.11.0, whose `VisualStudioVersion` and `MSBuildAssemblyVersion` are
/// `18.0`.
const PROBED_PRERELEASE_PRODUCT_VERSIONS: &[(&str, &str)] = &[("11.0.100-rc.1.26425.128", "18.0")];

/// The `VisualStudioVersion` a canonical .NET SDK version directory's toolset
/// defines: MSBuild's compiled-in `CurrentVisualStudioVersion`, which is its
/// product version ([`toolset_product_version`]). `None` (the read stays
/// undefined and declines) where that is not probed.
pub(crate) fn toolset_visual_studio_version(version_dir: &Path) -> Option<&'static str> {
    toolset_product_version(version_dir)
}

/// The `MSBuildAssemblyVersion` a canonical .NET SDK version directory's
/// toolset defines: its product version ([`toolset_product_version`]), not
/// the version of the MSBuild assembly. `None` (the read stays undefined and
/// declines) where that is not probed.
///
/// The name is reserved. A project write to it is MSB4004, a `-p:` of it is
/// MSB4177, and an environment variable of the name is ignored (each probed
/// under 10.0.401), so nothing displaces the toolset's value.
pub(crate) fn toolset_assembly_version(version_dir: &Path) -> Option<&'static str> {
    toolset_product_version(version_dir)
}

/// The property names MSBuild defines, non-empty, before any project text is
/// evaluated: the toolset seeds of [`State::seed_toolset_properties`], among
/// them `VisualStudioVersion` and `MSBuildAssemblyVersion` (each seeded only
/// where the SDK's version says what the toolset defines), and the names
/// MSBuild's evaluator seeds from the process's profile when the environment
/// lacks them (`Utilities.GetEnvironmentProperties`: `LocalAppData`, the
/// extension paths, and `MSBuildUserExtensionsPath` under the first).
/// Lowercase.
///
/// Whenever the walk holds no value for one of these, the real build still
/// does, so the absence is never a fact (see
/// [`State::self_default_absence_is_a_fact`]): the SDK's
/// `<VisualStudioVersion Condition="'$(VisualStudioVersion)' == ''">10.0</…>`
/// in `Microsoft.Common.CurrentVersion.targets` would otherwise commit `10.0`
/// where MSBuild 18 reads `18.0`. `toolset_predefined_names_diff` holds the
/// list to MSBuild both ways: every name here is defined in an empty project,
/// and every name the SDK self-defaults that MSBuild predefines is here.
pub(crate) const TOOLSET_PREDEFINED_NAMES: &[&str] = &[
    "msbuildtoolspath",
    "msbuildbinpath",
    "msbuildtoolsversion",
    "msbuildruntimetype",
    "msbuildassemblyversion",
    "msbuildextensionspath",
    "msbuildextensionspath32",
    "msbuildextensionspath64",
    "msbuildsdkspath",
    "visualstudioversion",
    "localappdata",
    "msbuilduserextensionspath",
];

fn is_toolset_predefined_name(lower: &str) -> bool {
    TOOLSET_PREDEFINED_NAMES.contains(&lower)
}

/// Toolset-computed property names MSBuild *overwrites* after folding the
/// environment in, so a same-named environment variable is invisible to
/// projects. Probed one name at a time against dotnet msbuild 10.0.300
/// (spoof each via the environment, read it back): these read their real
/// toolset values, while — notably — `MSBuildExtensionsPath{,32,64}`,
/// `MSBuildUserExtensionsPath`, `MSBuildSDKsPath`,
/// `MSBuildFrameworkToolsRoot`, `MSBuildAllProjects`,
/// `MSBuildSemanticVersion`, `MSBuildFileVersion`, `VisualStudioVersion`,
/// and `OS` all honour the spoof, so they must stay promotable. Most of these
/// names are host or toolset facts this crate does not know, and stay unseeded,
/// so reads surface as undefined — conservative. Two are seeded where the walk
/// does know them: `MSBuildAssemblyVersion` from a probed per-SDK table
/// ([`toolset_assembly_version`]), and `MSBuildStartupDirectory` only for an
/// evaluation of a process the caller launches, which hands the walk the
/// directory it starts the process in ([`startup_directory_seed`]). An
/// evaluation of a build nobody launched has no such directory, and leaves the
/// name undefined.
///
/// Lowercase, matched against the lowercased variable name: the property
/// table is case-insensitive, so the toolset overwrite displaces every
/// spelling.
///
/// `DOTNET_HOST_PATH` is here for the same reason one step earlier in the
/// pipeline: the `dotnet` *host* rewrites it to the muxer it actually selected
/// before MSBuild is even loaded, so the value our caller inherited never
/// reaches the evaluation. Probed: `DOTNET_HOST_PATH=SPOOF dotnet msbuild …`
/// reads the real dotnet path, not `SPOOF`. The F# SDK's own targets read the
/// property, so promoting the inherited value would commit a wrong path.
fn is_env_ignored_toolset_name(lower: &str) -> bool {
    matches!(
        lower,
        "msbuildbinpath"
            | "msbuildtoolspath"
            | "msbuildtoolsversion"
            | "msbuildruntimetype"
            | "msbuildassemblyversion"
            | "msbuildversion"
            | "msbuildprogramfiles32"
            | "msbuildnodecount"
            | "msbuildstartupdirectory"
            | "msbuildloadmicrosofttargetsreadonly"
            | "roslyntargetspath"
            | "dotnet_host_path"
    )
}

/// The `MSBuildStartupDirectory` of a build whose process starts in `dir`:
/// the directory as the file system resolves it, spliced raw, or `None` where
/// the walk cannot say.
///
/// MSBuild reads the process's working directory, which is the physical
/// directory: started through a symlink to `…/real`, it reports `…/real`. So
/// `dir` is canonicalised, through the observer, and retargeting a link on
/// the way invalidates the evaluation. The value has no trailing separator,
/// and is raw text in the escaped domain, as the `MSBuildThisFile*` names are
/// ([`properties::this_file_seeds`]): started in a directory named
/// `a%20b;c`, `$(MSBuildStartupDirectory)` reads `…/a b;c`, and an `Include`
/// of it splits at the `;`. Each probed against `dotnet msbuild` and held to
/// the oracle by `tests/startup_directory_diff.rs`.
///
/// `None`, so that the name stays unset and its reads inexact
/// ([`is_toolset_initial_property_name`]), for a `dir` that is not rooted
/// (which would name a directory relative to this process's own), one that
/// does not resolve or whose resolution is not UTF-8, and off Unix, where
/// nothing has graded how the working directory resolves links.
fn startup_directory_seed(observer: &Observer, dir: &Path) -> Option<Escaped> {
    if !cfg!(unix) || !dir.has_root() {
        return None;
    }
    let physical = observed::canonicalize(observer, dir).ok()?;
    Some(Escaped::from_xml(physical.to_str()?))
}

/// The names MSBuild treats as *reserved*, as MSBuild spells them: the one
/// statement of the set in this crate, transcribed from
/// `ReservedPropertyNames` (dotnet/msbuild `src/Build/ReservedPropertyNames.cs`,
/// matched with `MSBuildNameIgnoreCaseComparer`). `tests/reserved_global_diff.rs`
/// holds it to the installed MSBuild's own table, read by reflection, in both
/// directions.
///
/// MSBuild refuses a reserved name as a global property
/// (`ArgumentException`; MSB4177 from the command line), so
/// `validate_inputs` rejects a caller's extra property of one.
///
/// `Utilities.GetEnvironmentProperties` filters the environment against this
/// whole set — `!ReservedPropertyNames.IsReservedProperty(name)` — so a
/// reserved name in the environment is never promoted, *including* names this
/// crate does not model and leaves undefined. Filtering only on the names we
/// happen to seed would let a spoofed `MSBuildThisFileFullPath` become
/// readable and commit an import path the real build never sees.
///
/// Deliberately absent, and so still promotable (each probed): `OS`,
/// `MSBuildExtensionsPath{,32,64}`, `MSBuildUserExtensionsPath`,
/// `MSBuildSDKsPath`, `MSBuildFrameworkToolsRoot`, `LocalAppData`,
/// `VisualStudioVersion` — MSBuild deliberately keeps these overridable from
/// the environment.
pub(crate) const MSBUILD_RESERVED_NAMES: [&str; 25] = [
    "MSBuildProjectDirectory",
    "MSBuildProjectDirectoryNoRoot",
    "MSBuildProjectFile",
    "MSBuildProjectExtension",
    "MSBuildProjectFullPath",
    "MSBuildProjectName",
    "MSBuildThisFileDirectory",
    "MSBuildThisFileDirectoryNoRoot",
    "MSBuildThisFile",
    "MSBuildThisFileExtension",
    "MSBuildThisFileFullPath",
    "MSBuildThisFileName",
    "MSBuildBinPath",
    "MSBuildProjectDefaultTargets",
    "MSBuildToolsPath",
    "MSBuildToolsVersion",
    "MSBuildRuntimeType",
    "MSBuildStartupDirectory",
    "MSBuildNodeCount",
    "MSBuildLastTaskResult",
    "MSBuildProgramFiles32",
    "MSBuildAssemblyVersion",
    "MSBuildVersion",
    "MSBuildInteractive",
    "MSBuildDisableFeaturesFromVersion",
];

/// Whether `name` is one of [`MSBUILD_RESERVED_NAMES`], compared as MSBuild
/// compares property names (`OrdinalIgnoreCase`, which for these ASCII names
/// folds ASCII letters only: `ı` and `ſ` are not `i` and `s` to it, and are
/// not valid in a property name anyway).
pub(crate) fn is_msbuild_reserved_name(name: &str) -> bool {
    MSBUILD_RESERVED_NAMES
        .iter()
        .any(|reserved| reserved.eq_ignore_ascii_case(name))
}

/// The `MSBUILDDISABLEFEATURESFROMVERSION` variable's value, looked up the way
/// the host would.
///
/// MSBuild reads it through `Environment.GetEnvironmentVariable`, whose name
/// lookup is case-sensitive on Unix but case-insensitive on Windows. Taking
/// `case_insensitive` as an argument rather than reading `cfg!(windows)` here
/// keeps both host behaviours testable from either host.
///
/// On Windows the environment block cannot hold two names differing only in
/// case, so the case-insensitive arm cannot be ambiguous.
pub(crate) fn changewave_env_value(
    environment: &HashMap<String, String>,
    case_insensitive: bool,
) -> Option<&str> {
    const NAME: &str = "MSBUILDDISABLEFEATURESFROMVERSION";
    if case_insensitive {
        environment
            .iter()
            .find(|(key, _)| key.eq_ignore_ascii_case(NAME))
            .map(|(_, value)| value.as_str())
    } else {
        environment.get(NAME).map(String::as_str)
    }
}

/// Whether a [`DiagnosticKind`] can itself carry Compile items into the
/// project, so emitting it makes the Compile set untrustworthy *even outside*
/// a [`State::compile_context`]. A failed import or unresolved SDK may have
/// contributed `<Compile>` items — or properties that gate them — we never saw.
///
/// The predicate itself is [`DiagnosticKind::hides_unseen_content`], public
/// because consumers reason about the same class: it is why the walk goes
/// opaque, why `items_uncertain` and `project_references_uncertain` are raised,
/// and (in the LSP) which of an uncertain project's causes also explain a
/// dropped `<ProjectReference>` edge set. One definition, so those cannot
/// disagree about what counts.
fn is_structural_compile_risk(kind: &DiagnosticKind) -> bool {
    kind.hides_unseen_content()
}

fn package_structural_uncertainty_from_compile(
    kind: &StructuralCompileItemUncertainty,
) -> StructuralPackageReferenceUncertainty {
    match kind {
        StructuralCompileItemUncertainty::ProjectSdkUnsupported { sdk } => {
            StructuralPackageReferenceUncertainty::ProjectSdkUnsupported { sdk: sdk.clone() }
        }
        StructuralCompileItemUncertainty::ExplicitSdkUnsupported { sdk } => {
            StructuralPackageReferenceUncertainty::ExplicitSdkUnsupported { sdk: sdk.clone() }
        }
        StructuralCompileItemUncertainty::SdkImportProjectUnresolved { sdk, project } => {
            StructuralPackageReferenceUncertainty::SdkImportProjectUnresolved {
                sdk: sdk.clone(),
                project: project.clone(),
            }
        }
        StructuralCompileItemUncertainty::ImportProjectUnresolved { project } => {
            StructuralPackageReferenceUncertainty::ImportProjectUnresolved {
                project: project.clone(),
            }
        }
        StructuralCompileItemUncertainty::UnsupportedChoose => {
            StructuralPackageReferenceUncertainty::UnsupportedChoose
        }
        StructuralCompileItemUncertainty::DirectoryBuildImportUndecided { project, .. } => {
            StructuralPackageReferenceUncertainty::ImportProjectUnresolved {
                project: project.clone(),
            }
        }
    }
}

/// Return the SDK version directory for the canonical .NET SDK
/// `…/sdk/<version>/Sdks/<name>/Sdk` layout. Only that layout justifies
/// tolerating shared SDK files outside the specific `Sdks/<name>` subtree (see
/// [`State::note_sdk_tolerance`]). Case-insensitive, matching the host FS.
/// `path` with `.` dropped and `..` popped, without asking the file system.
fn lexically_normal(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

pub(crate) fn dotnet_sdk_version_dir(root: &Path) -> Option<&Path> {
    if !root
        .file_name()
        .is_some_and(|n| n.eq_ignore_ascii_case("Sdk"))
    {
        return None;
    }
    let sdk_name_dir = root.parent()?;
    let sdks_dir = sdk_name_dir.parent()?;
    if !sdks_dir
        .file_name()
        .is_some_and(|n| n.eq_ignore_ascii_case("Sdks"))
    {
        return None;
    }
    let version_dir = sdks_dir.parent()?;
    let sdk_dir = version_dir.parent()?;
    if !sdk_dir
        .file_name()
        .is_some_and(|n| n.eq_ignore_ascii_case("sdk"))
    {
        return None;
    }
    Some(version_dir)
}

/// What a diagnostic does to [`State::define_constants_uncertain`] while in
/// [`State::define_context`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DefineAxis {
    /// It raises the flag.
    Doubts,
    /// It is a `<DefineConstants>` value's own read of `$(DefineConstants)`
    /// while undefined, which leaves the flag alone.
    SelfAppend,
}

/// Whether an undefined read of `name`, made by a `<DefineConstants>` value, is
/// the accumulator append idiom (`$(DefineConstants);FOO`). The define set is
/// the project's own view, without the defines the SDK adds in targets
/// ([`crate::ParsedProject::define_constants_uncertain`]), so the read is ""
/// in that view and must not flag [`State::define_constants_uncertain`],
/// while nothing else may have written it
/// ([`State::self_append_reads_the_sdk_free_view`]).
///
/// Every *other* undefined/unsupported reference in a define value or condition
/// is a genuine divergence (the referenced property may be set in the real
/// build, or the expression evaluated). So is a read of a property that copied
/// `$(DefineConstants)`: the root that copy carries is a single witness, and
/// may stand in for an independent cause it does not name (a gate on the
/// copy's write, say).
fn is_define_self_reference(name: &str) -> bool {
    name.eq_ignore_ascii_case("DefineConstants")
}

/// Whether a `<PropertyGroup>` writes `<DefineConstants>` — the trigger for
/// treating the group's own condition as preprocessor-affecting (case-
/// insensitive, matching MSBuild's property-name comparison).
fn property_group_writes_define_constants(node: Node<'_, '_>) -> bool {
    node.children()
        .filter(Node::is_element)
        .any(|c| c.tag_name().name().eq_ignore_ascii_case("DefineConstants"))
}

/// Whether a `<PropertyGroup>` writes a Central Package Management flag. A write
/// under an unevaluable condition leaves CPM state unknown, which changes how
/// the package set's versions are interpreted, so the group's condition is
/// package-affecting (case-insensitive, matching MSBuild's property-name
/// comparison).
fn property_group_writes_cpm_flag(node: Node<'_, '_>) -> bool {
    node.children()
        .filter(Node::is_element)
        .any(|c| is_cpm_flag_property_name(c.tag_name().name()))
}

fn is_cpm_flag_property_name(name: &str) -> bool {
    name.eq_ignore_ascii_case("ManagePackageVersionsCentrally")
        || name.eq_ignore_ascii_case("CentralPackageVersionsFileImported")
        || name.eq_ignore_ascii_case("CentralPackageVersionOverrideEnabled")
}

/// Whether a property-group child could write at all if its group ran.
/// `false` only on exact knowledge: the child's own condition evaluates
/// cleanly false, decided from values the walk is certain of (none stale),
/// so the write cannot happen regardless of the group gate.
fn property_child_could_write(child: Node<'_, '_>, state: &State<'_>) -> bool {
    let cond = attribute(child, "Condition");
    let Some(cond) = cond.as_deref() else {
        return true;
    };
    let eval = if state.follow_imports {
        let exists = |path: &str| condition_exists(state.observer, path, &state.entry_project_dir);
        condition::evaluate_at(
            cond,
            &state.lookup,
            Some(condition::Probes {
                exists: &exists,
                observer: state.observer,
            }),
            state.condition_site(),
        )
    } else {
        condition::evaluate_at(cond, &state.lookup, None, state.condition_site())
    };
    // An undefined read the walk can prove is undefined in the real build too
    // substitutes to exactly "" (C.2b), so a child gated on a provably-false
    // `'$(NoSuch)' != ''` is ruled out. A gate that reads a stale value is
    // ruled out only where it fails whatever the names the walk is not
    // certain of hold: the stale one may have been rewritten so that it holds
    // (#1037).
    let exists_dir = state.entry_project_dir.clone();
    let fails_whatever =
        || directory_build::decision_from_certain_inputs(state, cond, &exists_dir) == Some(false);
    let ruled_out = eval.outcome == condition::Outcome::False
        && if state.trust_for_raw(cond).stale().is_some() {
            fails_whatever()
        } else {
            state.condition_is_decided_exactly(cond, Some(&exists_dir), &|name| {
                state.undefined_read_is_exact(name)
            }) || fails_whatever()
        };
    !ruled_out
}

/// Mark every unprotected, possibly-writing child of a maybe-run/maybe-skipped
/// `<PropertyGroup>` with the group gate's provenance in one pass, so the two
/// channels cannot diverge on which children they cover: SDK-package taint
/// always (the gate could not be pinned down, so a child's final value is
/// untrustworthy for a later package read whichever branch our evaluation
/// took), and the unpinned `unpinned_root` when the gate itself was
/// unpinnable (so every item-pass read re-surfaces its root cause).
///
/// Protected names are exempt: MSBuild discards those writes without
/// consulting the gate at all, so a maybe-skipped write cannot change them —
/// marking one would falsely degrade a value the caller pinned. Children whose
/// own condition is cleanly false are exempt too — they cannot write whichever
/// way the group gate goes (see [`property_child_could_write`]).
fn mark_property_group_children_provenance(
    node: Node<'_, '_>,
    unpinned_root: Option<&UnpinnedRoot>,
    state: &mut State<'_>,
) {
    for child in node.children().filter(Node::is_element) {
        if !property_child_could_write(child, state) {
            continue;
        }
        let name = child.tag_name().name();
        if state.protected.contains(&name.to_ascii_lowercase()) {
            continue;
        }
        state.apply_property_provenance(
            name,
            PropertyProvenance {
                taint: TaintOutcome::Set(child.range()),
                unpinned: match unpinned_root {
                    Some(root) => UnpinnedOutcome::Set(root.clone()),
                    None => UnpinnedOutcome::Keep,
                },
                // A write we skipped rather than refused: we computed no value
                // here, but neither did we drop one we had.
                refused: RefusedOutcome::Keep,
                stale: StaleOutcome::Keep,
            },
        );
    }
}

fn diagnose_item_op(node: Node<'_, '_>, attr: &str, state: &mut State<'_>) -> bool {
    let Some(value) = attribute(node, attr) else {
        return false;
    };
    state.push(
        DiagnosticKind::UnsupportedItemOperation {
            operation: format!("{attr}={value}"),
        },
        node.range(),
    );
    true
}

/// Dispatch a `<Import>` element. In pure mode (`follow_imports=false`)
/// every import becomes an [`DiagnosticKind::UnresolvedImport`]; with
/// imports enabled we evaluate `Condition`, refuse `Sdk` attributes
/// (phase 7b territory — they require an SDK resolver), and finally
/// recurse into the referenced file via [`walk_external_file`].
fn handle_import(node: Node<'_, '_>, current_file_dir: &Path, state: &mut State<'_>) {
    if !state.follow_imports {
        // MSBuild evaluates the import's condition, which the pure walker
        // judges though it follows no import.
        let reached = rejection::reach_is_certain(state);
        rejection::judge_unwalked(node, current_file_dir, reached, state);
        let project = attribute(node, "Project")
            .as_deref()
            .unwrap_or("")
            .to_string();
        state.push(
            DiagnosticKind::UnresolvedImport { path: project },
            node.range(),
        );
        return;
    }
    follow_explicit_import(node, current_file_dir, state);
}

fn follow_explicit_import(node: Node<'_, '_>, current_file_dir: &Path, state: &mut State<'_>) {
    // The pre-scan in [`find_explicit_sdk_promotion`] may have already
    // promoted this body `<Import Sdk=X Project="Sdk.{props,targets}"/>`
    // to a root-equivalent splice position. Re-walking it here would
    // misplace `Sdk.targets`: its splice runs at the *bottom*, so a
    // body-position walk would register the file first and turn the
    // splice into the skipped duplicate. Silent skip mirrors MSBuild's
    // effective behaviour: the SDK chain only enters once, at splice
    // position.
    //
    // The skip is gated on "currently walking the entry project's
    // body": `state.hoisted_sdk_imports` is populated with ranges
    // into the *entry project's* XML, but `node.range()` is a byte
    // offset into whatever XML buffer the current frame is walking.
    // An imported file's `<Import>` that happens to share a byte
    // offset with a hoisted entry-project import must not get
    // silently dropped here. `import_site_span` is `None` exactly
    // while we're inside the entry project body — see [`State`].
    if state.import_site_span.is_none() && state.hoisted_sdk_imports.contains(&node.range()) {
        return;
    }
    // An SDK's `Directory.Build.*` import point is an ordinary import when the
    // walk decided it; when it did not, the fallback settles it here.
    if let Some(kind) = directory_build::point_kind(node, state)
        && let directory_build::Visit::Settled =
            directory_build::visit_point(node, kind, current_file_dir, state)
    {
        return;
    }
    // The import's own `Condition` gates whether it (and any Compile items /
    // gating properties it carries) is brought in. If we can't trust it — an
    // unsupported condition, or one relying on an undefined property — an
    // import we skip may leave the Compile and dependency sets incomplete, and
    // one we follow may be one the real build skips. That holds in an SDK file
    // too: the file it names may be a user's, or import one (#821).
    let route_decided = directory_build::gate_is_decided(node, current_file_dir, state);
    let prev_gate = state.import_gate_context;
    let prev_pkg_gate = state.package_import_gate_context;
    state.import_gate_context = true;
    state.package_import_gate_context = true;
    let diagnostics_before_gate = state.diagnostics.len();
    let gate = evaluate_condition(node, current_file_dir, state);
    state.note_package_uncertain_if_condition_uses_sdk_taint(node);
    state.import_gate_context = prev_gate;
    state.package_import_gate_context = prev_pkg_gate;
    // An import decided by an untrusted read may go the other way in a real
    // build, in an SDK file as anywhere: a skipped file could mutate the
    // reference list, and a followed file's references may not actually be
    // brought in — either way `project_references` can't be trusted. (A
    // gate we could not decide at all, or one outside our grammar, raised a
    // diagnostic in the gate context, which withdraws the list on its own
    // account.)
    if state.condition_reads_untrusted_value(node) {
        state.project_references_uncertain = true;
    }
    // An import gate we could not decide exactly (its evaluation raised
    // diagnostics, or it is outside the grammar) may bring in — or omit —
    // a whole file of property writes, whichever way we resolved it:
    // Skip may hide writes the real build performs, Run may perform
    // writes the real build skips. Either way no later undefined read
    // can claim exactness, and a write the followed file makes is one the
    // real build may not make (#791).
    let gate_raised_doubt =
        state.diagnostics.len() != diagnostics_before_gate || matches!(gate, CondGate::Unsupported);
    let undecided =
        gate_raised_doubt.then(|| state.latch_undecided_import_gate(node, diagnostics_before_gate));
    // A gate decided on a stale value may go the other way in the real
    // build, as an undecided one may (#1037).
    let stale_gate = if gate_raised_doubt {
        None
    } else {
        state.stale_gate_cause(node, route_decided)
    };
    match gate {
        CondGate::Run => {}
        CondGate::Skip => {
            // A gate the walk did not decide from certain inputs may hold in
            // the build, which then makes the import (#820).
            if gate_raised_doubt || !route_decided {
                rejection::undecided_import(node, current_file_dir, state);
            }
            // The file the walk did not see may run.
            if let Some(cause) = stale_gate {
                state.latch_walk_opaque((*cause).clone(), node.range());
            }
            return;
        }
        CondGate::Unsupported => {
            // Re-enter the gate context so the `UnsupportedCondition` flags.
            state.import_gate_context = true;
            state.package_import_gate_context = true;
            emit_unsupported_condition(node, state);
            state.import_gate_context = prev_gate;
            state.package_import_gate_context = prev_pkg_gate;
            rejection::undecided_import(node, current_file_dir, state);
            return;
        }
    }
    // A path named from a value the walk is not certain of may be another in
    // the build: what the walk loads from it, MSBuild may not, and its failure
    // to load is no claim ([`rejection`]).
    let path_certain = rejection::import_path_is_certain(node, state);
    let saved_path_certain = std::mem::replace(&mut state.taken_import_path_certain, path_certain);
    state.reach_doubted += usize::from(!path_certain);
    // A path named from a value content the walk could not see may have
    // rewritten names another file in the real build (#1037): what the walk
    // followed, MSBuild may not have, and what MSBuild followed, the walk
    // did not see.
    let path_stale = ["Project", "Sdk"].into_iter().find_map(|name| {
        attribute(node, name).and_then(|raw| state.trust_for_raw(&raw).stale().cloned())
    });
    directory_build::within_route(route_decided, state, |state| {
        directory_build::within_followed_import(undecided, state, |state| {
            follow_import_after_gate(node, current_file_dir, state);
        });
    });
    if let Some(cause) = path_stale {
        state.latch_walk_opaque((*cause).clone(), node.range());
    }
    state.reach_doubted -= usize::from(!path_certain);
    state.taken_import_path_certain = saved_path_certain;
}

/// [`follow_explicit_import`] once the import's own gate has let it through.
fn follow_import_after_gate(node: Node<'_, '_>, current_file_dir: &Path, state: &mut State<'_>) {
    // `<Import Sdk="Microsoft.NET.Sdk" Project="Sdk.props" />` (or
    // `Sdk.targets`) is MSBuild's explicit way to import the SDK in two
    // pieces, sidestepping the `<Project Sdk=...>` shorthand. We
    // resolve via the caller-supplied SDK resolver and walk the chosen
    // file *at this position in the body*. The two well-known stems
    // use the explicit `SdkPaths::{props, targets}` fields; any other
    // `Project` value is resolved against the SDK's directory exactly as
    // MSBuild resolves it: `Path.Combine(sdkResult.Path, project)` of the
    // attribute *as written*, then expanded, then
    // `FileUtilities.NormalizePath` (Evaluator.cs). So `..` may leave the
    // SDK directory — the Web SDK's `Sdk.Server.targets` imports
    // `Microsoft.NET.Sdk.Web.ProjectSystem`'s
    // `..\targets\Microsoft.NET.Sdk.Web.BeforeCommon.targets`, and the
    // Worker SDK the same directory's `DefaultItems.props` — and a
    // `Project` written rooted names its own file, while one a property
    // makes rooted is appended to the SDK directory. Neither confines what a
    // project can read: a plain `<Import Project=...>` reaches any path
    // already. A missing entry point surfaces as
    // `ImportFailed::NotFound` from the IO path. Without a resolver,
    // every Sdk import surfaces as `SdkResolverAbsent`.
    if let Some(sdk_name) = attribute(node, "Sdk").as_deref() {
        let Some(resolver) = state.sdk_resolver else {
            state.push(
                DiagnosticKind::SdkResolverAbsent {
                    name: sdk_name.to_string(),
                },
                node.range(),
            );
            // An SDK import we couldn't evaluate (no resolver) may have carried
            // default-item machinery; in a user-authored file that leaves the
            // Compile set incomplete. Inside the SDK tree Compile uncertainty is
            // tolerated, but dependency items could still be hidden.
            state.mark_structural_skip(
                StructuralCompileItemUncertainty::ExplicitSdkUnsupported {
                    sdk: sdk_name.to_string(),
                },
                node.range(),
            );
            return;
        };
        let resolution = match resolver(sdk_name, state.observer) {
            Ok(resolution) => resolution,
            Err(err) => {
                state.push(sdk_error_to_diagnostic(sdk_name, err), node.range());
                return;
            }
        };
        let project_attr_raw = attribute(node, "Project").unwrap_or_default();
        let project_attr_raw: &str = &project_attr_raw;
        // MSBuild expands `$(...)` in `Import` `Project` attributes
        // before resolving them. The two well-known stems are matched
        // against the *expanded* value so a project that writes
        // `Project="$(SdkPropsName)"` (with `SdkPropsName=Sdk.props`)
        // still picks the explicit field, and a project that uses a
        // property to switch SDK variants
        // (`Project="Sdk.$(Flavor).props"`) resolves to the expanded
        // relative path. Expansion issues (residual `$(...)` or
        // empty substitution) skip the import silently, mirroring the
        // non-SDK path below. A rooted path that keeps a `\` is declined
        // with them ([`sdk_import_keeps_a_rooted_backslash`]).
        let expansion = state.expand(&import_project_as_expanded(project_attr_raw), node.range());
        if expansion.had_issue()
            || expansion.unpinned_root.is_some()
            || sdk_import_keeps_a_rooted_backslash(
                project_attr_raw,
                expansion.value.ignoring_trust(),
                &resolution,
            )
        {
            // An SDK import whose Project path we couldn't resolve is dropped;
            // an *unpinned* path (assembled from a property the property pass
            // couldn't pin down) is just as ambiguous — a real build may
            // resolve a different file entirely, so best-effort following
            // would be an over-resolve.
            // it could have carried Compile items or gating properties (same
            // reasoning as the plain `<Import>` path). Inside the SDK tree
            // Compile uncertainty is tolerated, but dependency items could
            // still be hidden.
            state.mark_structural_skip(
                StructuralCompileItemUncertainty::SdkImportProjectUnresolved {
                    sdk: sdk_name.to_string(),
                    project: project_attr_raw.to_string(),
                },
                node.range(),
            );
            rejection::taken_import_with_undecided_path(node, current_file_dir, state);
            return;
        }
        // The expansion's trust was judged just above, through its scan-based
        // flags (`had_issue`, `unpinned_root`).
        let project_attr_unescaped = expansion.value.ignoring_trust().unescape();
        let project_attr = project_attr_unescaped.as_str();
        // An empty `Project` names no file: MSBuild fails the evaluation
        // (MSB4035 for a missing attribute; `Path.Combine` of the SDK
        // directory with "" names the directory itself, which no import
        // can load). Decline as the plain `<Import>` path does. A resolver
        // that returns no directory gives MSBuild none to name, and a
        // `Project` expanding to empty then imports nothing (the workload
        // locators), so only a resolved directory makes the failure certain.
        if project_attr.trim().is_empty() {
            // Judged before the skip below latches the walk opaque.
            if matches!(&resolution, SdkResolution::Roots(roots) if roots.is_empty()) {
                state.note_possible_rejection(
                    crate::RejectionCause::Import {
                        project: project_attr_raw.to_owned(),
                        gate_undecided: false,
                        why: crate::UnloadableImport::NoPath,
                    },
                    node.range(),
                );
            } else {
                state.note_unloadable_import(node, crate::UnloadableImport::NoPath);
            }
            state.push(
                DiagnosticKind::UnsupportedConstruct {
                    element: format!(
                        "Import Sdk={sdk_name:?} Project={project_attr_raw:?} \
                         (names no file, an MSBuild evaluation error)"
                    ),
                },
                node.range(),
            );
            state.mark_structural_skip(
                StructuralCompileItemUncertainty::SdkImportProjectUnresolved {
                    sdk: sdk_name.to_string(),
                    project: project_attr_raw.to_string(),
                },
                node.range(),
            );
            return;
        }
        // Commit only on a path spelt from a positive alphabet: ASCII
        // alphanumerics, `.`, `_`, `-`, `+` and the separators — every real
        // SDK's spelling. Collapsing `..` below erases the segment before it,
        // so a character MSBuild would act on there vanishes unseen: a `;`
        // splits MSBuild's list (`a.props;sub/../b.props` imports both), a
        // decoded NUL fails it (MSB4102), a wildcard globs, and whitespace
        // is trimmed. And the only escape admitted is `%2e`: MSBuild turns a
        // literal `\` into `/` before decoding, so a decoded `\` is no
        // separator when `..` collapses (`.%5c./..` pops `.\.` whole) yet is
        // one when the file opens — structure is decided in the escaped domain,
        // so any escape that could decode to structure declines. Outside the
        // alphabet, decline.
        if !sdk_project_in_alphabet(expansion.value.ignoring_trust().as_escaped(), project_attr) {
            state.push(
                DiagnosticKind::UnsupportedConstruct {
                    element: format!(
                        "Import Sdk={sdk_name:?} Project={project_attr_raw:?} \\
                         (a path character outside the modelled alphabet)"
                    ),
                },
                node.range(),
            );
            state.mark_structural_skip(
                StructuralCompileItemUncertainty::SdkImportProjectUnresolved {
                    sdk: sdk_name.to_string(),
                    project: project_attr_raw.to_string(),
                },
                node.range(),
            );
            state.note_unloadable_import(node, crate::UnloadableImport::PathUndecided);
            return;
        }
        // MSBuild accepts either separator on either platform, as for a
        // plain `<Import>`.
        let relative = project_attr.replace('\\', "/");
        // `NormalizePath` collapses `.`/`..` lexically but keeps a trailing
        // separator, and a path ending in one names a directory, which
        // MSBuild never imports (MSB4019; probed, `dotnet msbuild` 10.0.401:
        // `E.props/`, `E.props/./` and `E.props/x/../` fail, while `E.props/.`
        // and `E.props/x/..` end in no separator and import `E.props`).
        // `sdk_import_path` collapses the path, which drops the separator, so
        // refuse it here, from the text, rather than at the IO path.
        let names_directory = relative.ends_with('/');
        // `Path.Combine(root, Project)` runs on the attribute as written, `\`
        // already `/` (`ProjectImportElement.Project`'s `FixFilePath`), and
        // the expansion comes after: only a `Project` written rooted replaces
        // the root. One a property makes rooted is appended to it, and the
        // separator it doubles collapses in `NormalizePath` (probed,
        // `dotnet msbuild` 10.0.401: `Project="$(P)"` with `P=/abs/x.props`
        // names `…/Sdk//abs/x.props`).
        let under_root = sdk_project_under_root(project_attr_raw, &relative);
        let walk_under = |root: &Path, state: &mut State<'_>| {
            // MSBuild imports `Path.Combine(root, Project)` as an escaped
            // import expression, so the root is re-parsed too: a `$(` expands,
            // a `;` splits it into a list, `*`/`?` glob and `%XX` decodes. A
            // root holding one names something else to MSBuild; decline. A
            // `Project` written rooted takes the root's place.
            if !sdk_project_written_rooted(project_attr_raw) && sdk_root_is_reparsed(root) {
                state.push(
                    DiagnosticKind::UnsupportedConstruct {
                        element: format!(
                            "Import Sdk={sdk_name:?} Project={project_attr_raw:?} \
                             (the SDK root {} holds a character MSBuild re-parses \
                             in an import path)",
                            root.display()
                        ),
                    },
                    node.range(),
                );
                state.mark_structural_skip(
                    StructuralCompileItemUncertainty::SdkImportProjectUnresolved {
                        sdk: sdk_name.to_string(),
                        project: project_attr_raw.to_string(),
                    },
                    node.range(),
                );
                state.note_unloadable_import(node, crate::UnloadableImport::PathUndecided);
                return;
            }
            // `NormalizePath` is `GetFullPath`: a relative root resolves
            // against the working directory *before* `..` collapses, so a
            // leading `..` that `normalise` alone could not pop still climbs.
            let path = match sdk_import_path(root, under_root) {
                Ok(path) => path,
                Err(e) => {
                    state.push(
                        DiagnosticKind::ImportFailed {
                            path: root.join(under_root),
                            reason: ImportFailReason::Io {
                                message: e.to_string(),
                            },
                        },
                        node.range(),
                    );
                    return;
                }
            };
            if names_directory {
                state.push(
                    DiagnosticKind::ImportFailed {
                        path: path.join(""),
                        reason: ImportFailReason::NotFound,
                    },
                    node.range(),
                );
            } else {
                walk_external_file(&path, node.range(), state);
            }
        };
        match resolution {
            SdkResolution::Single(sdk_paths) => {
                // Tolerate this SDK's own files too — the
                // `Microsoft.NET.Sdk.Web` → base `Microsoft.NET.Sdk`
                // (sibling dir) case (P2.1).
                state.note_sdk_tolerance(&sdk_paths.root);
                // The two well-known stems are only meaningful for an
                // ordinary single-root SDK.
                match project_attr {
                    "Sdk.props" => walk_external_file(&sdk_paths.props, node.range(), state),
                    "Sdk.targets" => walk_external_file(&sdk_paths.targets, node.range(), state),
                    _ => walk_under(&sdk_paths.root, state),
                }
            }
            SdkResolution::Roots(roots) => {
                // MSBuild's multi-path resolver contract: import `Project`
                // relative to every returned root, in order (all sharing
                // this walk's state); zero roots contribute nothing and
                // that is *exact* — MSBuild treats an empty workload
                // resolver result the same way.
                for root in roots {
                    state.note_sdk_tolerance(&root);
                    walk_under(&root, state);
                }
            }
        }
        return;
    }
    let raw_path = attribute(node, "Project");
    let Some(raw_path) = raw_path.as_deref() else {
        // `<Import>` with no Project attribute is malformed; surfacing
        // as an UnsupportedConstruct keeps the diagnostic shape
        // uniform without inventing a new variant for this corner.
        state.push(
            DiagnosticKind::UnsupportedConstruct {
                element: "Import (no Project attribute)".to_string(),
            },
            node.range(),
        );
        state.note_unloadable_import(node, crate::UnloadableImport::NoPath);
        return;
    };
    let fixed_raw = import_project_as_expanded(raw_path);
    let expansion = state.expand(&fixed_raw, node.range());
    if expansion.had_issue() || expansion.unpinned_root.is_some() {
        // The expanded path has residual `$(...)`, substituted to "", or
        // leaned on an *unpinned* property (a value the property pass could
        // not pin down — a real build may resolve a different file entirely)
        // — every case is too ambiguous to follow safely. In a user-authored
        // file the import we just dropped could have contributed `<Compile>`
        // items, so the Compile set is no longer trustworthy. Inside the SDK
        // tree Compile uncertainty is tolerated, but the dropped import can
        // still hide dependency items.
        state.mark_structural_skip(
            StructuralCompileItemUncertainty::ImportProjectUnresolved {
                project: raw_path.to_string(),
            },
            node.range(),
        );
        rejection::taken_import_with_undecided_path(node, current_file_dir, state);
        return;
    }
    // The `Project` attribute is a semicolon-separated *list* of paths
    // (pinned against dotnet msbuild 10.0.300 with stub projects):
    // segments are whitespace-trimmed, empty segments are skipped — the
    // SDK's own `$(CustomAfterDirectoryBuildProps);…` accumulator idiom
    // yields a leading `;`, and a fully-empty list (`";"`) is a silent
    // no-op — files import left to right, a missing non-wildcard segment
    // fails the evaluation (MSB4019; our `ImportFailed` degrade), and each
    // segment may carry its own wildcard. The `;` split, trim, and
    // empty-segment skip all happen **in the escaped domain**, so an escaped
    // `%3b` stays data and does not split (see [`Escaped::split_list`]).
    //
    // One case the split alone gets wrong: an *empty or whitespace-only whole*
    // value (`Project=""`, or `$(Missing)` expanding exactly to "") is an
    // error in MSBuild (MSB4035/MSB4020), not a no-op — probed: `dotnet
    // msbuild -getProperty` on `<Import Project="$(Empty)"/>` exits 1. Only a
    // *separator-bearing* list whose entries are all empty (`";"`, the SDK's
    // possibly-empty `$(CustomAfterDirectoryBuildProps)` accumulator) is the
    // silent no-op. Distinguish by the presence of a `;` before splitting; the
    // empty whole value degrades structurally exactly as the residual/unpinned
    // path above does.
    // The expansion's trust was judged above, through its scan-based flags.
    let escaped = expansion.value.ignoring_trust().as_escaped();
    if escaped.trim().is_empty() && !escaped.contains(';') {
        // Judged before the skip below latches the walk opaque.
        state.note_unloadable_import(node, crate::UnloadableImport::NoPath);
        // Push the diagnostic too, not just the uncertainty: this branch
        // can be reached with a *clean* expansion (a literal `Project=""`,
        // or an exact undefined read substituting "" without any
        // diagnostic of its own — C.2b), and `is_partial` derives solely
        // from `diagnostics`, so silently returning would report full
        // fidelity for a project MSBuild refuses to evaluate.
        state.push(
            DiagnosticKind::UnsupportedConstruct {
                element: format!(
                    "Import Project={raw_path:?} (expands to an empty path, \
                     an MSBuild evaluation error)"
                ),
            },
            node.range(),
        );
        state.mark_structural_skip(
            StructuralCompileItemUncertainty::ImportProjectUnresolved {
                project: raw_path.to_string(),
            },
            node.range(),
        );
        return;
    }
    // A `\` written in the attribute is already `/` (`fixed_raw`); one a
    // property supplies is still `\` here, and MSBuild's Unix path
    // adjustment decides it for the whole expansion at once.
    let mut rewrites = None;
    for segment in expansion.value.ignoring_trust().split_list() {
        // Wildcard-ness is classified on the **escaped** segment, before
        // decoding (classify, then unescape — the same order item specs use).
        // An escaped `%2a` is a literal star in a filename, so
        // `star%2afile.props` imports that one file; decoding first would glob
        // it. A segment carrying an escaped wildcard beside a live one is
        // literal too, whole: `*.props%2a` imports the file named `*.props*`
        // ([`Escaped::is_filespec_wildcard`]). So a glob's decoded pattern has
        // no `*`/`?` that was data.
        let decoded = segment.unescape();
        if !adjustment_settles(escaped, &segment, &mut rewrites, state.observer) {
            decline_import_path(
                node,
                raw_path,
                "a `\\` a property supplies, which MSBuild's Unix path adjustment \
                 keeps or rewrites as its working directory decides",
                state,
            );
            continue;
        }
        // Every live `\` reads as a `/` from here on.
        if segment.is_filespec_wildcard() {
            // MSBuild collapses the path before it globs, so the directory
            // listed is the collapsed one. An escaped `\` reaches the glob as
            // a character the walk does not model there.
            if has_escaped_backslash(segment.as_escaped()) {
                decline_import_path(node, raw_path, "an escaped `\\` in a wildcard", state);
                continue;
            }
            follow_wildcard_import(
                &decoded.replace('\\', "/"),
                true,
                current_file_dir,
                node.range(),
                state,
            );
            continue;
        }
        // An escaped separator (`%2f`, `%5c`) is data when MSBuild decides
        // the path's structure and collapses `..` (`.%5c./..` pops `.\.`
        // whole), and the walk cannot say which file that names; decline,
        // as an SDK import does.
        if has_escaped_separator(segment.as_escaped()) {
            decline_import_path(node, raw_path, "an escaped path separator", state);
            continue;
        }
        // MSBuild collapses the path as one written with `/`
        // (`adjustment_settles`).
        let path = import_open_path(&current_file_dir.join(decoded.replace('\\', "/")), true);
        walk_external_file(&path, node.range(), state);
        // Record NuGet's central-package import point by its *shape* —
        // membership in `walked_files` afterwards means the walk genuinely
        // entered the file, on this import or an earlier one (failed
        // walks never insert; a duplicate-skipped one was inserted by
        // its first walk).
        if attribute(node, "Project")
            .as_deref()
            .and_then(simple_property_reference)
            .is_some_and(|name| name.eq_ignore_ascii_case("DirectoryPackagesPropsPath"))
        {
            let canon = canonicalise_or_normalise(state.observer, &path);
            if state.walked_files.contains(&canon) {
                state.walked_directory_packages_props_import = Some(canon);
            }
        }
    }
}

/// Whether an SDK import's expanded `Project` (`escaped`, and `unescaped`
/// decoded) is spelt from the alphabet the walk joins under an SDK root: ASCII
/// alphanumerics, `.`, `_`, `-`, `+`, the separators, and no escape but `%2e`
/// (`follow_import_after_gate` says why). Shared with the rejection judgement
/// ([`rejection`]), which must name the file the walk would.
fn sdk_project_in_alphabet(escaped: &str, unescaped: &str) -> bool {
    let escapes_only_dots = escaped.match_indices('%').all(|(at, _)| {
        escaped
            .get(at..at + 3)
            .is_some_and(|e| e.eq_ignore_ascii_case("%2e"))
    });
    escapes_only_dots
        && unescaped
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-' | '+' | '/' | '\\'))
}

/// Decline the plain import at `node`, whose `Project` is `raw_path`, for
/// `why`: MSBuild may load another file than the walk would, or none.
fn decline_import_path(node: Node<'_, '_>, raw_path: &str, why: &str, state: &mut State<'_>) {
    state.push(
        DiagnosticKind::UnsupportedConstruct {
            element: format!("Import Project={raw_path:?} ({why})"),
        },
        node.range(),
    );
    state.mark_structural_skip(
        StructuralCompileItemUncertainty::ImportProjectUnresolved {
            project: raw_path.to_string(),
        },
        node.range(),
    );
    state.note_unloadable_import(node, crate::UnloadableImport::PathUndecided);
}

/// Whether `escaped`, an import path in MSBuild's escaped domain, holds an
/// escaped separator (`%2f` or `%5c`, either case).
fn has_escaped_separator(escaped: &str) -> bool {
    escaped.match_indices('%').any(|(at, _)| {
        escaped
            .get(at..at + 3)
            .is_some_and(|e| e.eq_ignore_ascii_case("%2f") || e.eq_ignore_ascii_case("%5c"))
    })
}

/// Whether `escaped` holds an escaped `\` (`%5c`, either case).
fn has_escaped_backslash(escaped: &str) -> bool {
    escaped.match_indices('%').any(|(at, _)| {
        escaped
            .get(at..at + 3)
            .is_some_and(|e| e.eq_ignore_ascii_case("%5c"))
    })
}

/// Whether the walk names the file MSBuild opens for `segment` of a plain
/// import's expansion `whole` (both escaped), and the duplicate-import key it
/// opens it under, by reading every `\` in it as `/`. Only a `\` a property
/// supplied is still there (the attribute's own are `/` already), and MSBuild's
/// Unix path adjustment (`FileUtilities.MaybeAdjustFilePath`) keeps or
/// rewrites it.
///
/// MSBuild adjusts each piece of the expansion (a literal run, a property's
/// value) and then the whole result, and opens what it ends with, collapsed
/// first as a path whose separators are `/` alone and only then with every
/// remaining `\` turned to `/` (`NormalizePath` is `FixFilePath(GetFullPath)`).
/// A `\` the adjustment keeps is a name character to that collapse, so
/// `q\..\../..` pops `q\..\..` whole; and the spelling it keeps is the
/// duplicate-import key, so `zz\..\T.props` imports a `T.props` already
/// imported again (both probed, dotnet 10.0.401). Every adjustment only turns
/// `\` into `/` and collapses slash runs, so the walk's reading holds when
/// either:
///
/// - the whole result's adjustment rewrites ([`unix_adjustment_rewrites`],
///   asked once per import through `rewrites`), which leaves the expansion
///   with every `\` a `/` whatever the pieces did; or
/// - the segment is not a wildcard and no spelling the adjustments can leave
///   collapses or keys otherwise ([`adjustment_is_immaterial`]), whatever
///   each one decided.
///
/// Otherwise some decision turns on what the segment names, and the piece
/// decisions are not modelled (some turn on a directory relative to the
/// working directory), so the caller declines.
pub(super) fn adjustment_settles(
    whole: &str,
    segment: &Escaped,
    rewrites: &mut Option<bool>,
    observer: &Observer,
) -> bool {
    !segment.as_escaped().contains('\\')
        || (!segment.is_filespec_wildcard() && adjustment_is_immaterial(&segment.unescape()))
        || *rewrites.get_or_insert_with(|| unix_adjustment_rewrites(whole, observer))
}

/// Whether every spelling MSBuild's Unix path adjustments can leave of
/// `decoded`, one import path with its `\` intact, opens the same file under
/// the same duplicate-import key. Each `\` sits between two characters that
/// are not separators, so an adjustment only turns some `\` into `/` (there is
/// no slash run for it to collapse, and the path's rootedness is its first
/// character's); and no `.` or `..` component follows the start of the first
/// `/`-separated segment holding a `\`, so the collapse over `/` alone pops and
/// drops what the collapse over both separators does, in every spelling.
fn adjustment_is_immaterial(decoded: &str) -> bool {
    let bytes = decoded.as_bytes();
    let separator = |at: usize| matches!(bytes.get(at), Some(b'/' | b'\\') | None);
    let flanked = bytes
        .iter()
        .enumerate()
        .filter(|(_, b)| **b == b'\\')
        .all(|(at, _)| at > 0 && !separator(at - 1) && !separator(at + 1));
    let Some(first) = decoded.find('\\') else {
        return true;
    };
    let from = decoded[..first].rfind('/').map_or(0, |at| at + 1);
    flanked
        && decoded[from..]
            .split(['/', '\\'])
            .all(|component| !matches!(component, "." | ".."))
}

/// Whether MSBuild's Unix path adjustment rewrites every `\` of a plain
/// import's expansion `escaped` as `/`, whatever MSBuild's working directory:
/// the probe the decision turns on (`LooksLikeUnixFilePath`) is asked of the
/// file system through `observer` where it names an absolute path, and a first
/// segment of `.` or `..` is a directory under any working directory that
/// exists.
pub(super) fn unix_adjustment_rewrites(escaped: &str, observer: &Observer) -> bool {
    // MSBuild on Windows reads `\` as a separator and adjusts nothing.
    if cfg!(windows) {
        return true;
    }
    // `None`: a `$(`, `@(` or `\\` prefix, which MSBuild returns unadjusted.
    let Some(rewrite) = properties::path_fixup::worlds(escaped) else {
        return false;
    };
    match properties::path_fixup::unix_path_probe(&rewrite) {
        properties::path_fixup::UnixPathProbe::Exists => true,
        properties::path_fixup::UnixPathProbe::Absent
        | properties::path_fixup::UnixPathProbe::WorkingDirectory => false,
        properties::path_fixup::UnixPathProbe::Directory(dir) => {
            observed::is_dir(observer, Path::new(dir))
        }
        properties::path_fixup::UnixPathProbe::FileOrDirectory(path) => {
            observed::exists(observer, Path::new(path))
        }
    }
}

/// What `Path.Combine(root, Project)` appends to an SDK root, for a `Project`
/// written as `raw` and expanded to `relative` (`/`-separated): all of it when
/// `raw` is written rooted, and otherwise the expansion with its leading
/// separators dropped.
fn sdk_project_under_root<'a>(raw: &str, relative: &'a str) -> &'a str {
    if sdk_project_written_rooted(raw) {
        relative
    } else {
        relative.trim_start_matches('/')
    }
}

/// Whether an SDK import's `Project`, written as `raw` and expanded to
/// `value`, names a file under `resolution` the walk does not model: one
/// rooted that keeps a `\` bypasses the SDK root, and a `..` after the `\`
/// pops a segment the `\` joins to its neighbour where MSBuild keeps it,
/// which the walk, reading every `\` as a separator, does not. A resolution
/// of no root names no file at all.
pub(super) fn sdk_import_keeps_a_rooted_backslash(
    raw: &str,
    value: &Escaped,
    resolution: &SdkResolution,
) -> bool {
    let names_a_file = !matches!(resolution, SdkResolution::Roots(roots) if roots.is_empty());
    // On Windows a `\` is a separator MSBuild reads as the walk does.
    // A `\` with no `.` or `..` after it names the same file in every
    // spelling (`adjustment_is_immaterial`).
    cfg!(not(windows))
        && names_a_file
        && sdk_project_written_rooted(raw)
        && value.as_escaped().contains('\\')
        && !adjustment_is_immaterial(&value.unescape())
}

/// An import's `Project` attribute, written as `raw`, as MSBuild expands it
/// ([`properties::path_fixup::fix_file_path`]): only a `\` a property or an
/// escape supplies survives expansion. Every reader that expands the
/// attribute (following the import, judging whether it may load nothing or
/// names its path for certain) expands this, plain import or SDK.
pub(super) fn import_project_as_expanded(raw: &str) -> String {
    properties::path_fixup::fix_file_path(raw)
}

/// Whether an SDK import's `Project`, written as `raw`, is rooted as written,
/// so `Path.Combine(root, Project)` drops the root: no character of the root
/// reaches MSBuild's import expression, and [`sdk_root_is_reparsed`] has
/// nothing to say about it.
fn sdk_project_written_rooted(raw: &str) -> bool {
    raw.replace('\\', "/").starts_with('/')
}

/// Whether MSBuild re-parses `root` in an import path, and so names something
/// other than the directory: it holds a `$(`, `;`, `*`, `?` or `%`, or on a
/// Unix host a `\`, which MSBuild reads as a separator (before a `..` in the
/// import resolves, from the command line, and after, in process).
fn sdk_root_is_reparsed(root: &Path) -> bool {
    let root_text = root.to_string_lossy();
    root_text.contains(['%', ';', '*', '?'])
        || root_text.contains("$(")
        || (cfg!(unix) && root_text.contains('\\'))
}

/// The file an SDK import names: `root` joined with `under_root`, made absolute
/// against the working directory and then collapsed lexically, as
/// `NormalizePath` does.
fn sdk_import_path(root: &Path, under_root: &str) -> std::io::Result<PathBuf> {
    Ok(normalise(&std::path::absolute(root.join(under_root))?))
}

/// A wildcard `<Import Project=…>`. MSBuild expands the wildcard and —
/// unlike a literal path, where a missing file is an error — **silently
/// skips** the import when nothing matches. The SDK relies on this: the
/// unconditional `Microsoft.VisualStudioVersion.v*.Common.props` import in
/// `Microsoft.Common.props` matches nothing on a clean dotnet host, and the
/// `Imports\…\ImportBefore\*` hooks usually match nothing too.
///
/// Only a wildcard confined to the final path component is modelled (that
/// covers every SDK use). Matches are walked in name order — MSBuild's
/// FileMatcher yields an OS listing that its import loop consumes as a
/// sorted set, and a deterministic order is required here anyway.
/// A wildcard *directory* component falls back to the conservative
/// structural skip: the un-followed files could have carried anything.
///
/// With `collapse`, the directory is collapsed as text before it is listed,
/// as MSBuild collapses the fixed part of a wildcard path, so the files
/// listed are the ones beside a symlink's text, not its target's.
fn follow_wildcard_import(
    normalised: &str,
    collapse: bool,
    current_file_dir: &Path,
    span: Range<usize>,
    state: &mut State<'_>,
) {
    match wildcard_import(normalised, collapse, current_file_dir, state.observer) {
        WildcardImport::Matches(matches) => {
            for matched in matches {
                walk_import_file(&matched, span.clone(), collapse, state);
            }
        }
        WildcardImport::Unmodelled => {
            // What MSBuild imports here, it may fail to load.
            note_undecided_wildcard(normalised, span.clone(), state);
            // Push the diagnostic too, not just the uncertainty: silently
            // returning would leave `is_partial` false with imports dropped.
            state.push(
                DiagnosticKind::UnsupportedConstruct {
                    element: format!(
                        "Import Project={normalised:?} (wildcard directory component)"
                    ),
                },
                span.clone(),
            );
            state.mark_structural_skip(
                StructuralCompileItemUncertainty::ImportProjectUnresolved {
                    project: normalised.to_string(),
                },
                span,
            );
        }
        WildcardImport::Unlisted { dir, message } => {
            note_undecided_wildcard(normalised, span.clone(), state);
            // Unreadable directory is NOT zero matches — files may well
            // be there, and the dropped imports could have carried
            // anything. Diagnostic + uncertainty, same as the wildcard-
            // directory arm above.
            state.push(
                DiagnosticKind::ImportFailed {
                    path: dir,
                    reason: ImportFailReason::Io { message },
                },
                span.clone(),
            );
            state.mark_structural_skip(
                StructuralCompileItemUncertainty::ImportProjectUnresolved {
                    project: normalised.to_string(),
                },
                span,
            );
        }
    }
}

/// Record that MSBuild may reject the project over a wildcard import of
/// `normalised` the walk took but could not expand: what it matches may not
/// load.
fn note_undecided_wildcard(normalised: &str, span: Range<usize>, state: &mut State<'_>) {
    state.note_rejection(
        crate::RejectionCertainty::Possible,
        crate::RejectionCause::Import {
            project: normalised.to_string(),
            gate_undecided: false,
            why: crate::UnloadableImport::PathUndecided,
        },
        span,
    );
}

/// What a wildcard import of `normalised` (a path with each `\` read as
/// `/`) from `current_file_dir` names: the one reading of a wildcard import,
/// as the walk ([`follow_wildcard_import`]) takes it.
pub(super) enum WildcardImport {
    /// The files MSBuild loads, in the order it loads them.
    Matches(Vec<PathBuf>),
    /// A wildcard in the directory part, no file part, or a spelling ending
    /// in a separator: a shape the walk does not expand.
    Unmodelled,
    /// The directory could not be listed.
    Unlisted { dir: PathBuf, message: String },
}

/// [`WildcardImport`] of `normalised`. Pinned against `dotnet msbuild`
/// 10.0.401:
///
/// - a spelling whose directory part names a file (or nothing) matches
///   nothing; one ending in a separator is not modelled;
/// - a match is any entry whose target is not a directory: a directory, or
///   a link to one, is no match, while a dangling link is one (and fails to
///   load), as is a link to a file;
/// - matching is case-insensitive, and matches load in ordinal-ignore-case
///   order (`a.props` before `B.props`).
///
/// With `collapse`, the directory is collapsed as text before it is listed,
/// as MSBuild collapses the fixed part of a wildcard path, so the files
/// listed are the ones beside a symlink's text, not its target's.
pub(super) fn wildcard_import(
    normalised: &str,
    collapse: bool,
    current_file_dir: &Path,
    observer: &observed::Observer,
) -> WildcardImport {
    // A wildcard spelt as a directory matches nothing when MSBuild reads it
    // as a file spec at all; which spellings it refuses instead (a decoded
    // NUL, a run of stars, a `..` it collapses first) is not modelled.
    if normalised.ends_with('/') {
        return WildcardImport::Unmodelled;
    }
    let path = current_file_dir.join(normalised);
    let file_pattern = path
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    let written_dir = path.parent().unwrap_or(current_file_dir);
    let dir = if written_dir.to_string_lossy().contains(['*', '?']) {
        written_dir.to_path_buf()
    } else {
        import_open_path(written_dir, collapse)
    };
    if dir.to_string_lossy().contains(['*', '?']) || file_pattern.is_empty() {
        return WildcardImport::Unmodelled;
    }
    let entries = match observed::read_dir(observer, &dir) {
        Ok(entries) => entries,
        // A missing directory, or a file where a directory was named, is
        // zero matches: MSBuild-silent.
        Err(e)
            if matches!(
                e.kind(),
                std::io::ErrorKind::NotFound | std::io::ErrorKind::NotADirectory
            ) =>
        {
            return WildcardImport::Matches(Vec::new());
        }
        Err(e) => {
            return WildcardImport::Unlisted {
                dir,
                message: e.to_string(),
            };
        }
    };
    let mut matches: Vec<PathBuf> = entries
        .into_iter()
        .filter_map(Result::ok)
        // The name first, so only a link the pattern names has its target
        // asked about (and enters the read set).
        .filter(|entry| wildcard_matches(&file_pattern, &entry.name.to_string_lossy()))
        .filter(|entry| match entry.kind {
            Ok(EntryKind::Dir) | Err(_) => false,
            // A link is a match unless its target is a directory; a dangling
            // one is (and fails to load).
            Ok(EntryKind::Symlink) => observed::kind(observer, &entry.path) != Ok(EntryKind::Dir),
            Ok(EntryKind::File | EntryKind::Other) => true,
        })
        .map(|entry| entry.path)
        .collect();
    // MSBuild consumes wildcard matches in ordinal-ignore-case order
    // (verified against `dotnet msbuild`: `a.props` imports before
    // `B.props`); byte order would put `B` first on unix. Byte order
    // breaks ties so equal-ignoring-case names still sort
    // deterministically.
    matches.sort_by(|a, b| {
        let key = |p: &PathBuf| {
            p.file_name()
                .map(|n| n.to_string_lossy().to_lowercase())
                .unwrap_or_default()
        };
        key(a).cmp(&key(b)).then_with(|| a.cmp(b))
    });
    WildcardImport::Matches(matches)
}

/// Match `pattern` (with `*` = any run, `?` = any single char) against
/// `name`, case-insensitively (MSBuild file matching is case-insensitive
/// even on case-sensitive filesystems). Classic two-pointer glob with
/// star backtracking.
fn wildcard_matches(pattern: &str, name: &str) -> bool {
    let pattern: Vec<char> = pattern.chars().flat_map(char::to_lowercase).collect();
    let name: Vec<char> = name.chars().flat_map(char::to_lowercase).collect();
    let (mut p, mut n) = (0usize, 0usize);
    let mut star: Option<(usize, usize)> = None;
    while n < name.len() {
        if p < pattern.len() && (pattern[p] == '?' || pattern[p] == name[n]) {
            p += 1;
            n += 1;
        } else if p < pattern.len() && pattern[p] == '*' {
            star = Some((p, n));
            p += 1;
        } else if let Some((star_p, star_n)) = star {
            p = star_p + 1;
            n = star_n + 1;
            star = Some((star_p, star_n + 1));
        } else {
            return false;
        }
    }
    while p < pattern.len() && pattern[p] == '*' {
        p += 1;
    }
    p == pattern.len()
}

fn simple_property_reference(raw: &str) -> Option<&str> {
    let trimmed = raw.trim();
    let inner = trimmed.strip_prefix("$(")?.strip_suffix(')')?;
    if inner.is_empty()
        || !inner
            .bytes()
            .all(|b| b == b'_' || b == b'.' || b.is_ascii_alphanumeric())
    {
        return None;
    }
    Some(inner)
}

/// Split a leading `'…'` literal off `input`, returning its contents and the
/// remaining text.
fn parse_single_quoted(input: &str) -> Option<(&str, &str)> {
    let rest = input.strip_prefix('\'')?;
    let end = rest.find('\'')?;
    Some((&rest[..end], &rest[end + 1..]))
}

fn condition_has_exists_for_property(condition: Option<&str>, property_name: &str) -> bool {
    let Some(condition) = condition else {
        return false;
    };
    for (idx, _) in condition.char_indices() {
        let Some(rest) = condition[idx..].strip_prefix("Exists").or_else(|| {
            condition[idx..]
                .get(..6)
                .filter(|s| s.eq_ignore_ascii_case("Exists"))
                .map(|_| &condition[idx + 6..])
        }) else {
            continue;
        };
        if !keyword_boundary(condition, idx, 6) {
            continue;
        }
        let Some(rest) = rest.trim_start().strip_prefix('(') else {
            continue;
        };
        let Some((arg, rest)) = parse_single_quoted(rest.trim_start()) else {
            continue;
        };
        if !rest.trim_start().starts_with(')') {
            continue;
        }
        if simple_property_reference(arg)
            .is_some_and(|name| name.eq_ignore_ascii_case(property_name))
        {
            return true;
        }
    }
    false
}

fn keyword_boundary(source: &str, start: usize, len: usize) -> bool {
    let bytes = source.as_bytes();
    let before = start
        .checked_sub(1)
        .and_then(|idx| bytes.get(idx))
        .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_');
    let after = bytes
        .get(start + len)
        .is_some_and(|b| b.is_ascii_alphanumeric() || *b == b'_');
    !before && !after
}

/// Read, parse, and recursively walk an external MSBuild file.
/// Caller-supplied `span` attributes any failure diagnostic to the
/// source location of the *importer* (the `<Import>` element's
/// range, or `0..0` for an implicit import).
///
/// Self-contained: both failure modes (depth, IO/parse) emit a single
/// [`DiagnosticKind::ImportFailed`] and return without disturbing
/// `state.depth`; a duplicate of an already-performed import returns
/// silently (see below). The depth increment/decrement pair only runs
/// on the happy path.
/// Offer `root`'s `DefaultTargets` to `MSBuildProjectDefaultTargets`, as
/// MSBuild's `Evaluator.UpdateDefaultTargets` does. Roots are offered in
/// depth-first import order, each before its own implicit imports. A root
/// whose `DefaultTargets` expands (properties only) to anything sets the
/// property to that text, unescaped and untrimmed; MSBuild stores the
/// unescaped text as the escaped value. The offer settles at the first root
/// whose expansion lists a target (split on `;`, each trimmed before it is
/// unescaped), and nothing
/// changes the property after; a root that sets it to blanks or separators
/// alone leaves the offer open.
///
/// A root the walk cannot vouch for settles the offer with the property
/// unset, so reads of it stay inexact. That is one whose expansion reads an
/// undecided or unpinned value, one reached after the walk passed content it
/// could not see (which may have set it first), and one in a file the
/// `Directory.Build.*` fallback walks doubted, which MSBuild may never
/// import.
fn latch_default_targets(root: Node<'_, '_>, state: &mut State<'_>) {
    if state.default_targets_decided {
        return;
    }
    let raw = attribute(root, "DefaultTargets");
    let Some(raw) = raw.as_deref() else {
        return;
    };
    let expansion = item_pass::expand_silent(raw, state);
    if expansion.had_issue()
        || expansion.unpinned_root.is_some()
        || state.walk_opaque.is_some()
        // A root the `Directory.Build.*` fallback walks may be one MSBuild
        // never imports.
        || state.directory_build.fallback.is_some()
    {
        state.default_targets_decided = true;
        state.lookup.unbind("MSBuildProjectDefaultTargets");
        return;
    }
    // The expansion's trust was judged just above (`had_issue`,
    // `unpinned_root`, opacity).
    if expansion.value.ignoring_trust().is_empty() {
        return;
    }
    let value = expansion.value.ignoring_trust().unescape();
    state.default_targets_decided = expansion
        .value
        .ignoring_trust()
        .as_escaped()
        .split(';')
        // Trimmed in the escaped domain, before unescaping: `%20` lists the
        // target " " (`EscapingUtilities.UnescapeAll(…, trim: true)`).
        .any(|target| !target.trim().is_empty());
    state
        .lookup
        .insert_escaped("MSBuildProjectDefaultTargets", Escaped::from_xml(value));
}

fn walk_external_file(path: &Path, span: Range<usize>, state: &mut State<'_>) {
    walk_import_file(path, span, true, state);
}

/// The path [`walk_import_file`] opens for `path`: collapsed as text when
/// `collapse` says and nothing that fails it in MSBuild would be erased.
fn import_open_path(path: &Path, collapse: bool) -> PathBuf {
    let text = path.as_os_str().as_encoded_bytes();
    if collapse && !text.contains(&0) && !matches!(text.last(), Some(b'/' | b'\\')) {
        std::path::absolute(path).map_or_else(|_| path.to_path_buf(), |p| normalise(&p))
    } else {
        path.to_path_buf()
    }
}

/// [`walk_external_file`], collapsing `path` first only when `collapse` says.
fn walk_import_file(path: &Path, span: Range<usize>, collapse: bool, state: &mut State<'_>) {
    // MSBuild opens an import at its path collapsed as text
    // (`FileUtilities.NormalizePath`, which is `GetFullPath`): `..` pops the
    // segment before it whatever that segment links to, so `link/../a.props`
    // is the `a.props` beside `link`, never the one beside `link`'s target.
    // The file's identity (`MSBuildThisFile*`, nested imports' directory) is
    // that collapsed path too. Collapsing would erase what fails the path in
    // MSBuild: a trailing separator, which names a directory no import loads
    // (MSB4019), and a NUL anywhere (MSB4102). Such a path is opened as
    // written, and fails as it does in MSBuild: `observed::canonicalize`
    // fails a file followed by a separator on every host, as the kernel
    // does.
    let collapsed = import_open_path(path, collapse);
    let path = collapsed.as_path();
    // On Unix MSBuild loads an imported file with every `\` of its path read
    // as `/` (`FileUtilities.FixFilePath`), and refuses the project where
    // that names no file. A `\` that reaches here came from a name a wildcard
    // matched, or from an SDK's directory: the file the walk would open is
    // not the one MSBuild opens, so decline. MSBuild may name no file there
    // and refuse the project, so nothing after this commits either.
    if cfg!(unix) && path.as_os_str().as_encoded_bytes().contains(&b'\\') {
        state.note_rejection(
            crate::RejectionCertainty::Possible,
            crate::RejectionCause::Import {
                project: path.display().to_string(),
                gate_undecided: false,
                why: crate::UnloadableImport::PathUndecided,
            },
            span.clone(),
        );
        state.push(
            DiagnosticKind::UnsupportedConstruct {
                element: format!(
                    "Import of {} (a `\\` in the path, which MSBuild reads as a separator \
                     on this host)",
                    path.display()
                ),
            },
            span.clone(),
        );
        state.mark_structural_skip(
            StructuralCompileItemUncertainty::ImportProjectUnresolved {
                project: path.display().to_string(),
            },
            span,
        );
        return;
    }
    // MSBuild's duplicate-import skip: an import that resolves to an
    // already-imported path (same lexically-normalised, case-insensitive
    // spelling — see [`import_dedup_key`]) is ignored with a warning
    // (MSB4011; MSB4210 for the entry project) and the evaluation
    // succeeds. That cuts repeated list segments, diamonds, *and*
    // cycles — MSBuild registers an import before walking the file, so
    // a cycle's back-edge is just another duplicate (probed: a↔b
    // evaluates cleanly with each body run once). The skip is faithful,
    // so it is silent here: pushing a diagnostic would flip
    // `is_partial` for evaluations MSBuild completes exactly.
    let dedup_key = import_dedup_key(path);
    if state.imports_seen.contains(&dedup_key) {
        return;
    }
    // An import a `Directory.Build.*` fallback walk made is one MSBuild may
    // not have made, so this one may not be a duplicate.
    if let directory_build::Doubted::Settled =
        directory_build::doubted_duplicate(path, &dedup_key, state)
    {
        return;
    }
    // Content the walk could not see may already have made this import, and
    // MSBuild then skips it here as a duplicate (MSB4011): like an import
    // followed on a gate the walk could not decide, it is one MSBuild may not
    // make, so what it writes is not the build's for certain (#891).
    if state.directory_build.fallback.is_none()
        && let Some(hidden) = state.walk_opaque.clone()
    {
        let root = match hidden {
            OpacityCause::Gate(root) => root,
            OpacityCause::Unentered(what) => UnpinnedRoot::UnsupportedCondition(
                format!(
                    "the import of {}, which content the walk could not enter ({what}) may \
                     already have made",
                    path.display()
                )
                .into(),
            ),
        };
        directory_build::within_followed_import(Some(root), state, |state| {
            walk_import_file(path, span, collapse, state);
        });
        return;
    }
    // A near-duplicate under the wider Unicode fold: the pair differs in
    // non-ASCII casing, where .NET's ordinal table (probed: `ı`≠`I` yet
    // `σ`==`Σ`) is not reproducible from Rust's folds. MSBuild might skip
    // this import or walk it; committing either would risk a wrong-clean
    // result, so decline — the diagnostic flips `is_partial` and the
    // structural skip records that a file's worth of content may be
    // missing (which also latches `walk_opaque` for C.2b).
    let fuzzy_key = import_dedup_fuzzy_key(path);
    if state.imports_seen_fuzzy.contains(&fuzzy_key)
        || state
            .directory_build
            .doubted_near_duplicate(&dedup_key, &fuzzy_key)
    {
        state.push(
            DiagnosticKind::UnsupportedConstruct {
                element: format!(
                    "Import Project={} (near-duplicate of an already-imported path \
                     under Unicode case folding)",
                    path.display()
                ),
            },
            span.clone(),
        );
        state.mark_structural_skip(
            StructuralCompileItemUncertainty::ImportProjectUnresolved {
                project: path.display().to_string(),
            },
            span,
        );
        return;
    }
    if state.depth >= MAX_IMPORT_DEPTH {
        state.push(
            DiagnosticKind::ImportFailed {
                path: path.to_path_buf(),
                reason: ImportFailReason::DepthLimit { depth: state.depth },
            },
            span,
        );
        return;
    }
    // Canonical (symlink-resolved) identity for `walked_files` and the
    // SDK-subtree verdict below. Deliberately *not* the dedup key: MSBuild
    // never resolves symlinks when deduping, so an alias of an imported
    // file must still walk (its dedup key differs), while `walked_files`
    // wants the file's real identity.
    let canon = match observed::canonicalize(state.observer, path) {
        Ok(c) => c,
        Err(e) => {
            let reason = if e.kind() == std::io::ErrorKind::NotFound {
                ImportFailReason::NotFound
            } else {
                ImportFailReason::Io {
                    message: e.to_string(),
                }
            };
            state.push(
                DiagnosticKind::ImportFailed {
                    path: path.to_path_buf(),
                    reason,
                },
                span,
            );
            return;
        }
    };
    let parsed = match observed::read_document(state.observer, &canon) {
        Ok(parsed) => parsed,
        Err(e) => {
            let reason = if e.kind() == std::io::ErrorKind::NotFound {
                ImportFailReason::NotFound
            } else {
                ImportFailReason::Io {
                    message: e.to_string(),
                }
            };
            state.push(
                DiagnosticKind::ImportFailed {
                    path: canon,
                    reason,
                },
                span,
            );
            return;
        }
    };
    let parsed = match parsed {
        Ok(parsed) => parsed,
        Err(e) => {
            state.push(
                DiagnosticKind::ImportFailed {
                    path: canon,
                    reason: ImportFailReason::MalformedXml {
                        message: e.to_string(),
                    },
                },
                span,
            );
            return;
        }
    };
    let doc = parsed.document();
    // Rebind `MSBuildThisFile{,Directory}` using the *pre-canonical*
    // path for the same reason nested `<Import>` resolution does
    // below: when MSBuild reaches a file through a symlink, it
    // treats the symlink path — not the OS-canonical target — as
    // the file's identity for path purposes. Using `&canon` here
    // would make `$(MSBuildThisFileDirectory)local.props` resolve
    // against the link target, picking the wrong sibling file.
    // `canon` is reserved for `walked_files` identity.
    let frame = state.enter_this_file(path);
    // The file's constructs are its own, for a site's construct
    // ([`State::site_file`]); what failed before it loaded is the import's,
    // in the importing file.
    let saved_site_file = state.site_file.replace(canon.as_path().into());
    // Deferred `<ItemGroup>`s recorded while inside this file must know
    // which document to replay against — same pre-canonical-path identity
    // as the `MSBuildThisFile` frame above. `retained: None` until the
    // first deferral in this frame forces the document to be kept.
    let saved_current_file = std::mem::replace(
        &mut state.current_file,
        CurrentFile::Imported {
            path: path.to_path_buf(),
            document: std::sync::Arc::clone(&parsed),
            retained: None,
        },
    );
    state.directory_build.register_import(
        dedup_key,
        fuzzy_key,
        &mut state.imports_seen,
        &mut state.imports_seen_fuzzy,
    );
    state.walked_files.insert(canon.clone());
    state.depth += 1;
    // Judge SDK-provenance by this file's *own* canonical path, independent of
    // how it was reached. A user `Directory.Build.props` pulled in through the
    // SDK's `Microsoft.Common.props` chain is still scored by its path (not
    // under the SDK tree → respected); an SDK target reached from anywhere is
    // tolerated. Save/restore so the parent file's verdict resumes on return.
    //
    // Two arms are ORed, both compared against the recorded (canonical) roots:
    //
    //  1. the file's own canonical path — the primary check (normal SDK files,
    //     diamond imports through differently-spelt paths that agree only after
    //     canonicalisation);
    //  2. the canonicalisation of the reach path's *parent directory*.
    //
    // Arm 2 exists for the file-level symlink-merge layout (Nix's combined dotnet
    // tree, but any store-of-symlinks qualifies): there the merge tree's
    // directories are real while its leaf files are per-file symlinks back to the
    // originating store, so a workload `WorkloadManifest.targets` canonicalises
    // into a *different* store than its own directory does. Arm 1 alone then
    // wrongly scores that SDK-internal manifest as a user file and lets its
    // `<ImportGroup>` conditions (e.g. `'$(TargetPlatformIdentifier)' ==
    // 'android'`) flip `items_uncertain`, refusing the fold for every real SDK
    // project (`sdk_project_fold_e2e`). Canonicalising the *directory* (which is
    // real in the merge tree) recovers tolerance.
    //
    // Crucially arm 2 canonicalises the directory, so it is not fooled by a
    // reach path that only *lexically* sits under a root: an SDK file importing
    // `../user.props` (parent canonicalises to the SDK's parent, outside every
    // root) or a directory symlink inside the SDK tree pointing out (parent
    // canonicalises to the escape target) are both correctly *not* tolerated —
    // only a genuine leaf-file symlink out of a real in-tree directory is.
    let reach_parent_canon = path.parent().map(|dir| {
        observed::canonicalize(state.observer, dir).unwrap_or_else(|_| dir.to_path_buf())
    });
    let saved_in_sdk_subtree = state.in_sdk_subtree;
    state.in_sdk_subtree = state.sdk_tolerance_roots.iter().any(|root| {
        canon.starts_with(root)
            || reach_parent_canon
                .as_deref()
                .is_some_and(|dir| dir.starts_with(root))
    });
    // The same two arms, against the entry SDK's version directory alone: a
    // file another SDK resolution brought into the tolerance set (a NuGet
    // MSBuild SDK, say) is still foreign to the entry .NET SDK.
    let in_entry_sdk = state.entry_sdk_version_dir.as_deref().is_some_and(|root| {
        canon.starts_with(root)
            || reach_parent_canon
                .as_deref()
                .is_some_and(|dir| dir.starts_with(root))
    });
    // A workload manifest ships with the .NET install, outside the version
    // directory (and, in a symlink-merged install, in another tree), and is
    // reached as tolerated SDK content.
    let workload_manifest = state.in_sdk_subtree
        && path
            .components()
            .any(|c| c.as_os_str().eq_ignore_ascii_case("sdk-manifests"));
    // A file of the SDK entered straight from a file outside it, other than an
    // SDK's own `Sdk.props`/`Sdk.targets` (which the `Sdk` attribute and an
    // `<Import Sdk=…>` reach): the SDK's own content, in an arrangement the SDK
    // did not choose.
    let sdk_entry_point = path.file_name().and_then(|n| n.to_str()).is_some_and(|n| {
        n.eq_ignore_ascii_case("Sdk.props") || n.eq_ignore_ascii_case("Sdk.targets")
    }) && path
        .parent()
        .and_then(Path::file_name)
        .is_some_and(|n| n.eq_ignore_ascii_case("Sdk"));
    if in_entry_sdk && !saved_in_sdk_subtree && !sdk_entry_point {
        state
            .sdk_files_imported_from_outside
            .insert(path.to_path_buf());
    }
    // The entry SDK's own file, by its canonical place in the version
    // directory, however the import spelled it.
    if let Some(root) = state.entry_sdk_version_dir.as_deref() {
        let relative = canon
            .strip_prefix(root)
            .ok()
            .map(Path::to_path_buf)
            .or_else(|| {
                let parent = reach_parent_canon.as_deref()?.strip_prefix(root).ok()?;
                Some(parent.join(path.file_name()?))
            });
        if let Some(relative) = relative {
            state.imported_sdk_files.insert(relative);
        }
    }
    // A workload manifest file, by its path under `sdk-manifests`.
    if workload_manifest {
        let under: Vec<_> = path
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .skip_while(|c| !c.eq_ignore_ascii_case("sdk-manifests"))
            .skip(1)
            .collect();
        if !under.is_empty() {
            state.workload_manifest_files.insert(under.join("/"));
        }
    }
    // A workload manifest the resolver found outside the entry SDK's install
    // (the user's own, behind the install's `userlocal` marker). Installed
    // manifests sit under `<dotnet root>/sdk-manifests` as the resolver
    // spells the root, wherever a merged install's links lead (the version
    // directory and the manifests can be different trees).
    let installed_manifests = state
        .resolved_sdk_root
        .as_deref()
        .and_then(dotnet_sdk_version_dir)
        .and_then(|version_dir| version_dir.parent()?.parent())
        .map(|root| lexically_normal(&root.join("sdk-manifests")));
    if workload_manifest
        && !installed_manifests
            .is_some_and(|manifests| lexically_normal(path).starts_with(manifests))
    {
        state
            .workload_manifests_outside_install
            .insert(path.to_path_buf());
    }
    let saved_in_foreign_document = state.in_foreign_document;
    state.in_foreign_document = !in_entry_sdk && !workload_manifest;
    if workload_manifest && !in_entry_sdk {
        state
            .workload_definitions
            .record_document(doc.root_element(), path);
    } else if !in_entry_sdk {
        state
            .foreign_definitions
            .record_document(doc.root_element(), path);
    }
    // Pin `import_site_span` on the *first* descent (when it's None)
    // and preserve it on nested descents. All diagnostics and items
    // produced inside this — and any further nested — file will be
    // attributed to this top-level `<Import>` element in the entry
    // project's source, keeping `Diagnostic::span` /
    // `ResolvedItem::span` valid byte offsets into the source the
    // caller handed in. This must happen before we record imported-file
    // uncertainty causes below, so those causes get `Imported`
    // provenance too. See [`State::import_site_span`].
    let saved_import_site_span = state.import_site_span.clone();
    if saved_import_site_span.is_none() {
        state.import_site_span = Some(span.clone());
    }
    // For nested `<Import>` resolution, use the *pre-canonical*
    // path's parent — the directory MSBuild reached this file
    // through, not the directory the OS symlink-resolves to. When
    // `links/common.props` is a symlink to `/elsewhere/common.props`
    // and that file imports `local.props`, MSBuild reads
    // `links/local.props`; canonicalising would have made us read
    // `/elsewhere/local.props`. `canon` is still used (above) for
    // `walked_files` — the one place resolved identity matters.
    let file_dir: PathBuf = path.parent().map(Path::to_path_buf).unwrap_or_default();
    // `TreatAsLocalProperty` on an imported root unprotects names
    // for the scope of that file. MSBuild specifies it only applies
    // to *global* properties — not reserved well-known names — so
    // we exclude names in `state.reserved` from the unprotection.
    // Track exactly what we removed so the corresponding restore
    // doesn't re-add names that the entry project itself had marked
    // local (and which therefore were never in `state.protected`).
    let imported_overrides = collect_local_overrides(doc.root_element());
    // Record the opt-out regardless of whether this walk had a matching global
    // to unprotect: the question a consumer asks is "could the document have
    // overwritten a global of this name", which does not depend on what the
    // caller happened to supply *this* time.
    state
        .locally_overridable
        .extend(imported_overrides.iter().cloned());
    let unprotected: Vec<String> = imported_overrides
        .into_iter()
        .filter(|name| !state.reserved.contains(name) && state.protected.remove(name))
        .collect();
    // Nested SDK roots are spliced through the same machinery the
    // entry project uses: `resolve_project_sdk` returns paths on a
    // happy resolve and pushes the appropriate diagnostic for every
    // failure mode (no resolver supplied, `Err(NotFound)`,
    // `Err(VersionNotSatisfied)`). The recursive `walk_external_file`
    // calls re-enter this same function, so the duplicate-import skip,
    // depth limits, and the import-site span pin (already `Some` here
    // for any descent beyond the first) all just work.
    // MSBuild loads the file before it evaluates any of it.
    rejection::judge_load_time(doc.root_element(), state);
    latch_default_targets(doc.root_element(), state);
    // The file's own imports say for themselves how they name their paths;
    // its implicit SDK imports are not explicit imports.
    let saved_path_certain = std::mem::take(&mut state.taken_import_path_certain);
    let nested_sdk = resolve_project_sdk(doc.root_element(), state);
    if let Some(paths) = nested_sdk.as_ref() {
        directory_build::note_nested_sdk(&paths.root, state);
        walk_external_file(&paths.props, doc.root_element().range(), state);
    }
    walk_doc_body(doc.root_element(), &file_dir, state);
    if let Some(paths) = nested_sdk.as_ref() {
        walk_external_file(&paths.targets, doc.root_element().range(), state);
    }
    state.taken_import_path_certain = saved_path_certain;
    for name in unprotected {
        state.protected.insert(name);
    }
    state.import_site_span = saved_import_site_span;
    state.in_sdk_subtree = saved_in_sdk_subtree;
    state.in_foreign_document = saved_in_foreign_document;
    state.depth -= 1;
    state.current_file = saved_current_file;
    state.site_file = saved_site_file;
    state.exit_this_file(frame);
}

fn contains_glob(s: &str) -> bool {
    s.bytes().any(|b| b == b'*' || b == b'?')
}

fn contains_item_reference(s: &str) -> bool {
    s.contains("@(")
}

fn contains_metadata_reference(s: &str) -> bool {
    s.contains("%(")
}

/// The body of `node` as MSBuild reads it (`Utilities.GetXmlNodeInnerContents`
/// over the children its XML reader reports, [`crate::document::element_content`]
/// and [`crate::document::inner_contents`]). Each text is read with its
/// references decoded and its line ends as written, so `a<CR><LF>b` is four
/// characters.
///
/// A run of text that is nothing but XML whitespace, written literally or as
/// hexadecimal references, is **insignificant** and contributes nothing,
/// matching MSBuild's XML layer. This is a per-run rule, not a whole-value one,
/// and all of it is pinned against `dotnet msbuild` 10.0.301 (2026-07-11):
///
/// - `<P> </P>`, a tab-only body and a CRLF-only body → `""` (so
///   `'$(P)' == ''` is *true*).
/// - `<Q>  x  </Q>` → `"  x  "`: padding around content stays verbatim, and
///   so does a line break in it, `<Q><CR><LF>  x<CR><LF></Q>` reading as
///   seven characters.
/// - `<R>  <!-- c -->x</R>` → `"x"`: a comment splits the text, and the
///   whitespace-only run drops on its own — which is why the test must be
///   per-run (a whole-value collapse would wrongly keep `"  x"` here). Each
///   surviving run keeps its own line ends: `a<CR><!-- c --><LF>b` is
///   `a<CR><LF>b`.
/// - `<P> $(Undefined) </P>` → `"  "`: the rule is pre-expansion, and is not
///   re-applied to an expansion result.
/// - `<P>&#32;</P>` → `" "` but `<P>&#x20;</P>` → `""`: one decimal reference
///   makes the whole run significant (` &#32; ` is three characters), as
///   MSBuild's reader classifies it (`dotnet msbuild` 10.0).
///
/// "XML whitespace" is exactly space/tab/CR/LF — a non-breaking space is
/// content (`&#160;` has length 1) — so this must not use `char::is_whitespace`,
/// which is Unicode-wide.
///
/// A CDATA section's content is read verbatim. A body of text and comments
/// alone reads as its text; one holding a CDATA section reads as its text too
/// when the section is all of it or comes first (after Unicode whitespace,
/// .NET's `TrimStart`), and as its inner XML otherwise (`dotnet msbuild`
/// 10.0):
///
/// - ` <![CDATA[ ]]> ` → `" "`; `<![CDATA[a]]>x<!-- c -->` → `"ax"`;
///   `&#160;<![CDATA[a]]>x` → `"\u{a0}ax"`.
/// - `x<![CDATA[y]]>`, `<!-- c --><![CDATA[y]]>` → themselves, and
///   `x>y<![CDATA[z]]>` → `"x&gt;y<![CDATA[z]]>"`: each text re-escaped, and
///   whitespace-only runs dropped from between the pieces.
///
/// Returns `None` for a body holding an element or a processing instruction,
/// whose value we do not derive, so callers degrade rather than commit a
/// guess: MSBuild then reads the body's inner XML, which re-spells the
/// markup (`<P>a<x/>b</P>` is `a<x />b`, where the text alone is `ab`).
fn collect_element_text(node: Node<'_, '_>) -> Option<String> {
    crate::document::inner_contents(&crate::document::element_content(node)?)
}

#[cfg(test)]
mod toolset_tests {
    use super::{toolset_assembly_version, toolset_visual_studio_version};
    use std::path::Path;

    #[test]
    fn the_product_version_commits_only_for_probed_release_majors() {
        for (dir, expected) in [
            ("/dotnet/sdk/6.0.418", Some("17.0")),
            ("/dotnet/sdk/8.0.425", Some("17.0")),
            ("/dotnet/sdk/9.0.315", Some("17.0")),
            ("/dotnet/sdk/10.0.109", Some("18.0")),
            ("/dotnet/sdk/10.0.401", Some("18.0")),
            // A preview can carry the previous MSBuild major.
            ("/dotnet/sdk/10.0.100-preview.3.25201.16", None),
            // A probed prerelease commits, and only its exact version.
            ("/dotnet/sdk/11.0.100-rc.1.26425.128", Some("18.0")),
            ("/dotnet/sdk/11.0.100-rc.1.26425.129", None),
            ("/dotnet/sdk/11.0.100-rc.2.26501.1", None),
            // Unprobed majors.
            ("/dotnet/sdk/7.0.410", None),
            ("/dotnet/sdk/11.0.100", None),
            // Not a version directory.
            ("/dotnet/sdk/current", None),
            ("/dotnet/sdk/10.0", None),
            ("/dotnet/sdk/10.0.x", None),
        ] {
            assert_eq!(
                toolset_visual_studio_version(Path::new(dir)),
                expected,
                "{dir}"
            );
            assert_eq!(toolset_assembly_version(Path::new(dir)), expected, "{dir}");
        }
    }
}

#[cfg(all(test, unix))]
mod adjustment_tests {
    use super::adjustment_is_immaterial;

    /// `GetFullPath` on Unix: `/` is the only separator; empty and `.`
    /// components drop, `..` pops (not past the root), and a trailing `/`
    /// stays.
    fn get_full_path(path: &str) -> String {
        let mut out: Vec<&str> = Vec::new();
        for component in path.split('/') {
            match component {
                "" | "." => {}
                ".." => {
                    out.pop();
                }
                _ => out.push(component),
            }
        }
        let trailing = path.ends_with('/') && !out.is_empty();
        format!("/{}{}", out.join("/"), if trailing { "/" } else { "" })
    }

    /// The duplicate-import key MSBuild gives an import of `spelling` from
    /// `/d/e`: `FixFilePath(GetFullPath(Path.Combine(dir, spelling)))`. The
    /// file it opens is that key collapsed again.
    fn key(spelling: &str) -> String {
        let combined = if spelling.starts_with('/') {
            spelling.to_string()
        } else {
            format!("/d/e/{spelling}")
        };
        get_full_path(&combined).replace('\\', "/")
    }

    /// Every spelling MSBuild's adjustments can leave of `value`: each run of
    /// separators holding a `\` is left with any of its `\` turned to `/`, or
    /// collapsed to one `/`.
    fn spellings(value: &str) -> Vec<String> {
        let mut out = vec![String::new()];
        let chars: Vec<char> = value.chars().collect();
        let mut at = 0;
        while at < chars.len() {
            let is_separator = |c: char| c == '/' || c == '\\';
            if !is_separator(chars[at]) {
                for s in &mut out {
                    s.push(chars[at]);
                }
                at += 1;
                continue;
            }
            let end = (at..chars.len())
                .find(|&i| !is_separator(chars[i]))
                .unwrap_or(chars.len());
            let run = &chars[at..end];
            let backslashes: Vec<usize> = (0..run.len()).filter(|&i| run[i] == '\\').collect();
            let mut variants: Vec<String> = Vec::new();
            for mask in 0..(1u32 << backslashes.len()) {
                let mut variant: Vec<char> = run.to_vec();
                for (bit, &i) in backslashes.iter().enumerate() {
                    if mask & (1 << bit) != 0 {
                        variant[i] = '/';
                    }
                }
                variants.push(variant.into_iter().collect());
            }
            if !backslashes.is_empty() {
                variants.push("/".to_string());
            }
            out = out
                .iter()
                .flat_map(|prefix| variants.iter().map(move |v| format!("{prefix}{v}")))
                .collect();
            at = end;
        }
        out
    }

    /// Every string up to `len` characters over `alphabet`.
    fn all_strings(alphabet: &[char], len: usize) -> Vec<String> {
        let mut all = vec![String::new()];
        let mut layer = vec![String::new()];
        for _ in 0..len {
            layer = layer
                .iter()
                .flat_map(|prefix| {
                    alphabet.iter().map(move |c| {
                        let mut s = prefix.clone();
                        s.push(*c);
                        s
                    })
                })
                .collect();
            all.extend(layer.iter().cloned());
        }
        all
    }

    /// Where `adjustment_is_immaterial` holds, every spelling the
    /// adjustments can leave has the walk's key (every `\` read as `/`), so
    /// MSBuild opens the walk's file under the walk's key whatever each
    /// adjustment decided.
    #[test]
    fn an_immaterial_adjustment_leaves_one_key() {
        let mut immaterial = 0;
        for value in all_strings(&['a', '.', '/', '\\'], 7) {
            if !value.contains('\\') || !adjustment_is_immaterial(&value) {
                continue;
            }
            immaterial += 1;
            let walk = key(&value.replace('\\', "/"));
            for spelling in spellings(&value) {
                assert_eq!(key(&spelling), walk, "{value:?} spelt {spelling:?}");
            }
        }
        assert!(immaterial > 500, "{immaterial}");
    }
}
