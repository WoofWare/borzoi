//! `Directory.Build.props` and `Directory.Build.targets` (#677).
//!
//! MSBuild has no implicit import of either file. `Microsoft.Common.props`
//! imports the first and `Microsoft.Common.targets` (and its cross-targeting
//! twin) the second, each through an ordinary `<Import>` of
//! `$(DirectoryBuild{Props,Targets}Path)` under a condition that reads the
//! file's gate (`ImportDirectoryBuild{Props,Targets}`) and tests the file
//! exists. So the walk follows those imports, at their own positions and
//! under their own conditions, and a project no SDK reaches gets neither file.
//!
//! **The domain.** An import point is *decided*, and followed as an ordinary
//! import, exactly when [`is_decided_point`] holds, which is all of:
//!
//! - the walk is not opaque there ([`State::walk_opaque`]): content it could
//!   not see may have imported the file already, which would make this import
//!   a duplicate MSBuild skips;
//! - the walk reached it along a route of import gates it decided
//!   ([`Bookkeeping::route_undecided`]);
//! - its condition is a conjunction each of whose conjuncts is either decided
//!   from certain inputs on its own, or exactly `Exists` of the point's own
//!   `Project` path ([`condition::decided_conjunctwise`]);
//! - the path property is certain, and names one literal file: no `;` list and
//!   no wildcard ([`names_one_file`]).
//!
//! "Certain" is [`Trust::is_certain`](super::Trust::is_certain) on the entry the read
//! consults, which joins every channel, [`Trust::stale`](super::Trust::stale) included; a name with
//! no binding is certain only when [`State::undefined_read_is_exact`] says the
//! real build has none either. Nothing else is decided, however precise a
//! special case could be: a shape that deserves precision declines until it is
//! added here.
//!
//! **The fallback.** Every other point the walk reaches, and every point it
//! never reaches once it has passed something it could not decide (which may
//! hold the point), is settled by [`fallback`]: any file may be imported, so
//! the whole evaluation from there is uncertain. Every property bound so far is
//! unpinned, the walk latches opacity, and every item facet and the define set
//! are withdrawn; the file the path names (or the one discovered by default) is
//! then walked doubted, so that what it writes is doubted too. When nothing
//! would be imported by default (no write touched the path and no
//! `Directory.Build.*` file exists above the project), and the point's
//! condition is false whenever `Exists` of its path is (or the walk never
//! reached the point), the walk's doubt is about a file only content it could
//! not see would name, which is that content's doubt like any other, and
//! nothing is charged. A reached point whose condition can hold without the
//! file (`X Or Exists(…)`) imports the path regardless, which MSBuild rejects
//! when it names nothing, so it is charged.
//!
//! An evaluation makes at most [`MAX_DOUBTED_WALKS`] doubted walks: past the
//! bound, a file the fallback would walk is content the walk does not see, and
//! the whole evaluation is uncertain from there.
//!
//! **What a doubted walk may leave behind.** A fallback walk follows the file
//! as an ordinary import, but MSBuild may not make that import, so nothing it
//! does may stand as certain. Every field of the walk state it can change, and
//! why each is safe:
//!
//! - `imports_seen`, `imports_seen_fuzzy`: never changed. A fallback walk
//!   registers its imports in [`Bookkeeping::doubted_imports`] instead, by the
//!   walk's number, so the certain set holds certain imports only. A later
//!   import of a file only a fallback walk made is a duplicate within that walk
//!   or one inside it, is walked with an enclosing fallback walk, and otherwise
//!   is walked again, doubted ([`doubted_duplicate`]): MSBuild made the import
//!   there or earlier, and which is unknown.
//! - `lookup`, `written`: the values written stay, and every name written (or
//!   whose write was skipped or refused) is unpinned when the walk returns.
//!   Opacity and staleness the walk latches only add doubt.
//! - `deferred_item_groups`, `retained_imported_files`: the file's items are
//!   replayed in the item pass, and every facet they reach is withdrawn:
//!   Compile and packages always, `<ProjectReference>` when the file declares
//!   or defines one.
//! - `protected`, `depth`, `import_site_span`, `current_file`,
//!   `in_sdk_subtree`, `enclosing_condition_stale`: restored per frame.
//! - `diagnostics`, `diagnostic_roots`, the `*_uncertain` flags and their
//!   causes, `walk_opaque`, `target_framework_read_exempted`: only add doubt.
//! - `walked_files`, `walked_directory_packages_props_import`: read only by the
//!   central-package discharge, which can only clear the package uncertainty
//!   the walk's withdrawal has already set.
//! - `foreign_definitions`, `workload_definitions`,
//!   `sdk_files_imported_from_outside`, `locally_overridable`:
//!   over-approximations by construction, recorded whatever decides a file's
//!   import.
//! - `default_targets_decided` and `MSBuildProjectDefaultTargets`: a root a
//!   fallback walk reaches settles the property unset, and an `MSBuild`-prefixed
//!   name read unset is never exact.
//! - `sdk_tolerance_roots`, [`Bookkeeping::nested_sdk_roots`] and the toolset
//!   seed: the roots classify files by path, and only that SDK's own files sit
//!   under them; the seed is the toolset's, which MSBuild holds either way.
//! - `target_definitions`, `initial_targets_named`, `using_task_names`: a
//!   target read is exact only when no fallback walk contributed.
//! - The item and package tables (`compile_*`, `project_references`,
//!   `package_*`, …): filled only by the item pass. `resolved_sdk_root`,
//!   `entry_sdk_version_dir`, `hoisted_sdk_imports`: the entry project's only.
//!
//! A point never reached by a walk that decided everything is never reached
//! by MSBuild either, and imports nothing. Under opacity, the walk has
//! accounted for the SDK's import of a file only at a point that names the
//! default file ([`names_the_default`]): a point that names another stands
//! beside the SDK's own, which may be in content the walk could not see.

use std::path::{Path, PathBuf};

use roxmltree::Node;

use crate::document::attribute;

use super::condition;
use super::observed;
use super::properties;
use super::properties::trust::{
    OpacityCause, PropertyProvenance, RefusedOutcome, StaleOutcome, TaintOutcome, UnpinnedOutcome,
    UnpinnedRoot,
};
use super::{
    CurrentFile, State, StructuralCompileItemUncertainty, canonicalise_or_normalise,
    condition_exists, condition_has_exists_for_property, import_dedup_key,
    simple_property_reference, walk_external_file,
};

/// Which of the two files.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DirectoryBuildFile {
    Props,
    Targets,
}

impl DirectoryBuildFile {
    pub(crate) const ALL: [DirectoryBuildFile; 2] =
        [DirectoryBuildFile::Props, DirectoryBuildFile::Targets];

    /// The property the SDK's import condition reads to decide whether to
    /// import the file. The walk never reads it itself: the SDK's condition
    /// does.
    #[cfg(test)]
    pub(crate) fn gate_name(self) -> &'static str {
        match self {
            DirectoryBuildFile::Props => "ImportDirectoryBuildProps",
            DirectoryBuildFile::Targets => "ImportDirectoryBuildTargets",
        }
    }

    /// The property the SDK's import names the file by.
    pub(crate) fn path_name(self) -> &'static str {
        match self {
            DirectoryBuildFile::Props => "DirectoryBuildPropsPath",
            DirectoryBuildFile::Targets => "DirectoryBuildTargetsPath",
        }
    }

    /// The `Project` text of the SDK's import of the file.
    fn project(self) -> String {
        format!("$({})", self.path_name())
    }

    fn file_name(self) -> &'static str {
        match self {
            DirectoryBuildFile::Props => "Directory.Build.props",
            DirectoryBuildFile::Targets => "Directory.Build.targets",
        }
    }

    fn index(self) -> usize {
        match self {
            DirectoryBuildFile::Props => 0,
            DirectoryBuildFile::Targets => 1,
        }
    }

    /// The root every fallback product of this file carries.
    fn root(self) -> UnpinnedRoot {
        UnpinnedRoot::UnsupportedCondition(format!(
            "the {} import, which the walk could not decide",
            self.file_name()
        ))
    }
}

/// The walk's record of the two import points.
#[derive(Debug, Default)]
pub(super) struct Bookkeeping {
    /// The nearest file of each kind above the project, as discovered before
    /// the walk: what the SDK's discovery would name by default.
    discovered: [Option<PathBuf>; 2],
    /// Whether the walk has accounted for the SDK's import of each kind: it
    /// reached an import point of that kind that names the default file
    /// ([`names_the_default`]), or settled one it could not decide.
    accounted: [bool; 2],
    /// How many imports the walk is inside whose gate it did not decide from
    /// certain inputs: a point reached inside one is not decided.
    route_undecided: usize,
    /// Whether the walk met an import gate it did not decide from certain
    /// inputs, whichever way it went. Every such gate also latches opacity
    /// except one deciding cleanly on an input another channel doubts.
    undecided_gate_seen: bool,
    /// The canonical roots of the SDKs an imported file's own `Sdk`
    /// attribute names. The walk does not tolerate their files as the entry
    /// SDK's ([`State::in_sdk_subtree`]), but their `Microsoft.Common.*`
    /// imports are import points all the same.
    nested_sdk_roots: Vec<PathBuf>,
    /// Set while the walk is inside a fallback walk: the root its products
    /// carry.
    pub(super) fallback: Option<UnpinnedRoot>,
    /// The names a fallback walk wrote (or skipped or refused a write of),
    /// unpinned when it returns. Not as they are written: inside the file the
    /// walk follows its imports and conditions as an ordinary import, so that
    /// doubting the file loses nothing it would do.
    doubted_writes: Vec<String>,
    /// The imports a fallback walk made, by their key ([`import_dedup_key`]),
    /// each with the walk's number: a fallback walk registers its imports here
    /// and never in [`State::imports_seen`], which holds certain imports only.
    doubted_imports: std::collections::HashMap<String, usize>,
    /// The near-duplicate keys (`import_dedup_fuzzy_key`) of the same imports,
    /// each with the keys of the imports it is the near-duplicate key of.
    doubted_fuzzy: std::collections::HashMap<String, Vec<String>>,
    /// The numbers of the fallback walks the walk is inside, innermost last,
    /// and how many have run.
    doubted_walk: Vec<usize>,
    doubted_walks: usize,
    /// Whether a fallback walked a file that contributes something.
    pub(super) contributed: bool,
    /// Whether a group the walk deferred while inside a fallback walk declares
    /// or defines `<ProjectReference>` items.
    pub(super) doubted_references: bool,
}

impl Bookkeeping {
    pub(super) fn discover(&mut self, props: Option<&Path>, targets: Option<&Path>) {
        self.discovered = [props.map(Path::to_path_buf), targets.map(Path::to_path_buf)];
    }

    /// Record a write of `name`, if the walk is inside a fallback walk.
    pub(super) fn note_write(&mut self, name: &str) {
        if self.fallback.is_some() {
            self.doubted_writes.push(name.to_owned());
        }
    }

    /// Register an import: in [`State::imports_seen`] when it is certain, and
    /// in [`Self::doubted_imports`] when a fallback walk makes it.
    pub(super) fn register_import(
        &mut self,
        key: String,
        fuzzy: String,
        imports_seen: &mut std::collections::HashSet<String>,
        imports_seen_fuzzy: &mut std::collections::HashSet<String>,
    ) {
        match self.doubted_walk.last() {
            Some(&walk) => {
                let keys = self.doubted_fuzzy.entry(fuzzy).or_default();
                if !keys.contains(&key) {
                    keys.push(key.clone());
                }
                self.doubted_imports.insert(key, walk);
            }
            None => {
                imports_seen.insert(key);
                imports_seen_fuzzy.insert(fuzzy);
            }
        }
    }

    /// Whether an import with key `key` and near-duplicate key `fuzzy` is a
    /// near-duplicate of an import a fallback walk made: one with the same
    /// near-duplicate key and another key. An import with the same key is
    /// [`doubted_duplicate`]'s to settle.
    pub(super) fn doubted_near_duplicate(&self, key: &str, fuzzy: &str) -> bool {
        self.doubted_fuzzy
            .get(fuzzy)
            .is_some_and(|keys| keys.iter().any(|other| other != key))
    }
}

/// What [`doubted_duplicate`] leaves its caller to do with an import.
pub(super) enum Doubted {
    /// No fallback walk made it, or this one may make it again: walk it.
    Walk,
    /// Settled here: a duplicate within the fallback walk that made it, or
    /// walked again, doubted.
    Settled,
}

/// An import of `path` the walk has not certainly made. When a fallback walk
/// made it (one MSBuild may not have made), it is a duplicate only within that
/// walk or one inside it (a cycle). Inside another fallback walk the import is
/// walked as any other, doubted with it. Outside every one, MSBuild has made
/// it here or before, and the walk cannot tell which, so it walks it again,
/// doubted.
pub(super) fn doubted_duplicate(path: &Path, key: &str, state: &mut State<'_>) -> Doubted {
    let bookkeeping = &state.directory_build;
    let Some(walk) = bookkeeping.doubted_imports.get(key) else {
        return Doubted::Walk;
    };
    if bookkeeping.doubted_walk.contains(walk) {
        return Doubted::Settled;
    }
    if !bookkeeping.doubted_walk.is_empty() {
        return Doubted::Walk;
    }
    if !contributes_nothing(path, state) {
        let root = UnpinnedRoot::UnsupportedCondition(format!(
            "the import of {}, which a doubted Directory.Build.* file may already have made",
            path.display()
        ));
        walk_doubted_as(root, &path.display().to_string(), path, state);
    }
    Doubted::Settled
}

/// Record the root of an SDK an imported file's own `Sdk` attribute names.
pub(super) fn note_nested_sdk(root: &Path, state: &mut State<'_>) {
    let canon = canonicalise_or_normalise(state.observer, root);
    if !state.directory_build.nested_sdk_roots.contains(&canon) {
        state.directory_build.nested_sdk_roots.push(canon);
    }
}

/// Whether the file being walked is one of an SDK's: the entry SDK's (or one
/// tolerated with it), or one under the root of a nested SDK.
fn in_an_sdk_file(state: &State<'_>) -> bool {
    if state.in_sdk_subtree {
        return true;
    }
    let CurrentFile::Imported { path, .. } = &state.current_file else {
        return false;
    };
    let canon = canonicalise_or_normalise(state.observer, path);
    state
        .directory_build
        .nested_sdk_roots
        .iter()
        .any(|root| canon.starts_with(root))
}

/// Whether `node`, an `<Import>`, is an SDK's import point for a
/// `Directory.Build.*` file: in an SDK's file ([`in_an_sdk_file`]), of
/// `$(DirectoryBuild{Props,Targets}Path)` alone, not qualified by an SDK,
/// under a condition that tests the file exists. The shape, not the path, so
/// an SDK's import point is one wherever the SDK puts it.
pub(super) fn point_kind(node: Node<'_, '_>, state: &State<'_>) -> Option<DirectoryBuildFile> {
    if attribute(node, "Sdk").is_some() || !in_an_sdk_file(state) {
        return None;
    }
    let project = attribute(node, "Project")?;
    let name = simple_property_reference(&project)?;
    let kind = DirectoryBuildFile::ALL
        .into_iter()
        .find(|kind| kind.path_name().eq_ignore_ascii_case(name))?;
    condition_has_exists_for_property(attribute(node, "Condition").as_deref(), name).then_some(kind)
}

/// What [`visit_point`] leaves its caller to do.
pub(super) enum Visit {
    /// The point is decided: follow it as an ordinary import.
    Follow,
    /// The point is not decided, and the fallback has settled it.
    Settled,
}

/// Account for the walk reaching an import point of `kind` at `node`, before
/// anything else happens there.
pub(super) fn visit_point(
    node: Node<'_, '_>,
    kind: DirectoryBuildFile,
    current_file_dir: &Path,
    state: &mut State<'_>,
) -> Visit {
    if is_decided_point(node, kind, current_file_dir, state) {
        if names_the_default(kind, current_file_dir, state) {
            state.directory_build.accounted[kind.index()] = true;
        }
        return Visit::Follow;
    }
    // The whole evaluation is uncertain from here: nothing a later point could
    // import adds to that.
    state.directory_build.accounted[kind.index()] = true;
    let named = named_file(state, kind.path_name(), current_file_dir);
    let condition = attribute(node, "Condition").unwrap_or_default();
    let guarded = condition::requires_exists(&condition, &|arg| is_the_path(arg, kind));
    fallback(kind, named, guarded, state);
    Visit::Settled
}

/// Whether `arg`, an `Exists` argument, is exactly the point's own path.
fn is_the_path(arg: &str, kind: DirectoryBuildFile) -> bool {
    simple_property_reference(arg).is_some_and(|name| name.eq_ignore_ascii_case(kind.path_name()))
}

/// The domain of a decided import point (see the module docs): the one place
/// it is stated.
fn is_decided_point(
    node: Node<'_, '_>,
    kind: DirectoryBuildFile,
    current_file_dir: &Path,
    state: &State<'_>,
) -> bool {
    let path_name = kind.path_name();
    let condition = attribute(node, "Condition").unwrap_or_default();
    let project = attribute(node, "Project").unwrap_or_default();
    let observer = state.observer;
    let exists = |path: &str| condition_exists(observer, path, current_file_dir);
    let probes = state.follow_imports.then_some(condition::Probes {
        exists: &exists,
        observer,
    });
    let unknown = |name: &str| !is_certain(state, name);
    let is_the_exists = |arg: &str| is_the_path(arg, kind);
    state.walk_opaque.is_none()
        && state.directory_build.route_undecided == 0
        && condition::decided_conjunctwise(
            &condition,
            &state.lookup,
            probes,
            &unknown,
            &is_the_exists,
        )
        && properties::property_references(&project).all(|name| is_certain(state, name))
        && is_certain(state, path_name)
        && names_one_file(state, path_name)
}

/// Whether the import point here names the file the SDK's discovery names by
/// default: by MSBuild's identity for an import ([`import_dedup_key`]), or, with
/// no file to discover, by naming none. A point that names another file (a
/// redirect, an alias) stands beside the SDK's own import, which content the
/// walk could not see may still make.
fn names_the_default(kind: DirectoryBuildFile, dir: &Path, state: &State<'_>) -> bool {
    let named = point_path(state, kind.path_name(), dir);
    match (&state.directory_build.discovered[kind.index()], named) {
        (Some(default), Some(named)) => import_dedup_key(default) == import_dedup_key(&named),
        (None, None) => true,
        _ => false,
    }
}

/// Whether the gate of an `<Import>` or `<ImportGroup>` at `node` is decided
/// from certain inputs; called before the walk evaluates it.
pub(super) fn gate_is_decided(
    node: Node<'_, '_>,
    current_file_dir: &Path,
    state: &mut State<'_>,
) -> bool {
    let decided = attribute(node, "Condition")
        .is_none_or(|condition| decided_from_certain_inputs(state, &condition, current_file_dir));
    if !decided {
        state.directory_build.undecided_gate_seen = true;
    }
    decided
}

/// Run `walk` (the imports of an element whose gate the walk took) as inside
/// an undecided route when `decided` is false.
pub(super) fn within_route<T>(
    decided: bool,
    state: &mut State<'_>,
    walk: impl FnOnce(&mut State<'_>) -> T,
) -> T {
    if decided {
        return walk(state);
    }
    state.directory_build.route_undecided += 1;
    let result = walk(state);
    state.directory_build.route_undecided -= 1;
    result
}

/// Settle each file whose import by the SDK the walk has not accounted for,
/// once every import it could follow is behind it.
pub(super) fn settle_unaccounted(state: &mut State<'_>) {
    for kind in DirectoryBuildFile::ALL {
        if state.directory_build.accounted[kind.index()] {
            continue;
        }
        if state.walk_opaque.is_none() && !state.directory_build.undecided_gate_seen {
            // Every gate decided and nothing hidden: MSBuild reaches no point
            // the walk did not.
            continue;
        }
        // The point, wherever it is, is somewhere the walk did not go, and
        // reads the path as it is there:
        // bound by the SDK's own discovery just before it, or by a write the
        // walk never saw, or left as some write earlier than the last the walk
        // holds. The file the path names now is only the likeliest.
        let project_dir = state.entry_project_dir.clone();
        let named = named_file(state, kind.path_name(), &project_dir);
        // A point the walk never reached is in content it could not see, and
        // whatever that point's condition does is that content's doubt.
        fallback(kind, named, true, state);
    }
}

/// See the module docs. `guarded`: the point's condition is false whenever
/// `Exists` of its path is ([`condition::requires_exists`]).
fn fallback(
    kind: DirectoryBuildFile,
    named: Option<PathBuf>,
    guarded: bool,
    state: &mut State<'_>,
) {
    // A path some write touched (bound, or left doubted by a write the walk
    // skipped or refused) may name a file the walk cannot see from here.
    let path_name = kind.path_name();
    let path_touched = state.lookup.is_bound(path_name) || !state.trust_of(path_name).is_certain();
    let file = named.or_else(|| state.directory_build.discovered[kind.index()].clone());
    if guarded && !path_touched && file.is_none() {
        return;
    }
    whole_evaluation_uncertain(kind, state);
    if let Some(file) = file {
        walk_doubted(kind, &file, state);
    }
}

/// Walk `file`, whose import is in doubt, so that everything it writes is
/// doubted too, and withdraw the facets it could change.
fn walk_doubted(kind: DirectoryBuildFile, file: &Path, state: &mut State<'_>) {
    if state.imports_seen.contains(&import_dedup_key(file)) || contributes_nothing(file, state) {
        return;
    }
    walk_doubted_as(kind.root(), &kind.project(), file, state);
}

/// [`walk_doubted`] for any doubted import: `root` is what its products carry
/// and `project` the import's `Project` text.
fn walk_doubted_as(root: UnpinnedRoot, project: &str, file: &Path, state: &mut State<'_>) {
    if state.directory_build.doubted_walks >= MAX_DOUBTED_WALKS {
        // Past the bound the file is content the walk does not see: nothing
        // it would write or contribute stands, as after any hidden content.
        state.directory_build.contributed = true;
        everything_uncertain(project, root, state);
        return;
    }
    state.directory_build.contributed = true;
    state.directory_build.doubted_walks += 1;
    let walk = state.directory_build.doubted_walks;
    state.directory_build.doubted_walk.push(walk);
    let saved_fallback = state.directory_build.fallback.replace(root.clone());
    let saved_references = std::mem::take(&mut state.directory_build.doubted_references);
    let saved_writes = std::mem::take(&mut state.directory_build.doubted_writes);
    let saved_span = state.import_site_span.take();
    walk_external_file(file, 0..0, state);
    state.import_site_span = saved_span;
    state.directory_build.fallback = saved_fallback;
    state.directory_build.doubted_walk.pop();
    let references = state.directory_build.doubted_references;
    state.directory_build.doubted_references |= saved_references;
    // MSBuild may not make any of these writes, so the value each name holds
    // may be the one before it.
    let written = std::mem::replace(&mut state.directory_build.doubted_writes, saved_writes);
    for name in written {
        unpin(&name, &root, state);
    }
    withdraw_facets(project, root, references, state);
}

/// Record `root` against `name`, leaving its value alone.
fn unpin(name: &str, root: &UnpinnedRoot, state: &mut State<'_>) {
    state.apply_property_provenance(
        name,
        PropertyProvenance {
            taint: TaintOutcome::Keep,
            unpinned: UnpinnedOutcome::Set(root.clone()),
            refused: RefusedOutcome::Keep,
            stale: StaleOutcome::Keep,
        },
    );
}

/// The doubted walks one evaluation makes, at most. A doubted walk may walk
/// again a file an earlier one walked ([`doubted_duplicate`]), so files that
/// import each other through undecided points could otherwise be walked a
/// number of times exponential in their count. Real projects make a handful.
const MAX_DOUBTED_WALKS: usize = 64;

/// The whole evaluation from here is uncertain: any file may be imported.
fn whole_evaluation_uncertain(kind: DirectoryBuildFile, state: &mut State<'_>) {
    everything_uncertain(&kind.project(), kind.root(), state);
}

/// [`whole_evaluation_uncertain`] for an import whose `Project` text is
/// `project`, its products carrying `root`.
fn everything_uncertain(project: &str, root: UnpinnedRoot, state: &mut State<'_>) {
    state.latch_walk_opaque(OpacityCause::Gate(root.clone()));
    let names: Vec<String> = state.lookup.canonical_keys().map(str::to_owned).collect();
    for name in names {
        if !state.protected.contains(&name.to_ascii_lowercase()) {
            unpin(&name, &root, state);
        }
    }
    withdraw_facets(project, root, true, state);
}

/// Withdraw the captured item facets and the define set. Through
/// `mark_structural_skip` rather than its SDK-tolerant twin, wherever the
/// point is: a `Directory.Build.*` file holds hand-written sources and
/// `<PackageReference>`s, and its properties can steer the SDK's own items.
/// The `<ProjectReference>` list only when `references`: the SDK declares no
/// reference, so a file changes the list only through its own items, and a
/// body item reading what the file writes reads a doubted value.
fn withdraw_facets(project: &str, root: UnpinnedRoot, references: bool, state: &mut State<'_>) {
    state.mark_structural_skip(
        StructuralCompileItemUncertainty::DirectoryBuildImportUndecided {
            project: project.to_string(),
            references,
        },
        0..0,
    );
    let saved = state.define_context;
    state.define_context = true;
    state.push_root(root, 0..0);
    state.define_context = saved;
}

/// Whether the file at `path` writes nothing: a `<Project>` with no attribute
/// but a namespace and no element child. Anything else may write a property,
/// declare an item, import a file, define a target, or decide one; a file that
/// does not read or parse is no file to call empty.
fn contributes_nothing(path: &Path, state: &State<'_>) -> bool {
    let canon = canonicalise_or_normalise(state.observer, path);
    let Ok(Ok(parsed)) = observed::read_document(state.observer, &canon) else {
        return false;
    };
    let root = parsed.document().root_element();
    root.has_tag_name("Project")
        && root.attributes().all(|a| a.name() == "xmlns")
        && !root.children().any(|child| child.is_element())
}

/// The file the path property names, resolved against `dir` as an import
/// there resolves it.
fn point_path(state: &State<'_>, path_name: &str, dir: &Path) -> Option<PathBuf> {
    // A point of use: trimmed in the domain (an escaped `%20` is filename
    // data, not padding). Its trust is the caller's to judge.
    let trimmed = state
        .lookup
        .get_ignoring_trust(path_name)?
        .trimmed_unescaped();
    if trimmed.is_empty() {
        return None;
    }
    let normalised = trimmed.replace('\\', "/");
    let path = Path::new(&normalised);
    Some(if path.is_absolute() {
        path.to_path_buf()
    } else {
        dir.join(path)
    })
}

/// Whether the path property names at most one file: a value that is no list
/// and no wildcard, classified in the escaped domain as an import's `Project`
/// is. A list or a wildcard imports every file it names or matches.
fn names_one_file(state: &State<'_>, path_name: &str) -> bool {
    state
        .lookup
        .get_ignoring_trust(path_name)
        .is_none_or(|value| !value.as_escaped().contains(';') && !value.is_filespec_wildcard())
}

/// [`point_path`], if the file exists.
fn named_file(state: &State<'_>, path_name: &str, dir: &Path) -> Option<PathBuf> {
    point_path(state, path_name, dir).filter(|path| observed::exists(state.observer, path))
}

/// Whether a read of `name` now is what the real build reads. An undefined
/// `TargetFramework` is judged by the walk's mode, as every other read of it
/// is, and leaning on its exactness is recorded as every other read records it.
fn is_certain(state: &State<'_>, name: &str) -> bool {
    state.trust_of(name).is_certain()
        && (state.lookup.is_bound(name) || state.undefined_read_is_exact(name))
}

/// Whether `condition` decides the same way whatever the names the walk is
/// not certain of hold ([`is_certain`]), within the grammar. The pure walker
/// has no file system, so an `Exists` leaf is outside it there.
fn decided_from_certain_inputs(state: &State<'_>, condition: &str, dir: &Path) -> bool {
    let observer = state.observer;
    let exists = |path: &str| condition_exists(observer, path, dir);
    let probes = state.follow_imports.then_some(condition::Probes {
        exists: &exists,
        observer,
    });
    let unknown = |name: &str| !is_certain(state, name);
    matches!(
        condition::decide_without(condition, &state.lookup, probes, &unknown),
        condition::Decision::Decided(_)
    )
}
