//! What may make MSBuild reject the whole project (#820, #845), and the
//! withdrawal that follows: [`crate::ParsedProject::rejection`].
//!
//! MSBuild fails the evaluation when an import it makes names no file it can
//! load, and then has no value for anything. The walk records the first such
//! construct as a [`Rejection`] and keeps going, for the read set and the
//! diagnostics; [`State::into_project`] withdraws what it publishes.
//!
//! Every site here is [`RejectionCertainty::Possible`]: it claims nothing
//! about MSBuild, so it needs no proof that MSBuild reaches the import. The
//! sites are:
//!
//! - an import the walk took whose path is empty or absent, which failed to
//!   load ([`State::push`]), or whose path it could not compute and may load
//!   nothing ([`taken_import_with_undecided_path`]);
//! - an import whose gate the walk could not decide and skipped, which MSBuild
//!   may make ([`undecided_import`]), and each import of an `<ImportGroup>` the
//!   walk skipped so ([`undecided_import_group`]);
//! - a `Directory.Build.*` import point the walk could not decide
//!   (`directory_build::visit_point`, through [`may_load_nothing_at`]).
//!
//! An import under a gate the walk could not decide is excused when the gate
//! is false whenever MSBuild's `Exists` of the import's own `Project` text is
//! (`Exists` as a conjunct, [`condition::requires_exists`]) and nothing is at
//! that path. `Exists` is true of a directory and of a dangling link, neither
//! of which an import loads, so either is still a rejection.
//!
//! **What is not judged.** Content the walk did not see may hold an import
//! that fails, or rewrite a value so that one the walk reached fails; the walk
//! cannot know of either. So a doubt that is only the walk's opacity — an
//! undefined read that would be exact had the walk seen every write, or a
//! value hidden content may have rewritten ([`super::Trust::stale`]) — is that
//! content's doubt, and the judgement reads such a name as the walk holds it
//! ([`certain_but_for_opacity`]), as every reader but the import points and
//! the Compile items does (#792). Nor is an SDK the walk cannot resolve: its
//! resolver may decline one MSBuild resolves. The pure walker follows no
//! import and judges none.

use std::collections::HashSet;
use std::ops::Range;
use std::path::{Path, PathBuf};

use roxmltree::Node;

use crate::diagnostic::{DiagnosticKind, ImportFailReason};
use crate::document::attribute;
use crate::imports::normalise;
use crate::{Rejection, RejectionCause, RejectionCertainty, UnloadableImport};

use super::item_pass::expand_silent;
use super::observed::{self, EntryKind};
use super::{
    SdkResolution, State, condition, condition_exists, import_dedup_key, properties,
    sdk_import_path, sdk_project_in_alphabet, sdk_project_under_root, sdk_root_is_reparsed,
};

impl State<'_> {
    /// Record that MSBuild may reject the project for `cause`, at `span`: the
    /// first such construct is the evaluation's [`Rejection`], and each gets a
    /// [`DiagnosticKind::MayBeRejected`].
    pub(super) fn note_possible_rejection(&mut self, cause: RejectionCause, span: Range<usize>) {
        if self.rejection.is_none() {
            self.rejection = Some(Rejection {
                certainty: RejectionCertainty::Possible,
                cause: cause.clone(),
                span: self.effective_span(span.clone()),
                origin: self.current_origin(),
            });
        }
        self.push(DiagnosticKind::MayBeRejected { cause }, span);
    }

    /// [`Self::note_possible_rejection`] for an import at `node` the walk took
    /// and cannot load.
    pub(super) fn note_unloadable_import(&mut self, node: Node<'_, '_>, why: UnloadableImport) {
        let project = attribute(node, "Project").unwrap_or_default().into_owned();
        self.note_possible_rejection(
            RejectionCause::Import {
                project,
                gate_undecided: false,
                why,
            },
            node.range(),
        );
    }
}

/// Whether a read of `name` now is the build's but for the walk's opacity: a
/// value no channel but staleness doubts, or an undefined read that would be
/// exact had the walk seen every write.
pub(super) fn certain_but_for_opacity(state: &State<'_>, name: &str) -> bool {
    !state.trust_of(name).reference_is_untrusted()
        && (state.lookup.is_bound(name) || state.undefined_read_is_exact_but_for_opacity(name))
}

/// What `condition` decides from the names [`certain_but_for_opacity`].
fn decision_but_for_opacity(
    state: &State<'_>,
    condition: &str,
    current_file_dir: &Path,
) -> condition::Decision {
    let observer = state.observer;
    let exists = |path: &str| condition_exists(observer, path, current_file_dir);
    let probes = state.follow_imports.then_some(condition::Probes {
        exists: &exists,
        observer,
    });
    let unknown = |name: &str| !certain_but_for_opacity(state, name);
    condition::decide_without(condition, &state.lookup, probes, &unknown)
}

/// Whether the gate at `node` holds in no build but one hidden content steers.
pub(super) fn ruled_out_but_for_opacity(
    node: Node<'_, '_>,
    current_file_dir: &Path,
    state: &State<'_>,
) -> bool {
    attribute(node, "Condition").is_some_and(|condition| {
        decision_but_for_opacity(state, &condition, current_file_dir)
            == condition::Decision::Decided(false)
    })
}

/// An import at `node` whose gate the walk could not decide and skipped:
/// MSBuild may make it.
pub(super) fn undecided_import(node: Node<'_, '_>, current_file_dir: &Path, state: &mut State<'_>) {
    undecided_import_within(node, current_file_dir, &mut HashSet::new(), state);
}

/// [`undecided_import`], `seen` holding the imports MSBuild would have made
/// earlier in the same speculative sequence, by [`import_dedup_key`].
fn undecided_import_within(
    node: Node<'_, '_>,
    current_file_dir: &Path,
    seen: &mut HashSet<String>,
    state: &mut State<'_>,
) {
    if ruled_out_but_for_opacity(node, current_file_dir, state) {
        return;
    }
    let Some(project) = attribute(node, "Project") else {
        state.note_possible_rejection(
            RejectionCause::Import {
                project: String::new(),
                gate_undecided: true,
                why: UnloadableImport::NoPath,
            },
            node.range(),
        );
        return;
    };
    let requires_own_file = requires_own_file(node, &project);
    if let Some(why) = may_load_nothing(
        node,
        &project,
        current_file_dir,
        requires_own_file,
        seen,
        state,
    ) {
        state.note_possible_rejection(
            RejectionCause::Import {
                project: project.into_owned(),
                gate_undecided: true,
                why,
            },
            node.range(),
        );
    }
}

/// The imports of an `<ImportGroup>` at `node` whose gate the walk could not
/// decide and skipped: MSBuild may make each one its own gate does not rule
/// out.
pub(super) fn undecided_import_group(
    node: Node<'_, '_>,
    current_file_dir: &Path,
    state: &mut State<'_>,
) {
    // The pure walker follows no import and reads no file, so it judges none.
    if !state.follow_imports || ruled_out_but_for_opacity(node, current_file_dir, state) {
        return;
    }
    // The group's imports run in order, so a later one may be a duplicate of an
    // earlier one MSBuild would have made.
    let mut seen = HashSet::new();
    for child in node.children().filter(|c| c.has_tag_name("Import")) {
        undecided_import_within(child, current_file_dir, &mut seen, state);
    }
}

/// An import at `node` the walk took, whose path it could not compute: MSBuild
/// makes it, and may load nothing.
pub(super) fn taken_import_with_undecided_path(
    node: Node<'_, '_>,
    current_file_dir: &Path,
    state: &mut State<'_>,
) {
    let project = attribute(node, "Project").unwrap_or_default();
    let requires_own_file = requires_own_file(node, &project);
    let mut seen = HashSet::new();
    if let Some(why) = may_load_nothing(
        node,
        &project,
        current_file_dir,
        requires_own_file,
        &mut seen,
        state,
    ) {
        state.note_unloadable_import(node, why);
    }
}

/// Whether the gate of the import at `node` of `project` is false whenever
/// MSBuild's `Exists` of `project` is: its own condition, or that of the
/// `<ImportGroup>` around it, which gates it as much, has that `Exists` as a
/// conjunct. An SDK import's path is not the `Exists` argument's, so none is.
fn requires_own_file(node: Node<'_, '_>, project: &str) -> bool {
    let is_own_file = |arg: &str| arg == project;
    let requires = |gate: Node<'_, '_>| {
        attribute(gate, "Condition")
            .is_some_and(|condition| condition::requires_exists(&condition, &is_own_file))
    };
    attribute(node, "Sdk").is_none()
        && (requires(node)
            || node
                .parent_element()
                .is_some_and(|parent| parent.has_tag_name("ImportGroup") && requires(parent)))
}

/// Why an import of `project` at `node`, which MSBuild may make, may load no
/// file, or `None` when every file it names loads. `requires_own_file`: its
/// gate is false whenever MSBuild's `Exists` of `project` is.
fn may_load_nothing(
    node: Node<'_, '_>,
    project: &str,
    current_file_dir: &Path,
    requires_own_file: bool,
    seen: &mut HashSet<String>,
    state: &State<'_>,
) -> Option<UnloadableImport> {
    if let Some(sdk) = attribute(node, "Sdk") {
        return sdk_import_may_load_nothing(&sdk, project, seen, state);
    }
    let expansion = expand_silent(project, state);
    if path_undecided(project, state, expansion.had_unsupported) {
        return (!requires_own_file).then_some(UnloadableImport::PathUndecided);
    }
    // Its trust is judged just above, name by name.
    let value = expansion.value.ignoring_trust();
    if requires_own_file {
        let whole = current_file_dir.join(value.unescape().replace('\\', "/"));
        if value.trimmed_unescaped().is_empty()
            || observed::link_kind(state.observer, &normalise(&whole)).is_err()
        {
            return None;
        }
    }
    if value.as_escaped().trim().is_empty() && !value.as_escaped().contains(';') {
        return Some(UnloadableImport::NoPath);
    }
    value
        .split_list()
        .filter(|segment| !segment.is_filespec_wildcard())
        .find_map(|segment| {
            let path = current_file_dir.join(segment.unescape().replace('\\', "/"));
            load_failure(state, &path, seen).map(UnloadableImport::Failed)
        })
}

/// Whether the walk cannot compute `project`: it reads a name not
/// [`certain_but_for_opacity`], or holds an expression the walk leaves as
/// text.
fn path_undecided(project: &str, state: &State<'_>, had_unsupported: bool) -> bool {
    had_unsupported
        || properties::property_references(project)
            .any(|name| !certain_but_for_opacity(state, name))
}

/// [`may_load_nothing`] for an import of `project` from the SDK `sdk`.
fn sdk_import_may_load_nothing(
    sdk: &str,
    project: &str,
    seen: &mut HashSet<String>,
    state: &State<'_>,
) -> Option<UnloadableImport> {
    let resolution = state
        .sdk_resolver
        .and_then(|resolver| resolver(sdk, state.observer).ok())?;
    let expansion = expand_silent(project, state);
    if path_undecided(project, state, expansion.had_unsupported) {
        return Some(UnloadableImport::PathUndecided);
    }
    // Judged name by name just above.
    let value = expansion.value.ignoring_trust();
    let relative = value.unescape();
    if relative.trim().is_empty() {
        return Some(UnloadableImport::NoPath);
    }
    // The file the walk would name, by the walk's own rules
    // (`follow_import_after_gate`): outside its alphabet, or under a root
    // MSBuild re-parses, it does not say what MSBuild names.
    if !sdk_project_in_alphabet(value.as_escaped(), &relative) {
        return Some(UnloadableImport::PathUndecided);
    }
    let relative = relative.replace('\\', "/");
    if relative.ends_with('/') {
        return Some(UnloadableImport::Failed(ImportFailReason::NotFound));
    }
    let under_root = sdk_project_under_root(project, &relative);
    let roots: Vec<PathBuf> = match resolution {
        SdkResolution::Single(paths) => match relative.as_str() {
            "Sdk.props" => {
                return load_failure(state, &paths.props, seen).map(UnloadableImport::Failed);
            }
            "Sdk.targets" => {
                return load_failure(state, &paths.targets, seen).map(UnloadableImport::Failed);
            }
            _ => vec![paths.root],
        },
        SdkResolution::Roots(roots) => roots,
    };
    roots.iter().find_map(|root| {
        if sdk_root_is_reparsed(root) {
            return Some(UnloadableImport::PathUndecided);
        }
        match sdk_import_path(root, under_root) {
            Ok(path) => load_failure(state, &path, seen).map(UnloadableImport::Failed),
            Err(e) => Some(UnloadableImport::Failed(ImportFailReason::Io {
                message: e.to_string(),
            })),
        }
    })
}

/// Why the file at `path` does not load as an import, or `None` when it does
/// or MSBuild skips it as a duplicate: it is missing, not a file (a directory,
/// a dangling link), unreadable, or not well-formed XML. The path is collapsed
/// lexically first, as MSBuild collapses an import's.
fn load_failure(
    state: &State<'_>,
    path: &Path,
    seen: &mut HashSet<String>,
) -> Option<ImportFailReason> {
    // `NormalizePath` is `GetFullPath`: a relative path resolves against the
    // working directory before `..` collapses.
    let path = match std::path::absolute(path) {
        Ok(path) => normalise(&path),
        Err(e) => {
            return Some(ImportFailReason::Io {
                message: e.to_string(),
            });
        }
    };
    // MSBuild skips an import of a path it has already imported, by its own
    // identity for one (`import_dedup_key`), without loading it.
    let key = import_dedup_key(&path);
    if state.imports_seen.contains(&key) || seen.contains(&key) {
        return None;
    }
    if observed::kind(state.observer, &path) != Ok(EntryKind::File) {
        return Some(ImportFailReason::NotFound);
    }
    match observed::read_document(state.observer, &path) {
        Ok(Ok(_)) => {
            seen.insert(key);
            None
        }
        Ok(Err(e)) => Some(ImportFailReason::MalformedXml {
            message: e.to_string(),
        }),
        Err(e) => Some(ImportFailReason::Io {
            message: e.to_string(),
        }),
    }
}

/// Why a `Directory.Build.*` import point whose gate the walk could not
/// decide may load nothing: its path is `path` (`None` when it names nothing)
/// and `certain` says whether the walk computes it, but for its opacity.
/// `guarded`: the gate is false whenever MSBuild's `Exists` of the path is.
pub(super) fn may_load_nothing_at(
    state: &State<'_>,
    path: Option<&Path>,
    certain: bool,
    guarded: bool,
) -> Option<UnloadableImport> {
    if !certain {
        return (!guarded).then_some(UnloadableImport::PathUndecided);
    }
    let Some(path) = path else {
        return (!guarded).then_some(UnloadableImport::NoPath);
    };
    if guarded && observed::link_kind(state.observer, &normalise(path)).is_err() {
        return None;
    }
    load_failure(state, path, &mut HashSet::new()).map(UnloadableImport::Failed)
}
