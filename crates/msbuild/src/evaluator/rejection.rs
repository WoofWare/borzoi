//! What may make MSBuild reject the whole project (#820, #845, #783), and the
//! withdrawal that follows: [`crate::ParsedProject::rejection`].
//!
//! MSBuild fails the evaluation when an import it makes names no file it can
//! load, when a file it loads breaks its loader's schema ([`judge_load_time`],
//! #888, #917), or when a condition it evaluates throws, and then has no value
//! for anything. The walk records the first such construct as a [`Rejection`]
//! (the first [`RejectionCertainty::Certain`] one, if any) and keeps going,
//! for the read set and the diagnostics; [`State::into_project`] withdraws
//! what it publishes.
//!
//! **Possible.** A [`RejectionCertainty::Possible`] site claims nothing about
//! MSBuild, so it needs no proof that MSBuild reaches it. The import sites are:
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
//! A condition the walk evaluates to [`condition::Outcome::Illegal`] is a
//! site too ([`illegal_condition_at`]), and so is one MSBuild may evaluate
//! where the walk does not: under a gate the walk could not decide from
//! certain inputs ([`judge_unwalked`]), and every condition of the item pass,
//! judged group by group ([`judge_deferred`]) where a build evaluates it
//! (below), since the walk's item capture gates an illegal condition's
//! contents as an unmodelled one's. A group of the item pass in a branch the
//! walk could not decide is judged there too, against the final property
//! table as MSBuild evaluates it ([`State::defer_judgement`]), not against the
//! properties the walk holds where it meets the group.
//!
//! **Certain.** A [`RejectionCertainty::Certain`] site is a claim the
//! differentials grade, so it needs MSBuild to reach the construct for
//! certain ([`reach_is_certain`]): the walk has hidden nothing before it
//! ([`State::walk_opaque`]), it is in no doubted `Directory.Build.*` walk and
//! behind no import gate the walk did not decide from certain inputs
//! (`directory_build::reached_for_certain`), and every gate around it in its
//! file was decided from certain inputs ([`State::reach_doubted`]). The walk
//! never descends a `<Target>`, which MSBuild does not evaluate. On top of
//! that:
//!
//! - an import that failed to load ([`import_failure_certainty`]) or has no
//!   path ([`State::note_unloadable_import`]) must name its path from certain
//!   values ([`import_path_is_certain`]) and not be a duplicate MSBuild skips,
//!   which the walk's own skip settles before it tries the file. Only a
//!   missing file at a path with nothing to collapse and an empty path are
//!   claimed: what the walk's XML reader and file system call malformed or
//!   unreadable, MSBuild may read;
//! - an illegal condition whose verdict depends on the values it reads
//!   (MSB4086, a non-boolean scalar) must read only certain values, the
//!   stale channel included ([`operands_are_certain`]); a syntax error
//!   rejects whatever they hold ([`condition::rejected_by_syntax`]).
//!
//! Short of that, the same construct is a Possible site.
//!
//! Where MSBuild evaluates a condition at all is pinned against the oracle in
//! `tests/condition_diff.rs`'s `where_msbuild_evaluates_a_condition`, which
//! also holds these judgements to it: never under a false `<PropertyGroup>`,
//! `<ItemGroup>` (or false item), `<ItemDefinitionGroup>` (or false item
//! definition) or `<ImportGroup>`, an unchosen `<When>` (nor a `<When>` after
//! the chosen one), on or inside a `<Target>`, or on a write of a global
//! property; an `Update` item's metadata only when the update applies.
//!
//! That is a build's evaluation (`ProjectInstance`: `dotnet build`, `dotnet
//! restore`), the compilation the LSP models, and the one these judgements
//! follow. Under a false `<ItemGroup>` or item it evaluates nothing of the
//! item: not its condition (under a false group), its `Include`, `Exclude` or
//! metadata, nor the item operation it would build. Design-time evaluation
//! (the editable `Project`, which `dotnet msbuild -getProperty:` with no target
//! also builds) evaluates all of those but an `Update`'s, so it rejects
//! projects a build accepts; the same test pins which, and the walk evaluates
//! each as a build does.
//!
//! **What is not judged.** Content the walk did not see may hold an import
//! that fails, or rewrite a value so that one the walk reached fails; the walk
//! cannot know of either. So for a Possible import site, a doubt that is only
//! the walk's opacity — an undefined read that would be exact had the walk
//! seen every write, or a value hidden content may have rewritten
//! ([`super::Trust::stale`]) — is that content's doubt, and the judgement reads
//! such a name as the walk holds it ([`certain_but_for_opacity`]), as every
//! reader but the import points and the Compile items does (#792). Nor is an
//! SDK the walk cannot resolve: its resolver may decline one MSBuild resolves.
//! The pure walker follows no import and judges none; it judges conditions.

use std::collections::HashSet;
use std::ops::Range;
use std::path::{Path, PathBuf};

use roxmltree::Node;

use crate::diagnostic::ImportFailReason;
use crate::document::attribute;
use crate::imports::normalise;
use crate::{Rejection, RejectionCause, RejectionCertainty, UnloadableImport};

use super::item_pass::{DeferredGroupKind, expand_silent};
use super::observed::{self, EntryKind};
use super::{
    SdkResolution, State, condition, condition_exists, directory_build, import_dedup_key, loader,
    properties, sdk_import_path, sdk_project_in_alphabet, sdk_project_under_root,
    sdk_root_is_reparsed,
};

impl State<'_> {
    /// Record that MSBuild may reject the project, or does (`certainty`), for
    /// `cause`, at `span`: the first certain construct, else the first, is the
    /// evaluation's [`Rejection`], and each gets a [`crate::DiagnosticKind::Rejected`]
    /// or [`crate::DiagnosticKind::MayBeRejected`].
    pub(super) fn note_rejection(
        &mut self,
        certainty: RejectionCertainty,
        cause: RejectionCause,
        span: Range<usize>,
    ) {
        let replaces = match &self.rejection {
            None => true,
            Some(held) => {
                held.certainty == RejectionCertainty::Possible
                    && certainty == RejectionCertainty::Certain
            }
        };
        let rejection = Rejection {
            certainty,
            cause,
            span: self.effective_span(span.clone()),
            origin: self.current_origin(),
        };
        let kind = rejection.diagnostic_kind();
        if replaces {
            self.rejection = Some(rejection);
        }
        // A group judged in both passes may note one construct twice.
        let effective = self.effective_span(span.clone());
        if !self
            .diagnostics
            .iter()
            .any(|d| d.kind == kind && d.span == effective)
        {
            self.push(kind, span);
        }
    }

    /// [`Self::note_rejection`] of a [`RejectionCertainty::Possible`] site.
    pub(super) fn note_possible_rejection(&mut self, cause: RejectionCause, span: Range<usize>) {
        self.note_rejection(RejectionCertainty::Possible, cause, span);
    }

    /// [`Self::note_rejection`] for an import at `node` the walk took and
    /// cannot load: certain for an import with no path, named from certain
    /// values ([`State::taken_import_path_certain`]) where MSBuild reaches it
    /// for certain.
    pub(super) fn note_unloadable_import(&mut self, node: Node<'_, '_>, why: UnloadableImport) {
        let project = attribute(node, "Project").unwrap_or_default().into_owned();
        let certainty = certain_if(
            why == UnloadableImport::NoPath
                && self.taken_import_path_certain
                && reach_is_certain(self),
        );
        self.note_rejection(
            certainty,
            RejectionCause::Import {
                project,
                gate_undecided: false,
                why,
            },
            node.range(),
        );
    }
}

fn certain_if(certain: bool) -> RejectionCertainty {
    if certain {
        RejectionCertainty::Certain
    } else {
        RejectionCertainty::Possible
    }
}

/// Whether MSBuild reaches the walk's current position for certain (see the
/// module docs): the walk has hidden nothing before it, it is in no doubted
/// walk and behind no import gate or path it did not decide from certain
/// inputs, and every gate around it in its file was so decided.
pub(super) fn reach_is_certain(state: &State<'_>) -> bool {
    state.walk_opaque.is_none()
        && state.reach_doubted == 0
        && directory_build::reached_for_certain(state)
}

/// Whether every name `text` reads is read now as the build reads it, every
/// trust channel clean, staleness included ([`directory_build::is_certain`]).
pub(super) fn operands_are_certain(state: &State<'_>, text: &str) -> bool {
    properties::property_references(text).all(|name| directory_build::is_certain(state, name))
}

/// Whether the walk names the `Project` of the import at `node` from certain
/// values ([`operands_are_certain`]), with nothing it leaves as text.
pub(super) fn import_path_is_certain(node: Node<'_, '_>, state: &State<'_>) -> bool {
    let project = attribute(node, "Project").unwrap_or_default();
    !expand_silent(&project, state).had_unsupported && operands_are_certain(state, &project)
}

/// How sure the walk is that a failed load of `path`, the import it is taking,
/// for `reason`, makes MSBuild reject the project. Asked as the failure is
/// pushed, before it latches the walk opaque. MSBuild collapses `..` and `.` in
/// an import's path as text before it opens the file, as the walk's own
/// imports do (`walk_external_file`): a failure recorded at a path that does
/// not collapse to itself was not opened as MSBuild opens it, and claims
/// nothing.
pub(super) fn import_failure_certainty(
    state: &State<'_>,
    path: &Path,
    reason: &ImportFailReason,
) -> RejectionCertainty {
    certain_if(
        matches!(reason, ImportFailReason::NotFound)
            && path.is_absolute()
            && normalise(path) == path
            && state.taken_import_path_certain
            && reach_is_certain(state),
    )
}

/// A condition the walk evaluated to [`condition::Outcome::Illegal`], at
/// `span`: MSBuild rejects the project if it evaluates it with the values the
/// walk read. `reached`: whether MSBuild evaluates it for certain.
pub(super) fn illegal_condition_at(
    state: &mut State<'_>,
    condition: &str,
    reached: bool,
    span: Range<usize>,
) {
    let certain = reached
        && (condition::rejected_by_syntax(condition) || operands_are_certain(state, condition));
    state.note_rejection(
        certain_if(certain),
        RejectionCause::IllegalCondition {
            condition: condition.to_owned(),
        },
        span,
    );
}

/// Judge the file whose root element is `root`, which the walk is entering,
/// for a rule of MSBuild's loader it breaks (#888, #917; [`loader`]).
/// MSBuild parses the whole file before it evaluates any of it, so no
/// condition in the file matters, nor whether the walk later reaches the
/// construct: the rejection is certain wherever MSBuild certainly loads the
/// file, which is where the walk reaches the file's own import for certain,
/// and the port is sure of the rule. A rule a newer MSBuild's parse
/// configuration may relax is claimed only where none can apply
/// ([`parse_configuration_may_apply`]), unless the file breaks another rule
/// too.
pub(super) fn judge_load_time(root: Node<'_, '_>, state: &mut State<'_>) {
    let Some(mut found) = loader::first_violation(root, false) else {
        return;
    };
    if found.relaxable && parse_configuration_may_apply(state) {
        match loader::first_violation(root, true) {
            Some(strict) => found = strict,
            None => found.sure = false,
        }
    }
    state.note_rejection(
        certain_if(found.sure && reach_is_certain(state)),
        RejectionCause::LoadTime(found.error),
        found.span,
    );
}

/// Whether a newer MSBuild's parse configuration (`ParserIgnoreConfiguration`)
/// may apply to this evaluation: `MSBUILD_PARSE_CONFIG` is set, or a
/// `Directory.Parse.config` may stand in the project's directory or one above
/// it, where `dotnet msbuild` looks. The pure walker cannot look, so for it
/// one may.
fn parse_configuration_may_apply(state: &State<'_>) -> bool {
    if state.parse_configuration_named || !state.follow_imports {
        return true;
    }
    state.entry_project_dir.ancestors().any(|dir| {
        !matches!(
            observed::kind(state.observer, &dir.join("Directory.Parse.config")),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound
        )
    })
}

/// What a judged condition decides about the constructs under it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Judged {
    /// Decided from certain inputs, to this boolean.
    Decided(bool),
    /// Anything else: MSBuild may take either side, or reject.
    Undecided,
}

impl Judged {
    /// Whether MSBuild evaluates what this gate gates, for certain
    /// (`Some(reached)`), perhaps (`Some(false)`) or never (`None`), the gate
    /// itself reached as `reached` says.
    fn inner(self, reached: bool) -> Option<bool> {
        match self {
            Judged::Decided(true) => Some(reached),
            Judged::Decided(false) => None,
            Judged::Undecided => Some(false),
        }
    }
}

/// Judge the condition at `node` as MSBuild evaluates it, `Exists` resolved
/// against `exists_dir`, noting a rejection when it is illegal. `reached`:
/// whether MSBuild evaluates it for certain.
fn judge_condition(node: Node<'_, '_>, exists_dir: &Path, reached: bool, state: &mut State<'_>) {
    if let Some(text) = attribute(node, "Condition") {
        judge_text(node, &text, exists_dir, reached, state);
    }
}

/// [`judge_condition`] of a gate, and what it decides about the constructs
/// under it.
fn judge_gate(
    node: Node<'_, '_>,
    exists_dir: &Path,
    reached: bool,
    state: &mut State<'_>,
) -> Judged {
    let Some(text) = attribute(node, "Condition") else {
        return Judged::Decided(true);
    };
    match judge_text(node, &text, exists_dir, reached, state) {
        outcome @ (condition::Outcome::True | condition::Outcome::False)
            if directory_build::decided_from_certain_inputs(state, &text, exists_dir) =>
        {
            Judged::Decided(outcome == condition::Outcome::True)
        }
        _ => Judged::Undecided,
    }
}

/// [`judge_gate`] of a gate MSBuild evaluates in its item pass, against the
/// final property table. Outside the walk's item pass (in a branch it could not
/// decide) a later write may still change what the gate reads, so there it
/// decides nothing.
fn judge_item_pass_gate(
    node: Node<'_, '_>,
    exists_dir: &Path,
    reached: bool,
    state: &mut State<'_>,
) -> Judged {
    let judged = judge_gate(node, exists_dir, reached, state);
    if state.in_item_pass {
        judged
    } else {
        Judged::Undecided
    }
}

/// [`judge_condition`] of the condition `text` at `node`, returning its outcome.
fn judge_text(
    node: Node<'_, '_>,
    text: &str,
    exists_dir: &Path,
    reached: bool,
    state: &mut State<'_>,
) -> condition::Outcome {
    let observer = state.observer;
    let exists = |path: &str| condition_exists(observer, path, exists_dir);
    let outcome = if state.follow_imports {
        let probes = condition::Probes {
            exists: &exists,
            observer,
        };
        condition::evaluate_with_exists(text, &state.lookup, probes).outcome
    } else {
        condition::evaluate(text, &state.lookup).outcome
    };
    if outcome == condition::Outcome::Illegal {
        illegal_condition_at(state, text, reached, node.range());
    }
    outcome
}

/// Judge the conditions MSBuild evaluates in `node`, a construct of the
/// property pass the walk does not walk: one under a gate it could not decide
/// from certain inputs, or the gate of a group the walk skips unevaluated.
/// `dir` is the directory of the file holding it, and `reached` says whether
/// MSBuild reaches `node` for certain.
pub(super) fn judge_unwalked(node: Node<'_, '_>, dir: &Path, reached: bool, state: &mut State<'_>) {
    match node.tag_name().name() {
        "PropertyGroup" => {
            if let Some(inner) = judge_gate(node, dir, reached, state).inner(reached) {
                judge_properties(node, inner, state);
            }
        }
        "ImportGroup" => {
            if let Some(inner) = judge_gate(node, dir, reached, state).inner(reached) {
                judge_imports(node, dir, inner, state);
            }
        }
        "Import" => {
            judge_condition(node, dir, reached, state);
        }
        "Choose" => judge_whens(node, 0, dir, reached, state),
        // MSBuild evaluates these against the final property table, which the
        // branch the walk could not decide may change: judged against the
        // properties the walk holds here, deciding no gate, and again against
        // the final table in the item pass.
        "ItemGroup" | "ItemDefinitionGroup" if !state.in_item_pass => {
            debug_assert!(!reached, "the property pass judges only undecided branches");
            let kind = if node.has_tag_name("ItemGroup") {
                judge_item_group(node, reached, state);
                DeferredGroupKind::ItemGroup
            } else {
                judge_item_definition_group(node, reached, state);
                DeferredGroupKind::ItemDefinitionGroup
            };
            state.defer_judgement(node, kind);
        }
        "ItemGroup" => judge_item_group(node, reached, state),
        "ItemDefinitionGroup" => judge_item_definition_group(node, reached, state),
        // A `<UsingTask>` resolves `Exists` against its own file's directory.
        "UsingTask" => {
            judge_condition(node, dir, reached, state);
        }
        _ => {}
    }
}

/// Judge the property writes of the `<PropertyGroup>` at `node`, which
/// MSBuild evaluates as `reached` says. A write of a global property is
/// discarded unevaluated, condition and all.
pub(super) fn judge_properties(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    let entry_dir = state.entry_project_dir.clone();
    for child in node.children().filter(Node::is_element) {
        if state
            .protected
            .contains(&child.tag_name().name().to_ascii_lowercase())
        {
            continue;
        }
        judge_condition(child, &entry_dir, reached, state);
    }
}

/// Judge the imports' own conditions in the `<ImportGroup>` at `node`, which
/// MSBuild evaluates as `reached` says.
pub(super) fn judge_imports(node: Node<'_, '_>, dir: &Path, reached: bool, state: &mut State<'_>) {
    for child in node.children().filter(|c| c.has_tag_name("Import")) {
        judge_condition(child, dir, reached, state);
    }
}

/// Judge the `<When>`s of the `<Choose>` at `node` from the `from`th on, and
/// what they choose, MSBuild reaching the first of them as `reached` says.
/// MSBuild evaluates a `<When>` only while every earlier one was false, and
/// the `<Otherwise>` only when all were.
pub(super) fn judge_whens(
    node: Node<'_, '_>,
    from: usize,
    dir: &Path,
    reached: bool,
    state: &mut State<'_>,
) {
    let entry_dir = state.entry_project_dir.clone();
    let mut reach = Some(reached);
    for when in node
        .children()
        .filter(|c| c.has_tag_name("When"))
        .skip(from)
    {
        let Some(at) = reach else {
            return;
        };
        match judge_gate(when, &entry_dir, at, state) {
            Judged::Decided(true) => {
                judge_branch(when, dir, at, state);
                reach = None;
            }
            Judged::Decided(false) => {}
            Judged::Undecided => {
                judge_branch(when, dir, false, state);
                reach = Some(false);
            }
        }
    }
    if let Some(at) = reach
        && let Some(otherwise) = node.children().find(|c| c.has_tag_name("Otherwise"))
    {
        judge_branch(otherwise, dir, at, state);
    }
}

/// Judge what the `<When>` or `<Otherwise>` at `branch` holds, which MSBuild
/// evaluates as `reached` says.
pub(super) fn judge_branch(branch: Node<'_, '_>, dir: &Path, reached: bool, state: &mut State<'_>) {
    for child in branch.children().filter(Node::is_element) {
        judge_unwalked(child, dir, reached, state);
    }
}

/// Judge the conditions of a group the item pass replays: `<ItemGroup>`,
/// `<ItemDefinitionGroup>` or `<UsingTask>`, against the final property
/// table. `reached`: whether MSBuild reaches the group for certain, as the
/// property pass found it ([`reach_is_certain`] there; never for a group it
/// only recorded for judgement).
pub(super) fn judge_deferred(node: Node<'_, '_>, dir: &Path, reached: bool, state: &mut State<'_>) {
    judge_unwalked(node, dir, reached, state);
}

/// Judge the `<ItemGroup>` at `node`, which MSBuild reaches as `reached` says.
/// A build evaluates an item's condition only under a true group, and the
/// rest of the item (the operation it builds, and an `Include` item's
/// metadata conditions) only under a true item; an `Update`'s metadata only
/// where the update applies. Metadata that reads item metadata (`%(…)`) or an
/// item list (`@(…)`) is evaluated item by item, so not at all when the
/// `Include` names no item: then its conditions are only possibly evaluated.
fn judge_item_group(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    let entry_dir = state.entry_project_dir.clone();
    let Some(inner) = judge_item_pass_gate(node, &entry_dir, reached, state).inner(reached) else {
        return;
    };
    for item in node.children().filter(Node::is_element) {
        let Some(reached) = judge_item_pass_gate(item, &entry_dir, inner, state).inner(inner)
        else {
            continue;
        };
        if let Some(sure) = loader::remove_matching_more_than_items(item) {
            state.note_rejection(
                certain_if(reached && sure),
                RejectionCause::IllegalItemOperation {
                    item: item.tag_name().name().to_owned(),
                },
                item.range(),
            );
        }
        let reads_items = |text: &str| text.contains("%(") || text.contains("@(");
        let per_item = item.attributes().any(|a| reads_items(a.value()))
            || item.children().filter(Node::is_element).any(|metadata| {
                // Text the reader declines (a CDATA section) counts as reading.
                let text: Option<String> = metadata
                    .descendants()
                    .filter(|n| n.is_text())
                    .map(crate::document::text)
                    .collect();
                text.is_none_or(|t| reads_items(&t))
                    || metadata.attributes().any(|a| reads_items(a.value()))
            });
        let metadata_reached = reached && attribute(item, "Include").is_some() && !per_item;
        for metadata in item.children().filter(Node::is_element) {
            judge_condition(metadata, &entry_dir, metadata_reached, state);
        }
    }
}

/// Judge the `<ItemDefinitionGroup>` at `node`, which MSBuild reaches as
/// `reached` says. MSBuild evaluates a definition's condition only under a
/// true group, and its metadata's only under a true definition. `Exists` resolves
/// against the project's directory, as for every item-pass condition.
fn judge_item_definition_group(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    let entry_dir = state.entry_project_dir.clone();
    let Some(inner) = judge_item_pass_gate(node, &entry_dir, reached, state).inner(reached) else {
        return;
    };
    for definition in node.children().filter(Node::is_element) {
        let Some(metadata_reached) =
            judge_item_pass_gate(definition, &entry_dir, inner, state).inner(inner)
        else {
            continue;
        };
        for metadata in definition.children().filter(Node::is_element) {
            judge_condition(metadata, &entry_dir, metadata_reached, state);
        }
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
    // MSBuild turns the attribute's own `\` into `/` before it expands it.
    let expansion = expand_silent(&project.replace('\\', "/"), state);
    if path_undecided(project, state, expansion.had_unsupported) {
        return (!requires_own_file).then_some(UnloadableImport::PathUndecided);
    }
    // Its trust is judged just above, name by name.
    let value = expansion.value.ignoring_trust();
    // A `\` a property supplied that MSBuild's Unix path adjustment may keep
    // can name a file the walk does not (`adjustment_settles`), and `Exists`
    // collapses its argument otherwise than the import does, so a gate that
    // requires the file does not guard this one.
    let mut rewrites = None;
    if value.split_list().any(|segment| {
        !super::adjustment_settles(value.as_escaped(), &segment, &mut rewrites, state.observer)
    }) {
        return Some(UnloadableImport::PathUndecided);
    }
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

/// Judge the condition of the group at `node` alone, which the walk skips
/// unevaluated though MSBuild evaluates it as `reached` says: a
/// `<PropertyGroup>` whose every write MSBuild discards unevaluated.
pub(super) fn judge_unwalked_gate(
    node: Node<'_, '_>,
    dir: &Path,
    reached: bool,
    state: &mut State<'_>,
) {
    judge_condition(node, dir, reached, state);
}
