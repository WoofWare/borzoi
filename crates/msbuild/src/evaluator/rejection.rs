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
//! A condition is a site too ([`judge_condition_rejection`]): one the walk
//! evaluates to [`condition::Outcome::Illegal`], or one whose evaluation stops
//! at an operand MSBuild may throw on (a property function the walk does not
//! model, reached on values it holds). So is one MSBuild may evaluate where
//! the walk does not: under a gate the walk could not decide from certain
//! inputs ([`judge_unwalked`]), and every condition of the item pass, judged
//! group by group ([`judge_deferred`]) because MSBuild evaluates an item's
//! condition, and an `Include` item's metadata conditions, whatever its
//! group's or its own gate holds.
//!
//! So is a property function MSBuild throws on (an indexer out of range, a
//! malformed `[MSBuild]::Version*` operand: [`properties::Issue::Throws`]) in
//! text it evaluates: a property body, walked or not ([`judge_unwalked_body`]),
//! an item's attributes and metadata, an item definition's
//! ([`judge_throwing_expression`]). One the walk does not model in such text
//! is no site yet (#1094): the SDK's own bodies call several on certain
//! values; nor is one reading item metadata in a metadatum, which MSBuild
//! hands the metadatum's value ([`judge_metadata_text`]). Nor is a throw on a
//! value the walk holds none of (a write it refused to compute, a reserved
//! name it does not seed), in a condition or a text: whether MSBuild's own
//! value throws is the judgement over the values a name may hold, #1009's
//! second stage. A leaf of a condition that reads such a name has none of
//! MSBuild's booleans, so what comes after it is reached perhaps, and judged
//! on the values held.
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
//! - an illegal condition must throw whatever the names it reaches that the
//!   walk is not certain of hold, the stale channel included
//!   ([`judge_condition_rejection`]): a syntax error, or an ill-typed operand
//!   (MSB4086, a non-boolean scalar) or a property function MSBuild throws on,
//!   reached, left to right, through operands of certain value. What an
//!   operand MSBuild never reaches reads does not matter;
//! - a property function MSBuild throws on in text must read only names the
//!   walk is certain of ([`judge_throwing_expression`]).
//!
//! Short of that, the same construct is a Possible site.
//!
//! Where MSBuild evaluates a condition at all is pinned against the oracle in
//! `tests/condition_diff.rs`'s `where_msbuild_evaluates_a_condition`: never
//! under a false `<PropertyGroup>`, `<ItemDefinitionGroup>` (or false item
//! definition) or `<ImportGroup>`, an unchosen `<When>` (nor a `<When>` after
//! the chosen one), on or inside a `<Target>`, or on a write of a global
//! property; always for an `<ItemGroup>`'s items and an `Include` item's
//! metadata; an `Update` item's metadata only when the update applies.
//!
//! "Always" is design-time evaluation's rule (the editable `Project`, which
//! `dotnet msbuild -getProperty:` with no target also builds), and the one
//! these judgements follow. A build (`ProjectInstance`: `dotnet build`, `dotnet
//! restore`) evaluates an item under a false gate not at all, so it accepts
//! every project whose only illegal condition sits there. Design-time
//! evaluation rejects every project a build rejects, so a withdrawal by this
//! rule commits nothing a build rejects; a Certain claim on such an item is a
//! claim about design-time evaluation. The same test pins which projects only
//! design-time evaluation rejects.
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

use std::collections::{HashMap, HashSet};
use std::ops::Range;
use std::path::{Path, PathBuf};

use roxmltree::Node;

use crate::diagnostic::ImportFailReason;
use crate::document::attribute;
use crate::imports::normalise;
use crate::{Rejection, RejectionCause, RejectionCertainty, UnloadableImport};

use super::item_pass::{DeferredGroupKind, expand_silent, metadata_attribute};
use super::observed::{self, EntryKind};
use super::{
    Arm, PathOf, SdkResolution, Speculation, State, collect_element_text, condition,
    condition_exists, directory_build, import_dedup_key, loader, properties, sdk_import_path,
    sdk_project_in_alphabet, sdk_project_under_root, sdk_project_written_rooted,
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
        self.push(kind, span);
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

/// Whether the walk holds a value of `name` MSBuild may hold, as a Possible
/// site asks: one it computed (bound), however it doubts it, or an undefined
/// read it shows exact. A value the walk doubts is one MSBuild may hold among
/// others: a write it skipped under a gate it could not decide adds one, and
/// hidden content may have rewritten it, or not. A name the walk holds no
/// value of and cannot show undefined is otherwise: `""` for a write it
/// refused to compute, or for a reserved name it does not seed, is a value
/// MSBuild need not hold at all, so what a function does on it says nothing of
/// the build.
pub(super) fn holds_a_value_msbuild_may(state: &State<'_>, name: &str) -> bool {
    (state.lookup.is_bound(name) || state.undefined_read_is_exact(name))
        && !state.speculatively_unheld(name)
}

impl State<'_> {
    /// Where the conditions the walk evaluates now are MSBuild's: the
    /// property pass's, an item definition group's, or another of the item
    /// pass's ([`condition::Site`]).
    pub(super) fn condition_site(&self) -> condition::Site {
        match self.item_pass {
            None => condition::Site::PropertyPass,
            Some(DeferredGroupKind::ItemDefinitionGroup) => condition::Site::ItemDefinition,
            Some(DeferredGroupKind::ItemGroup | DeferredGroupKind::UsingTask) => {
                condition::Site::ItemPass
            }
        }
    }

    /// Whether the speculative walk of content the walk does not take
    /// ([`State::speculation`]) leaves `name`'s value unknown.
    pub(super) fn speculatively_unheld(&self, name: &str) -> bool {
        self.speculation.as_ref().is_some_and(|speculation| {
            let name = name.to_ascii_lowercase();
            speculation.unheld.contains(&name)
                || speculation
                    .inherited
                    .as_ref()
                    .is_some_and(|inherited| inherited.unknown(&name))
        })
    }

    /// Open a walk of content the walk does not take: what a write there
    /// names ([`speculative_write`]) is unknown to what follows on that path,
    /// until the outermost walk closes. MSBuild's value on that path is the
    /// judgement over the values a name may hold (#1009's second stage); the
    /// value the walk holds is not it.
    fn open_speculation(&mut self) {
        match &mut self.speculation {
            Some(speculation) => speculation.depth += 1,
            None => {
                self.speculation = Some(Speculation {
                    unheld: HashSet::new(),
                    gained: Vec::new(),
                    walk_written: std::rc::Rc::default(),
                    arms: Vec::new(),
                    inherited: None,
                    depth: 1,
                    dead_arms: 0,
                });
            }
        }
    }

    /// Close one walk of content the walk does not take.
    fn close_speculation(&mut self) {
        let speculation = self.speculation.as_mut().expect("a speculation is open");
        speculation.depth -= 1;
        if speculation.depth == 0 {
            self.speculation = None;
        }
    }

    /// Where an item group from the walk the judgement makes now stands, for
    /// it to be judged later ([`State::defer_judgement`]): the walk's writes,
    /// shared and still filling until the walk closes, and the arms the
    /// group is in.
    pub(super) fn speculatively_written(&self) -> Option<PathOf> {
        self.speculation.as_ref().map(|speculation| PathOf {
            writes: speculation.walk_written.clone(),
            arms: speculation.arms.as_slice().into(),
        })
    }

    /// Record the write of `name` on the path the judgement walks now, in the
    /// arms it walks.
    fn record_write(&mut self, name: String) {
        if let Some(speculation) = self.speculation.as_mut() {
            let arms: std::rc::Rc<[Arm]> = speculation.arms.as_slice().into();
            speculation
                .walk_written
                .borrow_mut()
                .writes
                .entry(name.clone())
                .or_default()
                .push(arms);
        }
        self.mark_unheld([name]);
    }

    /// Mark `names` unknown to what follows on the path the judgement walks
    /// now. Their writes are recorded where they were made
    /// ([`State::record_write`]).
    fn mark_unheld(&mut self, names: impl IntoIterator<Item = String>) {
        if let Some(speculation) = self.speculation.as_mut() {
            for name in names {
                if speculation.unheld.insert(name.clone()) {
                    speculation.gained.push(name);
                }
            }
        }
    }

    /// Judge, as [`judge_deferred`] does, an item group from content the walk
    /// does not take, with `written` where it stands in that walk: the names
    /// written on its path, before the group or after it, and in no arm of a
    /// `<Choose>` another arm of which holds it, whose final value is still
    /// not certain, since a certain write after the walk settles the value
    /// MSBuild reads in the item pass. Which names are not certain is
    /// computed once per walk, the table being final.
    pub(super) fn judge_from_path(
        &mut self,
        written: Option<&PathOf>,
        judge: impl FnOnce(&mut State<'_>),
    ) {
        let Some(written) = written else {
            judge(self);
            return;
        };
        if written.writes.borrow().settled.is_none() {
            let names: HashSet<String> = written
                .writes
                .borrow()
                .writes
                .keys()
                .filter(|name| {
                    crate::cost::count(|costs| costs.path_writes_examined += 1);
                    !directory_build::is_certain(self, name)
                })
                .cloned()
                .collect();
            written.writes.borrow_mut().settled = Some(std::rc::Rc::new(names));
        }
        let saved = self.speculation.replace(Speculation {
            unheld: HashSet::new(),
            gained: Vec::new(),
            walk_written: std::rc::Rc::default(),
            arms: Vec::new(),
            inherited: Some(written.clone()),
            depth: 1,
            dead_arms: 0,
        });
        judge(self);
        self.speculation = saved;
    }
}

/// On the path the judgement walks, the write at `node`, whose gate may hold:
/// its name's value is unknown to what follows there.
fn speculative_write(node: Node<'_, '_>, state: &mut State<'_>) {
    state.record_write(node.tag_name().name().to_ascii_lowercase());
}

/// Whether the walk names the `Project` of the import at `node` from certain
/// values ([`operands_are_certain`]), with nothing it leaves as text.
pub(super) fn import_path_is_certain(node: Node<'_, '_>, state: &State<'_>) -> bool {
    let project =
        super::import_project_as_expanded(&attribute(node, "Project").unwrap_or_default());
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

/// Note the rejection MSBuild may make evaluating `condition`, at `span`,
/// which the walk evaluated to `outcome` on the values it holds, `Exists`
/// resolved against `exists_dir`. `reached`: whether MSBuild evaluates the
/// condition for certain.
///
/// A condition that throws on the values the walk holds
/// ([`condition::Outcome::Illegal`]) may make MSBuild reject the project. The
/// rejection is certain where MSBuild throws whatever the names the walk is
/// not certain of hold ([`directory_build::is_certain`], the stale channel
/// included): MSBuild evaluates the condition left to right and stops at the
/// operand that decides it ([`condition::throws_whatever`]), so a throw on certain
/// values that MSBuild reaches through operands of certain value is certain,
/// whatever an operand it never reaches reads.
///
/// One whose evaluation stopped at an operand we cannot evaluate
/// ([`condition::Outcome::Unsupported`]) is a Possible site where, on the
/// values the walk holds, that operand may throw itself (one we do not model,
/// a property function included), or may let MSBuild reach one it throws on.
/// An operand MSBuild evaluates without throwing, to a boolean we cannot
/// compute (a string equality whose case folding we do not model), is no
/// site of its own ([`condition::Throws::Never`]).
///
/// A condition legal on the values the walk holds is judged too where it
/// reads a name the walk is not certain of: a leaf on one has none of
/// MSBuild's booleans, so an operand after it is reached perhaps, and a throw
/// there on the values held is a Possible site
/// ([`condition::may_throw_on_held`]). The leaf itself is judged on the value
/// held, though it may throw on another value of the name
/// ([`condition::Throws::Maybe`]): judging that withdraws every project the
/// SDK's own conditions read such a name in, so it waits on knowing what
/// values such a name may hold (#1009's second stage).
pub(super) fn judge_condition_rejection(
    state: &mut State<'_>,
    condition: &str,
    outcome: condition::Outcome,
    exists_dir: &Path,
    reached: bool,
    span: Range<usize>,
) {
    let observer = state.observer;
    let exists = |path: &str| condition_exists(observer, path, exists_dir);
    let probes = state.follow_imports.then_some(condition::Probes {
        exists: &exists,
        observer,
    });
    let doubted = |name: &str| !holds_a_value_msbuild_may(state, name);
    let uncertain = |name: &str| !directory_build::is_certain(state, name);
    if matches!(
        outcome,
        condition::Outcome::True | condition::Outcome::False
    ) && !properties::property_references(condition).any(uncertain)
    {
        return;
    }
    // Reached only perhaps, it is Possible however its operands stand, and
    // judging them would only probe the file system for nothing.
    let certainly = reached
        && outcome == condition::Outcome::Illegal
        && condition::throws_whatever(
            condition,
            &state.lookup,
            probes,
            state.condition_site(),
            &uncertain,
        );
    // Short of that, evaluation threw, or stopped at an operand we cannot
    // evaluate, which may throw, or return a value that lets MSBuild reach
    // one it throws on with the values the walk holds. What an operand past
    // it reads from the file system may decide whether it throws, so the
    // judgement probes as the evaluation would have.
    if certainly
        || condition::may_throw_on_held(
            condition,
            &state.lookup,
            probes,
            state.condition_site(),
            &uncertain,
            &doubted,
        )
    {
        state.note_rejection(
            certain_if(certainly),
            RejectionCause::IllegalCondition {
                condition: condition.to_owned(),
            },
            span,
        );
    }
}

/// A `$(…)` MSBuild throws on, on the values the walk holds
/// ([`properties::Issue::Throws`]).
#[derive(Debug, Clone)]
pub(super) struct Thrown {
    /// The expression, as written.
    pub(super) expression: String,
    /// The names its evaluation read before it threw: what the throw rests
    /// on.
    reads: Vec<String>,
}

/// Every `$(…)` of `text` MSBuild throws on, on the values the walk holds
/// ([`properties::Issue::Throws`]): for text MSBuild may evaluate where the
/// walk does not. Expanded with the file system where the walk has it, as
/// the walk's own expansions are, so a probe it makes is recorded.
pub(super) fn throwing_expressions(text: &str, state: &State<'_>) -> Vec<Thrown> {
    let (_, issues) = if state.follow_imports {
        properties::substitute_with_fs(text, &state.lookup, state.observer)
    } else {
        properties::substitute(text, &state.lookup)
    };
    throws_in(&issues)
}

/// Every expression of an expansion's `issues` MSBuild throws on, on the
/// values the expansion read ([`properties::Issue::Throws`]), in order.
pub(super) fn throws_in(issues: &[properties::Issue]) -> Vec<Thrown> {
    issues
        .iter()
        .filter_map(|issue| match issue {
            properties::Issue::Throws { expression, reads } => Some(Thrown {
                expression: expression.clone(),
                reads: reads.clone(),
            }),
            _ => None,
        })
        .collect()
}

/// Note the rejection MSBuild makes evaluating a text, at `span`, whose
/// `$(…)` expressions `thrown` throw on the values the walk holds. `reached`:
/// whether MSBuild evaluates the text for certain. MSBuild expands the whole
/// text, and a throw anywhere in it rejects the project, so what an
/// expression before a throwing one does is moot: it is certain where it is
/// reached for certain and every name one of them read before it threw is
/// certain ([`directory_build::is_certain`]).
///
/// Short of that it is Possible, where every name one of them read holds a
/// value MSBuild may hold ([`holds_a_value_msbuild_may`]), or where one
/// throws whatever its expressions on the names that do not return
/// ([`condition::expression_throws_whatever_they_return`]). Any other throw on
/// such a name is no site: the value held is none MSBuild need hold, and
/// whether the function throws on MSBuild's own value is the judgement over
/// the values a name may hold (#1009's second stage), as for a condition
/// ([`condition::may_throw_on_held`]).
pub(super) fn judge_throwing_expression(
    state: &mut State<'_>,
    thrown: Vec<Thrown>,
    reached: bool,
    span: Range<usize>,
) {
    let unheld = |name: &str| !holds_a_value_msbuild_may(state, name);
    let (held, on_unheld): (Vec<Thrown>, Vec<Thrown>) = thrown
        .into_iter()
        .partition(|thrown| !thrown.reads.iter().any(|name| unheld(name)));
    let certain = held
        .iter()
        .find(|thrown| {
            thrown
                .reads
                .iter()
                .all(|name| directory_build::is_certain(state, name))
        })
        .filter(|_| reached)
        .cloned();
    // One that read a name the walk holds none of throws whatever that
    // name's expressions return, perhaps: on each value tried, it throws on
    // the rest.
    let observer = state.follow_imports.then_some(state.observer);
    let possible = || {
        held.first().cloned().or_else(|| {
            on_unheld.into_iter().find(|thrown| {
                condition::expression_throws_whatever_they_return(
                    &thrown.expression,
                    &state.lookup,
                    observer,
                    &unheld,
                )
            })
        })
    };
    let (certainty, thrown) = match certain {
        Some(thrown) => (RejectionCertainty::Certain, thrown),
        None => match possible() {
            Some(thrown) => (RejectionCertainty::Possible, thrown),
            None => return,
        },
    };
    state.note_rejection(
        certainty,
        RejectionCause::ThrowingExpression {
            expression: thrown.expression,
        },
        span,
    );
}

/// Judge `text`, at `span`, which MSBuild evaluates as `reached` says and the
/// walk does not, for an expression MSBuild throws on.
fn judge_unwalked_text(state: &mut State<'_>, text: &str, reached: bool, span: Range<usize>) {
    let expressions = throwing_expressions(text, state);
    if !expressions.is_empty() {
        judge_throwing_expression(state, expressions, reached, span);
    }
}

/// Judge the body of the property write at `node`, which MSBuild evaluates
/// as `reached` says and the walk does not ([`judge_unwalked_text`]).
pub(super) fn judge_unwalked_body(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    judge_element_contents(state, node, reached, Contents::Text);
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
        condition::evaluate_at(text, &state.lookup, Some(probes), state.condition_site()).outcome
    } else {
        condition::evaluate_at(text, &state.lookup, None, state.condition_site()).outcome
    };
    judge_condition_rejection(state, text, outcome, exists_dir, reached, node.range());
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
        // MSBuild evaluates these after every property write: from the
        // property pass, judged in the item pass against the final table.
        "ItemGroup" if state.item_pass.is_none() => {
            state.defer_judgement(node, DeferredGroupKind::ItemGroup, reached);
        }
        "ItemDefinitionGroup" if state.item_pass.is_none() => {
            state.defer_judgement(node, DeferredGroupKind::ItemDefinitionGroup, reached);
        }
        "UsingTask" if state.item_pass.is_none() => {
            state.defer_judgement(node, DeferredGroupKind::UsingTask, reached);
        }
        "ItemGroup" => judge_item_group(node, reached, state),
        "ItemDefinitionGroup" => judge_item_definition_group(node, reached, state),
        // A `<UsingTask>` resolves `Exists` against its own file's directory.
        // MSBuild expands its attributes where it takes it.
        "UsingTask" => {
            let gate = judge_gate(node, dir, reached, state);
            if let Some(inner) = gate.inner(reached) {
                judge_using_task(node, inner, state);
            }
        }
        _ => {}
    }
}

/// Judge the property writes of the `<PropertyGroup>` at `node`, which
/// MSBuild evaluates as `reached` says: each one's condition, and its body
/// where the condition may hold. A write of a global property is discarded
/// unevaluated, condition and all.
pub(super) fn judge_properties(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    let entry_dir = state.entry_project_dir.clone();
    // Each write is judged on the path MSBuild takes: after the writes before
    // it there.
    state.open_speculation();
    for child in node.children().filter(Node::is_element) {
        if state
            .protected
            .contains(&child.tag_name().name().to_ascii_lowercase())
        {
            continue;
        }
        // A write whose gate is certainly false there writes nothing.
        if let Some(body_reached) = judge_gate(child, &entry_dir, reached, state).inner(reached) {
            judge_unwalked_body(child, body_reached, state);
            speculative_write(child, state);
        }
    }
    state.close_speculation();
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
    // Each branch starts from what the path held before the `<Choose>`; what
    // follows it on the path, from what any of them wrote.
    let mut written = HashSet::new();
    for when in node
        .children()
        .filter(|c| c.has_tag_name("When"))
        .skip(from)
    {
        let Some(at) = reach else {
            break;
        };
        match judge_gate(when, &entry_dir, at, state) {
            Judged::Decided(true) => {
                written.extend(judge_branch(when, dir, at, state));
                reach = None;
            }
            Judged::Decided(false) => {}
            Judged::Undecided => {
                written.extend(judge_branch(when, dir, false, state));
                reach = Some(false);
            }
        }
    }
    if let Some(at) = reach
        && let Some(otherwise) = node.children().find(|c| c.has_tag_name("Otherwise"))
    {
        written.extend(judge_branch(otherwise, dir, at, state));
    }
    state.mark_unheld(written);
    state.arm_decisions.remove(&choose_key(node));
}

/// Judge what the `<When>` or `<Otherwise>` at `branch` holds, which MSBuild
/// evaluates as `reached` says, from what the path held before it. The names
/// it writes, which it leaves the path as it found it without.
pub(super) fn judge_branch(
    branch: Node<'_, '_>,
    dir: &Path,
    reached: bool,
    state: &mut State<'_>,
) -> HashSet<String> {
    // Decided before the walk opens, on the path as it stands at the
    // `<Choose>`.
    let dead = arm_is_dead(branch, state);
    state.open_speculation();
    let choose = branch.parent_element().unwrap_or(branch);
    let arm: Arm = (
        (
            std::ptr::from_ref(branch.document()) as usize,
            choose.range().start,
        ),
        branch.range().start,
    );
    let mark = match state.speculation.as_mut() {
        Some(speculation) => {
            speculation.arms.push(arm);
            speculation.dead_arms += usize::from(dead);
            speculation.gained.len()
        }
        None => 0,
    };
    judge_branch_children(branch, dir, reached, state);
    let mut written = HashSet::new();
    if let Some(speculation) = state.speculation.as_mut() {
        speculation.arms.pop();
        speculation.dead_arms -= usize::from(dead);
        for name in speculation.gained.drain(mark..) {
            speculation.unheld.remove(&name);
            written.insert(name);
        }
    }
    state.close_speculation();
    written
}

/// Whether MSBuild cannot take the `<When>` or `<Otherwise>` at `branch`, by
/// the gates of its `<Choose>`, which MSBuild evaluates on the state before
/// the `<Choose>`: an earlier `<When>`'s true, or its own false, each decided
/// whatever the names the walk doubts hold, those the judged path writes
/// included ([`State::reference_gate_decision`]). A refusal a clean write
/// overwrote does not keep such a gate open, as it keeps an import point's
/// ([`directory_build::decision_from_certain_inputs`]): the rejection
/// judgement walks the arm all the same; [`super::item_pass`]'s reference
/// check does not count what it defers from there.
///
/// Only an arm holding a `<ProjectReference>` is asked about, as only such an
/// arm defers a group the check reads, so an arm with none probes nothing.
/// The arms' fates are taken in one forward pass over the `<Choose>` per pass
/// over its arms (`State::arm_decisions`, which [`judge_whens`] and
/// `handle_choose` clear when the pass ends), as far as the arm asked about
/// and no further, and a gate after one that holds whatever the doubted names
/// hold is not evaluated, as MSBuild does not evaluate it: so a chain of `n`
/// arms costs at most `n` decisions, and the read set gains no probe MSBuild
/// does not make.
fn arm_is_dead(branch: Node<'_, '_>, state: &mut State<'_>) -> bool {
    if !branch.descendants().any(|node| {
        node.is_element() && node.has_tag_name("ProjectReference") && node.has_attribute("Include")
    }) {
        return false;
    }
    // Once the walk has hidden content no arm is ruled out (a gate reading a
    // doubted name settles nothing then, `State::reference_gate_decision`),
    // and a gate decided on held values alone may itself rest on a value the
    // hidden content rewrote, so none is probed: an arm counts as live, which
    // costs at most a decline.
    if state.walk_opaque.is_some() {
        return false;
    }
    let Some(choose) = branch.parent_element() else {
        return false;
    };
    let mut fates = state
        .arm_decisions
        .remove(&choose_key(choose))
        .unwrap_or_default();
    let from = fates.next;
    for arm in choose
        .children()
        .filter(|arm| arm.is_element() && arm.range().start >= from)
    {
        let gate = attribute(arm, "Condition").filter(|_| arm.has_tag_name("When"));
        let dead = fates.taken
            || match gate {
                Some(condition) => {
                    crate::cost::count(|costs| costs.arm_gate_decisions += 1);
                    match state.reference_gate_decision(&condition, None) {
                        Some(true) => {
                            fates.taken = true;
                            false
                        }
                        Some(false) => true,
                        None => false,
                    }
                }
                None => false,
            };
        fates.dead.insert(arm.range().start, dead);
        fates.next = arm.range().end;
        if arm.id() == branch.id() {
            break;
        }
    }
    let dead = fates
        .dead
        .get(&branch.range().start)
        .copied()
        .unwrap_or(false);
    state.arm_decisions.insert(choose_key(choose), fates);
    dead
}

/// The arms of one `<Choose>` whose fates [`arm_is_dead`] has taken so far,
/// in order.
#[derive(Default)]
pub(super) struct ArmFates {
    /// Each arm's fate, by the offset of its `<When>` or `<Otherwise>`.
    dead: HashMap<usize, bool>,
    /// Whether an arm taken so far holds whatever the doubted names hold, so
    /// that every later one is dead.
    taken: bool,
    /// The offset past the last arm taken so far.
    next: usize,
}

/// The key of the `<Choose>` at `choose` in `State::arm_decisions`.
pub(super) fn choose_key(choose: Node<'_, '_>) -> (usize, usize) {
    (
        std::ptr::from_ref(choose.document()) as usize,
        choose.range().start,
    )
}

/// [`judge_branch`] within its speculative walk.
fn judge_branch_children(branch: Node<'_, '_>, dir: &Path, reached: bool, state: &mut State<'_>) {
    for child in branch.children().filter(Node::is_element) {
        judge_unwalked(child, dir, reached, state);
    }
}

/// Judge the conditions of a group the item pass replays: `<ItemGroup>`,
/// `<ItemDefinitionGroup>` or `<UsingTask>`, against the final property
/// table. `reached`: whether MSBuild reaches the group for certain, as the
/// property pass found it ([`reach_is_certain`] there).
pub(super) fn judge_deferred(node: Node<'_, '_>, dir: &Path, reached: bool, state: &mut State<'_>) {
    judge_unwalked(node, dir, reached, state);
}

/// The attributes of a `<UsingTask>` MSBuild expands as it registers the
/// task. Its `Condition` is judged as one, and it expands neither its
/// `Label` nor `RequiredPlatform` nor `RequiredRuntime` (probed,
/// `msbuild-condition-oracle`, SDK 10.0.401; `tests/condition_diff.rs`'s
/// `using_task_texts_are_judged_where_msbuild_expands_them`).
const USING_TASK_EXPANDED: &[&str] = &[
    "TaskName",
    "AssemblyFile",
    "AssemblyName",
    "TaskFactory",
    "Architecture",
    "Runtime",
    "Override",
];

/// Judge what MSBuild expands of the `<UsingTask>` at `node` as it registers
/// the task, which it does as `reached` says, for an expression it throws on:
/// the attributes it expands ([`USING_TASK_EXPANDED`]), each parameter's
/// `ParameterType`, `Required` and `Output`, the body's `Evaluate`, and the
/// body itself (its text, CDATA included, and its elements' attributes; not
/// its comments) unless `Evaluate` holds `false`, in any case and padding.
/// Any other `Evaluate` MSBuild evaluates the body under or throws on, which
/// rejects alike. A value the walk cannot vouch for leaves the body reached
/// perhaps.
fn judge_using_task(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    for name in USING_TASK_EXPANDED {
        if let Some(text) = attribute(node, name) {
            // MSBuild turns `AssemblyFile`'s own `\` into `/` before it expands
            // it, where `\` is no separator (`ProjectUsingTaskElement.
            // AssemblyFile`, `FixFilePath`), as an import's `Project`.
            let text = if *name == "AssemblyFile" && std::path::MAIN_SEPARATOR != '\\' {
                text.replace('\\', "/")
            } else {
                text.into_owned()
            };
            judge_unwalked_text(state, &text, reached, node.range());
        }
    }
    for child in node.children().filter(Node::is_element) {
        match child.tag_name().name() {
            "ParameterGroup" => {
                for parameter in child.children().filter(Node::is_element) {
                    for name in ["ParameterType", "Required", "Output"] {
                        if let Some(text) = attribute(parameter, name) {
                            judge_unwalked_text(state, &text, reached, parameter.range());
                        }
                    }
                }
            }
            "Task" => {
                let body_reached = match attribute(child, "Evaluate") {
                    None => Some(reached),
                    Some(evaluate) => {
                        judge_unwalked_text(state, &evaluate, reached, child.range());
                        let (value, issues) = properties::substitute(&evaluate, &state.lookup);
                        // Its trust is judged just below, name by name. MSBuild
                        // reads the flag as expanded, escapes and all
                        // (`%66alse` is no `false`; probed,
                        // `msbuild-condition-oracle`, SDK 10.0.401).
                        let value = value.ignoring_trust().as_escaped().to_owned();
                        // An item list or metadatum MSBuild expands into it
                        // the walk does not.
                        if !issues.is_empty()
                            || !operands_are_certain(state, &evaluate)
                            || value.contains("@(")
                            || value.contains("%(")
                        {
                            Some(false)
                        } else if value
                            // `Boolean.TryParse`'s padding: whitespace, as
                            // `char.IsWhiteSpace` and Rust's `trim` both
                            // classify it, and NUL.
                            .trim_matches(|c: char| c.is_whitespace() || c == '\0')
                            .eq_ignore_ascii_case("false")
                        {
                            None
                        } else {
                            Some(reached)
                        }
                    }
                };
                if let Some(body_reached) = body_reached {
                    judge_element_contents(state, child, body_reached, Contents::Text);
                }
            }
            _ => {}
        }
    }
}

/// What MSBuild reads as the text of `element`, a property, a metadatum or
/// an inline task body, unexpanded (`Utilities.GetXmlNodeInnerContents`),
/// where the walk reproduces it: [`collect_element_text`] for text, CDATA
/// sections and comments alone, else [`inner_xml`].
pub(crate) fn element_inner_contents(element: Node<'_, '_>) -> Option<String> {
    collect_element_text(element).or_else(|| inner_xml(element))
}

/// How the text of an element is judged.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Contents {
    /// A property's body or an inline task's ([`judge_unwalked_text`]).
    Text,
    /// A metadatum's ([`judge_metadata_text`]).
    Metadata,
}

/// Judge the text MSBuild reads of `element` ([`element_inner_contents`]),
/// which it expands as `reached` says. Where the walk cannot reproduce that
/// reading, an expression in it may throw on what the walk does not see: one
/// may be spelt with a reference (`&#36;(…)`), may stand in an attribute,
/// which serialized XML keeps, or may form across the markup an inner text
/// drops, so any of those in the source is a possible rejection.
fn judge_element_contents(
    state: &mut State<'_>,
    element: Node<'_, '_>,
    reached: bool,
    contents: Contents,
) {
    match (element_inner_contents(element), contents) {
        (Some(text), Contents::Text) => {
            judge_unwalked_text(state, &text, reached, element.range());
        }
        (Some(text), Contents::Metadata) => {
            judge_metadata_text(state, &text, reached, element.range());
        }
        (None, _) => note_unread_contents(state, element_content_source(element), element.range()),
    }
}

/// The source of `element`'s content: between its start tag and its end
/// tag, so neither its own attributes, which MSBuild does not read as its
/// text, nor its name. Empty for an empty element.
fn element_content_source<'input>(element: Node<'_, 'input>) -> &'input str {
    let source: &'input str = element.document().input_text();
    let whole = &source[element.range()];
    // The start tag ends at the first `>` outside an attribute's quotes; the
    // end tag starts at the last `</`, as nothing follows it but its name.
    let mut quote = None;
    let mut start = None;
    for (at, byte) in whole.bytes().enumerate() {
        match quote {
            Some(open) if byte == open => quote = None,
            Some(_) => {}
            None if matches!(byte, b'"' | b'\'') => quote = Some(byte),
            None if byte == b'>' => {
                start = Some(at + 1);
                break;
            }
            None => {}
        }
    }
    match (start, whole.rfind("</")) {
        (Some(start), Some(end)) if start <= end => &whole[start..end],
        _ => "",
    }
}

/// Note what a text MSBuild reads, and the walk could not read as it does,
/// may throw on: `source` is its markup as written. An expression may be
/// spelt with a reference (`&#36;(…)`), may stand in an attribute, which
/// serialized XML keeps, or may form across the markup an inner text drops,
/// and across the whitespace nodes it drops with it: any of those in the
/// source is a possible rejection.
fn note_unread_contents(state: &mut State<'_>, source: &str, span: Range<usize>) {
    let joined: String = without_markup(source)
        .chars()
        .filter(|c| !matches!(c, ' ' | '\t' | '\n' | '\r'))
        .collect();
    if source.contains("$(") || source.contains("&#") || joined.contains("$(") {
        let expression = properties::expression_texts(source)
            .next()
            .unwrap_or(source)
            .to_owned();
        state.note_possible_rejection(RejectionCause::ThrowingExpression { expression }, span);
    }
}

/// The text of `element`, which holds an element or a processing
/// instruction, as MSBuild reads it (`Utilities.GetXmlNodeInnerContents`):
/// its inner text where it starts with a CDATA section after any
/// whitespace, else its inner XML as `XmlDocument` serializes it
/// ([`serialize_inner_xml`]). `None` where it holds neither, which MSBuild
/// reads otherwise, or where the walk does not reproduce that reading: a
/// text whose line ends `roxmltree` folds and MSBuild's reader keeps, an
/// `xml:space` scope, a CDATA section beside other text, a namespace
/// declared or a prefix spelt, or a value serializing would spell as a
/// reference. Held to MSBuild's reading by `tests/element_contents_diff.rs`.
fn inner_xml(element: Node<'_, '_>) -> Option<String> {
    if !element
        .children()
        .any(|child| child.is_element() || child.is_pi())
    {
        return None;
    }
    let source = element.document().input_text();
    let body = &source[element.range()];
    if body.contains("xml:space") || under_xml_space(element) {
        return None;
    }
    let first = element
        .children()
        .find(|child| !(child.is_text() && is_whitespace_node(*child)));
    if let Some(first) = first
        && first.is_text()
        && source[first.range()].trim_start().starts_with("<![CDATA[")
    {
        // The inner text: every text and CDATA section beneath it, joined,
        // but for a whitespace node, which MSBuild's reader drops. `roxmltree`
        // joins a CDATA section and the text beside it into one node, where
        // MSBuild's reader sees a section and a text, either of which may be
        // a whitespace node it drops, and folds line ends MSBuild's reader
        // keeps: a node that is not one piece read as MSBuild reads it
        // declines.
        let mut text = String::new();
        for descendant in element.descendants().filter(Node::is_text) {
            if is_whitespace_node(descendant) {
                continue;
            }
            #[allow(clippy::disallowed_methods)]
            let value = descendant.text()?;
            let raw = &source[descendant.range()];
            let one_piece = match raw
                .strip_prefix("<![CDATA[")
                .and_then(|rest| rest.strip_suffix("]]>"))
            {
                Some(section) => section == value,
                None => crate::document::text(descendant).is_some_and(|read| read == value),
            };
            if !one_piece {
                return None;
            }
            text.push_str(value);
        }
        return Some(text);
    }
    let mut out = String::new();
    for child in element.children() {
        serialize_inner_xml(child, &mut out, 0, None)?;
    }
    Some(out)
}

/// How deeply [`serialize_inner_xml`] descends into an element's contents
/// before it declines: it recurses once per element, and a body nested
/// deeper than any task holds would otherwise take the stack.
const MAX_TASK_BODY_DEPTH: usize = 64;

/// `source` without its markup (every `<…>`, CDATA delimiters included), so
/// that text an element's tags separate is joined as an inner text joins it.
fn without_markup(source: &str) -> String {
    let mut out = String::with_capacity(source.len());
    let mut rest = source;
    while let Some(open) = rest.find('<') {
        out.push_str(&rest[..open]);
        rest = &rest[open..];
        // A section's text is kept; a comment, a processing instruction and
        // a tag end where their own syntax ends, a tag's `>` outside its
        // attributes' quotes.
        let (kept, end) = if let Some(after) = rest.strip_prefix("<![CDATA[") {
            let end = after.find("]]>").unwrap_or(after.len());
            (&after[..end], "<![CDATA[".len() + end + "]]>".len())
        } else if let Some(after) = rest.strip_prefix("<!--") {
            let end = after.find("-->").unwrap_or(after.len());
            ("", "<!--".len() + end + "-->".len())
        } else if let Some(after) = rest.strip_prefix("<?") {
            let end = after.find("?>").unwrap_or(after.len());
            ("", "<?".len() + end + "?>".len())
        } else {
            let mut quote = None;
            let mut end = rest.len();
            for (at, byte) in rest.bytes().enumerate() {
                match quote {
                    Some(open) if byte == open => quote = None,
                    Some(_) => {}
                    None if matches!(byte, b'"' | b'\'') => quote = Some(byte),
                    None if byte == b'>' => {
                        end = at + 1;
                        break;
                    }
                    None => {}
                }
            }
            ("", end)
        };
        out.push_str(kept);
        rest = rest.get(end..).unwrap_or("");
    }
    out.push_str(rest);
    out
}

/// Whether `node` is in the scope of an `xml:space` attribute, under which
/// MSBuild's reader keeps whitespace the walk would drop: the walk declines
/// such a reading.
fn under_xml_space(node: Node<'_, '_>) -> bool {
    node.ancestors()
        .any(|element| crate::document::xml_space(element).is_some())
}

/// Whether the text node `node` is a whitespace node MSBuild's reader drops:
/// XML whitespace alone, no decimal reference spelling any of it.
fn is_whitespace_node(node: Node<'_, '_>) -> bool {
    let source = node.document().input_text();
    let raw = &source[node.range()];
    let is_xml_whitespace =
        |text: &str| text.chars().all(|c| matches!(c, ' ' | '\t' | '\n' | '\r'));
    crate::document::text(node).is_some_and(|value| is_xml_whitespace(&value))
        && !raw
            .match_indices("&#")
            .any(|(at, _)| raw[at + 2..].starts_with(|c: char| c.is_ascii_digit()))
}

/// `node` written as `XmlTextWriter` writes it into an element's inner XML:
/// an element as `<name a="v" />` or `<name a="v">…</name>` (`"` around
/// every attribute value, its `&`, `<`, `>` and `"` as entities, the default
/// namespace declared after them where `written_namespace`, the one the
/// written XML already declares, is another), text with its `&`, `<` and
/// `>` as entities, a whitespace node not at all, a comment as written, a
/// processing instruction as `<?target data?>`. `None` where that is not
/// certain (see [`inner_xml`]).
fn serialize_inner_xml(
    node: Node<'_, '_>,
    out: &mut String,
    depth: usize,
    written_namespace: Option<&str>,
) -> Option<()> {
    if depth >= MAX_TASK_BODY_DEPTH {
        return None;
    }
    let source = node.document().input_text();
    let raw = &source[node.range()];
    let escape = |text: &str, attribute: bool| {
        let mut escaped = String::with_capacity(text.len());
        for c in text.chars() {
            match c {
                '&' => escaped.push_str("&amp;"),
                '<' => escaped.push_str("&lt;"),
                '>' => escaped.push_str("&gt;"),
                '"' if attribute => escaped.push_str("&quot;"),
                '\n' if attribute => escaped.push_str("&#xA;"),
                '\r' if attribute => escaped.push_str("&#xD;"),
                '\t' | '\n' | '\r' => escaped.push(c),
                c if c.is_control() => return None,
                c => escaped.push(c),
            }
        }
        Some(escaped)
    };
    if node.is_element() {
        // A namespace declaration, which `roxmltree` keeps out of the
        // attributes and `XmlDocument` keeps among them, in their order,
        // even where it declares what is in scope already.
        let declares = super::loader::attribute_names(node)
            .iter()
            .any(|name| *name == "xmlns" || name.starts_with("xmlns:"));
        // An element in a namespace it inherits (the project's own, as most
        // `.targets` declare) is serialized with that declaration after its
        // attributes, where the inner XML has not declared it yet; one that
        // declares a namespace or spells a prefix declines, and so does one
        // in none beneath one in some (which would take `xmlns=""`).
        let name = node.tag_name().name();
        let unprefixed = raw[1..].starts_with(name)
            && raw[1 + name.len()..]
                .starts_with(|c: char| c.is_whitespace() || c == '>' || c == '/');
        let namespace = node.tag_name().namespace();
        if declares || !unprefixed || (namespace.is_none() && written_namespace.is_some()) {
            return None;
        }
        out.push('<');
        out.push_str(name);
        for attr in node.attributes() {
            if attr.namespace().is_some() {
                return None;
            }
            let value = attribute(node, attr.name())?;
            out.push(' ');
            out.push_str(attr.name());
            out.push_str("=\"");
            out.push_str(&escape(&value, true)?);
            out.push('"');
        }
        if let Some(namespace) = namespace
            && written_namespace != Some(namespace)
        {
            out.push_str(" xmlns=\"");
            out.push_str(&escape(namespace, true)?);
            out.push('"');
        }
        if node.children().next().is_none() && raw.ends_with("/>") {
            out.push_str(" />");
        } else {
            out.push('>');
            // An element of text, CDATA sections and comments alone is read
            // piece by piece, a CDATA section kept as one.
            match crate::document::element_content(node) {
                Some(contents) => {
                    for content in contents {
                        match content {
                            crate::document::Content::Text {
                                whitespace: true, ..
                            } => {}
                            crate::document::Content::Text { value, .. } => {
                                out.push_str(&escape(&value, false)?);
                            }
                            crate::document::Content::CData(text) => {
                                out.push_str("<![CDATA[");
                                out.push_str(text);
                                out.push_str("]]>");
                            }
                            crate::document::Content::Comment(text) => {
                                out.push_str("<!--");
                                out.push_str(text);
                                out.push_str("-->");
                            }
                        }
                    }
                }
                None => {
                    for child in node.children() {
                        serialize_inner_xml(child, out, depth + 1, namespace)?;
                    }
                }
            }
            out.push_str("</");
            out.push_str(name);
            out.push('>');
        }
    } else if node.is_text() {
        if is_whitespace_node(node) {
            return Some(());
        }
        out.push_str(&escape(&crate::document::text(node)?, false)?);
    } else if node.is_comment() {
        out.push_str(raw);
    } else if let Some(instruction) = node.pi() {
        // Written from its target and data, a space between them however
        // the source spaced them, or none.
        out.push_str("<?");
        out.push_str(instruction.target);
        out.push(' ');
        out.push_str(instruction.value.unwrap_or(""));
        out.push_str("?>");
    }
    Some(())
}

/// Judge each metadatum of the item or item definition at `node` written as
/// an attribute, read as MSBuild reads one (`item_pass::metadata_attribute`),
/// which MSBuild expands as `reached` says.
fn judge_metadata_attributes(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    for attr in node.attributes() {
        if attr.namespace().is_none()
            && item_attribute(node, attr.name()) == ItemAttribute::Metadata
        {
            match metadata_attribute(node, &attr) {
                Some(text) => judge_metadata_text(state, &text, reached, node.range()),
                // An XML fragment the walk does not read as MSBuild does.
                None => {
                    let value = crate::document::attribute(node, attr.name()).unwrap_or_default();
                    note_unread_contents(state, &value, node.range());
                }
            }
        }
    }
}

/// What an attribute of an item is to MSBuild's evaluation
/// (`tests/condition_diff.rs`'s `where_msbuild_evaluates_a_text`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum ItemAttribute {
    /// Not expanded at evaluation: the condition (judged as one), a label,
    /// the operations only a target runs, the `MatchOnMetadata` options
    /// (parsed as written), and an operation's attribute the item's own
    /// operation does not read.
    Unexpanded,
    /// The item's operation: an `Include` and its `Exclude`, a `Remove` and
    /// its `MatchOnMetadata`, an `Update`.
    Operation,
    /// A metadatum of an `Include` or an `Update`, or of an item definition.
    Metadata,
}

/// What the attribute `name` of the item or item definition at `node` is to
/// MSBuild, by the item's operation: `LazyItemEvaluator.ProcessItemElement`
/// builds an `Include`, else a `Remove`, else an `Update`, and each build
/// expands only its own attributes. A reserved name in another case is no
/// metadatum but a loader error ([`loader`]), so the names are matched as
/// MSBuild spells them.
fn item_attribute(node: Node<'_, '_>, name: &str) -> ItemAttribute {
    let operation = ["Include", "Remove", "Update"]
        .into_iter()
        .find(|operation| attribute(node, operation).is_some());
    match (operation, name) {
        (
            _,
            "Condition"
            | "Label"
            | "KeepMetadata"
            | "RemoveMetadata"
            | "KeepDuplicates"
            | "MatchOnMetadataOptions",
        ) => ItemAttribute::Unexpanded,
        (Some("Include"), "Include" | "Exclude")
        | (Some("Remove"), "Remove" | "MatchOnMetadata")
        | (Some("Update"), "Update") => ItemAttribute::Operation,
        (_, "Include" | "Exclude" | "Remove" | "Update" | "MatchOnMetadata") => {
            ItemAttribute::Unexpanded
        }
        // A `Remove` builds no metadata: one written on it is never expanded
        // (probed, `msbuild-condition-oracle`, SDK 10.0.401).
        (Some("Remove"), _) => ItemAttribute::Unexpanded,
        _ => ItemAttribute::Metadata,
    }
}

/// Judge `text`, the value of an item's or item definition's metadatum
/// ([`judge_unwalked_text`]), but for an expression that reads item metadata
/// (`%(…)`): MSBuild expands a metadatum's metadata references into it before
/// its properties (escaped, so no expression's extent moves), and the walk's
/// expansion leaves them as text, so a throw it finds there is not MSBuild's.
/// An item list (`@(…)`) is expanded after the properties, so a function
/// reads it as written, as the walk does (`<M>$([MSBuild]::VersionEquals('@(J)',
/// '1.0'))</M>` throws whatever `J` holds; probed, `msbuild-condition-oracle`,
/// SDK 10.0.401).
fn judge_metadata_text(state: &mut State<'_>, text: &str, reached: bool, span: Range<usize>) {
    let expressions: Vec<Thrown> = throwing_expressions(text, state)
        .into_iter()
        .filter(|thrown| !thrown.expression.contains("%("))
        .collect();
    // A metadatum's value substituted into the text may move where an
    // expression starts or ends (`%(M)` holding `$(`), so a throw the walk
    // finds in such text is MSBuild's perhaps.
    let reached = reached && !text.contains("%(");
    if !expressions.is_empty() {
        judge_throwing_expression(state, expressions, reached, span);
    }
}

/// Judge the `<ItemGroup>` at `node`, which MSBuild reaches as `reached` says.
/// MSBuild evaluates each item's condition whatever the group's holds, and an
/// `Include` item's metadata conditions whatever the item's holds; an
/// `Update`'s metadata only where the update applies. Metadata that reads
/// item metadata (`%(…)`) or an item list (`@(…)`) is evaluated item by item,
/// so not at all when the `Include` names no item: then its conditions are
/// only possibly evaluated.
///
/// It expands an item's operation (an `Include` and its `Exclude`, a `Remove`
/// and its `MatchOnMetadata`, an `Update`) whatever the group's and the item's
/// conditions hold, and an `Include` item's metadata, child or attribute, as
/// it evaluates their conditions, but not under a false condition of the
/// metadatum's own; an `Update`'s metadata only where the update applies,
/// which the walk does not know here (`tests/condition_diff.rs`'s
/// `where_msbuild_evaluates_a_text`).
fn judge_item_group(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    let entry_dir = state.entry_project_dir.clone();
    judge_condition(node, &entry_dir, reached, state);
    for item in node.children().filter(Node::is_element) {
        judge_condition(item, &entry_dir, reached, state);
        // Design-time evaluation expands the operation whatever the group's
        // or the item's condition holds.
        for attr in item.attributes() {
            if attr.namespace().is_none()
                && item_attribute(item, attr.name()) == ItemAttribute::Operation
                && let Some(text) = attribute(item, attr.name())
            {
                // MSBuild reads a metadata reference in an operation as
                // written, as the walk does (`expand_metadata`).
                judge_unwalked_text(state, &text, reached, item.range());
            }
        }
        if let Some(sure) = loader::remove_matching_more_than_items(item) {
            state.note_rejection(
                certain_if(reached && sure),
                RejectionCause::IllegalItemOperation {
                    item: item.tag_name().name().to_owned(),
                },
                item.range(),
            );
        }
        // Read as MSBuild reads each value (a metadatum attribute read again
        // as XML, `&lt;![CDATA[%]]&gt;(Identity)` being `%(Identity)`); one the
        // walk cannot read counts as reading.
        let reads_items =
            |text: Option<&str>| text.is_none_or(|text| text.contains("%(") || text.contains("@("));
        let attribute_reads = |node: Node<'_, '_>, attr: &roxmltree::Attribute<'_, '_>| {
            if item_attribute(node, attr.name()) == ItemAttribute::Metadata {
                reads_items(metadata_attribute(node, attr).as_deref())
            } else {
                reads_items(attribute(node, attr.name()).as_deref())
            }
        };
        let per_item = item.attributes().any(|a| attribute_reads(item, &a))
            || item.children().filter(Node::is_element).any(|metadata| {
                reads_items(element_inner_contents(metadata).as_deref())
                    || metadata
                        .attributes()
                        .any(|a| reads_items(attribute(metadata, a.name()).as_deref()))
            });
        let metadata_reached = reached && attribute(item, "Include").is_some() && !per_item;
        // An `Update`'s metadata is expanded only where the update applies,
        // which the walk does not know here: reached perhaps. One under a
        // gate certainly false applies nowhere.
        let ruled_out = |node: Node<'_, '_>| {
            attribute(node, "Condition").is_some_and(|condition| {
                directory_build::decision_from_certain_inputs(state, &condition, &entry_dir)
                    == Some(false)
            })
        };
        if attribute(item, "Include").is_none() && (ruled_out(node) || ruled_out(item)) {
            continue;
        }
        judge_metadata_attributes(item, metadata_reached, state);
        for metadata in item.children().filter(Node::is_element) {
            if let Some(value_reached) =
                judge_gate(metadata, &entry_dir, metadata_reached, state).inner(metadata_reached)
            {
                judge_element_contents(state, metadata, value_reached, Contents::Metadata);
            }
        }
    }
}

/// Judge the `<ItemDefinitionGroup>` at `node`, which MSBuild reaches as
/// `reached` says. MSBuild evaluates a definition's condition only under a
/// true group, and its metadata's only under a true definition. `Exists` resolves
/// against the project's directory, as for every item-pass condition.
fn judge_item_definition_group(node: Node<'_, '_>, reached: bool, state: &mut State<'_>) {
    let entry_dir = state.entry_project_dir.clone();
    let Some(inner) = judge_gate(node, &entry_dir, reached, state).inner(reached) else {
        return;
    };
    for definition in node.children().filter(Node::is_element) {
        let Some(metadata_reached) = judge_gate(definition, &entry_dir, inner, state).inner(inner)
        else {
            continue;
        };
        judge_metadata_attributes(definition, metadata_reached, state);
        for metadata in definition.children().filter(Node::is_element) {
            if let Some(value_reached) =
                judge_gate(metadata, &entry_dir, metadata_reached, state).inner(metadata_reached)
            {
                judge_element_contents(state, metadata, value_reached, Contents::Metadata);
            }
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
    condition::decide_without(
        condition,
        &state.lookup,
        probes,
        state.condition_site(),
        &unknown,
    )
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
    // earlier one MSBuild would have made. Only an import MSBuild makes
    // whenever it takes the group, one with no condition of its own, makes a
    // later one a duplicate: one under a condition of its own may not be made
    // at all, so it is judged against no earlier import, and what it would
    // import makes no later one a duplicate.
    let mut seen = HashSet::new();
    for child in node.children().filter(|c| c.has_tag_name("Import")) {
        if attribute(child, "Condition").is_none() {
            undecided_import_within(child, current_file_dir, &mut seen, state);
        } else {
            undecided_import_within(child, current_file_dir, &mut HashSet::new(), state);
        }
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
/// The argument and `project` are compared as written
/// ([`condition::requires_exists`]).
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
    let expansion = expand_silent(&super::import_project_as_expanded(project), state);
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
    // The gate's `Exists`, asked as the gate's own evaluation asks it
    // ([`condition::exists_of_list`]): false rules the import out; true
    // leaves each entry to be judged below, as with no guard; undecided says
    // nothing of the import.
    if requires_own_file {
        let exists = |path: &str| super::condition_exists(state.observer, path, current_file_dir);
        match condition::exists_of_list(value, &exists) {
            Some(false) => return None,
            Some(true) => {}
            None => return Some(UnloadableImport::PathUndecided),
        }
    }
    if value.as_escaped().trim().is_empty() && !value.as_escaped().contains(';') {
        return Some(UnloadableImport::NoPath);
    }
    value.split_list().find_map(|segment| {
        let relative = segment.unescape().replace('\\', "/");
        // A wildcard MSBuild may expand is not judged: what it matches, and
        // whether each match loads, the walk declines to settle under a gate
        // it could not decide.
        if segment.is_filespec_wildcard() {
            return Some(UnloadableImport::PathUndecided);
        }
        // `GetFullPath` keeps a trailing separator, and a path ending in one
        // names a directory, which MSBuild never imports (MSB4019); the
        // collapse in `load_failure` would drop it.
        if relative.ends_with('/') {
            return Some(UnloadableImport::Failed(ImportFailReason::NotFound));
        }
        let path = current_file_dir.join(relative);
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
    let expansion = expand_silent(&super::import_project_as_expanded(project), state);
    // A rooted path that keeps a `\` is one the walk does not follow
    // (`follow_import_after_gate`).
    if path_undecided(project, state, expansion.had_unsupported)
        || super::sdk_import_keeps_a_rooted_backslash(
            project,
            expansion.value.ignoring_trust(),
            &resolution,
        )
    {
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
        // The SDK's own two files sit under its root, which MSBuild may read
        // as another directory.
        SdkResolution::Single(paths)
            if matches!(relative.as_str(), "Sdk.props" | "Sdk.targets")
                && sdk_root_is_reparsed(&paths.root) =>
        {
            return Some(UnloadableImport::PathUndecided);
        }
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
        if !sdk_project_written_rooted(project) && sdk_root_is_reparsed(root) {
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
