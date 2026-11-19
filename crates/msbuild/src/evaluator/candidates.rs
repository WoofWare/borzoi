//! The walk's candidate channel ([`crate::properties::candidates`]): what each
//! name may hold in the real build where the walk is not certain which value.
//!
//! A name the walk holds exactly ([`State::held_exactly`], the test on which
//! the end of the walk commits a value or an unset) has that value as its one
//! candidate, whatever is recorded for it: the channel's certainty is the
//! walk's. A refused or stale name the walk does not hold exactly may hold
//! anything. Every other name reads as what the walk recorded for it, or as
//! anything where it recorded nothing:
//!
//! - a write it ran on a gate it did not decide from certain inputs (its own,
//!   or an enclosing group's, `<Choose>`'s or import's): the candidates the
//!   name held before, and those of the value written;
//! - a write it ran on certain gates, of a value read from names it does not
//!   hold exactly: the candidates of that value;
//! - a write it skipped, or a `<Choose>` branch it did not take, on a gate it
//!   did not decide from certain inputs for a reason that leaves the name no
//!   mark (a stale value read leaves it stale, a diagnostic unpinned): the
//!   candidates the name held before, and those of the value the write would
//!   have written.
//!
//! The table drops every record when the walk passes content it could not see.
//! And once an imported document opts a caller global out of protection, the
//! channel names nothing at all ([`State::candidates_withdrawn`], #1041).
//!
//! A value is expanded speculatively only where it splices plain references
//! (`$(A)x$(B)`): its candidates are the products of the candidates of the
//! names it reads, expanded as the walk expands the value, each product's
//! length bounded before it is built. Any other value, and any past
//! [`MAX_CANDIDATES`] or [`MAX_CANDIDATE_BYTES`], is [`Candidates::Anything`].
//!
//! The channel shares the walk's assumptions about MSBuild's process: that a
//! relative path the Unix path adjustment probes names nothing in its working
//! directory (`properties::Relative::MissForProjectText`).
//!
//! Nothing decides on candidates yet. `tests/fsproj_candidates_diff.rs`,
//! `tests/fsproj_stale_gate_diff.rs` and
//! `tests/fsproj_global_perturbation_diff.rs` hold the channel to MSBuild:
//! under globals that steer gates the walk cannot decide, the value MSBuild
//! ends with is always among a name's candidates, and a value the walk commits
//! is its only one.

use std::collections::{BTreeSet, HashMap};

use roxmltree::Node;

use crate::properties::candidates::{Candidate, Candidates, MAX_CANDIDATE_BYTES, MAX_CANDIDATES};
use crate::properties::escaping::Escaped;
use crate::properties::{self, Origin, PropertyMap};

use super::{State, attribute, collect_element_text, directory_build};

impl State<'_> {
    /// What `name` may hold in the real build now: the value the walk holds,
    /// where it holds it exactly; what the walk recorded, where it doubts it;
    /// anything otherwise.
    pub(super) fn candidates_of(&self, name: &str) -> Candidates {
        if !self.track_candidates {
            return Candidates::Anything;
        }
        if self.held_exactly_for_candidates(name) {
            // One past the budget is not copied only to be dropped.
            if self
                .lookup
                .held_len(name)
                .is_some_and(|len| len > MAX_CANDIDATE_BYTES)
            {
                return Candidates::Anything;
            }
            return Candidates::one(
                self.lookup
                    .held_candidate(name)
                    .unwrap_or_else(Candidate::undefined),
            );
        }
        let trust = self.trust_of(name);
        if self.candidates_withdrawn || trust.stale().is_some() || trust.refused() {
            return Candidates::Anything;
        }
        self.lookup
            .recorded_candidates(name)
            .cloned()
            .unwrap_or(Candidates::Anything)
    }

    /// Whether the walk holds `name` exactly ([`State::held_exactly`]), as
    /// the channel takes it: never once the channel is withdrawn
    /// ([`State::candidates_withdrawn`], #1041).
    pub(super) fn held_exactly_for_candidates(&self, name: &str) -> bool {
        !self.candidates_withdrawn && self.held_exactly(name)
    }

    /// Whether the walk holds every name `raw` reads exactly
    /// ([`Self::held_exactly_for_candidates`]).
    pub(super) fn reads_only_certain(&self, raw: &str) -> bool {
        properties::property_references(raw).all(|name| self.held_exactly_for_candidates(name))
    }

    /// Whether the walk is inside a gate it did not decide from certain
    /// inputs: a property group's, a `<Choose>` branch's, or an import's.
    pub(super) fn inside_doubted_gate(&self) -> bool {
        self.reach_doubted > 0 || !directory_build::reached_for_certain(self)
    }

    /// The candidates of a value spelt `raw`, expanded speculatively: only
    /// text that splices plain references is, whose length the candidates it
    /// splices bound before it is built.
    pub(super) fn value_candidates(&self, raw: &str) -> Candidates {
        if !self.track_candidates {
            return Candidates::Anything;
        }
        // The text alone bounds every expansion of it from below.
        if raw.len() > MAX_CANDIDATE_BYTES || !splices_plain_references_only(raw) {
            return Candidates::Anything;
        }
        // Each name `raw` reads, first spelling first, with how many times.
        let mut names: Vec<(&str, usize)> = Vec::new();
        let mut index: HashMap<String, usize> = HashMap::new();
        for name in properties::property_references(raw) {
            match index.entry(name.to_ascii_lowercase()) {
                std::collections::hash_map::Entry::Occupied(at) => names[*at.get()].1 += 1,
                std::collections::hash_map::Entry::Vacant(slot) => {
                    slot.insert(names.len());
                    names.push((name, 1));
                }
            }
        }
        // The bytes outside the references, each `$(Name)` spelt in
        // `Name.len() + 3` of them.
        let literal_bytes = raw.len()
            - names
                .iter()
                .map(|(name, count)| count * (name.len() + 3))
                .sum::<usize>();
        let mut each: Vec<Vec<Candidate>> = Vec::with_capacity(names.len());
        let mut product = 1usize;
        for (name, _) in &names {
            let Candidates::OneOf(values) = self.candidates_of(name) else {
                return Candidates::Anything;
            };
            product = product.saturating_mul(values.len());
            if product > MAX_CANDIDATES {
                return Candidates::Anything;
            }
            each.push(values.into_iter().collect());
        }
        let mut values = BTreeSet::new();
        let mut choice = vec![0usize; names.len()];
        loop {
            // The expansion splices each candidate where its name is read, so
            // this bounds its length before it is built.
            let length = names
                .iter()
                .zip(&choice)
                .zip(&each)
                .map(|(((_, count), &at), options)| count.saturating_mul(options[at].text.len()))
                .fold(literal_bytes, usize::saturating_add);
            if length > MAX_CANDIDATE_BYTES {
                return Candidates::Anything;
            }
            let bindings: Vec<(&str, &Candidate)> = names
                .iter()
                .zip(&choice)
                .zip(&each)
                .map(|(((name, _), &at), options)| (*name, &options[at]))
                .collect();
            let table = PropertyMap::of_candidates(&bindings);
            let (value, issues) = self.expand_for_candidates(raw, &table);
            if !issues.is_empty() {
                return Candidates::Anything;
            }
            let value: Escaped = value.into_ignoring_trust();
            values.insert(Candidate::new(&value, Origin::Expansion));
            // The next choice, odometer style; done when every name wrapped.
            let mut position = 0;
            loop {
                if position == choice.len() {
                    return Candidates::bounded(values);
                }
                choice[position] += 1;
                if choice[position] < each[position].len() {
                    break;
                }
                choice[position] = 0;
                position += 1;
            }
        }
    }

    fn expand_for_candidates(
        &self,
        raw: &str,
        table: &PropertyMap,
    ) -> (properties::Provenanced<Escaped>, Vec<properties::Issue>) {
        // Without the file system, and assuming nothing of MSBuild's working
        // directory: a speculative value is no reason for the evaluation to
        // depend on what a probe would find, so one the Unix path adjustment
        // would probe for, relative or absolute, is an issue, and anything.
        properties::substitute_undecided(raw, table)
    }

    /// The candidates of a property element whose write the real build may
    /// run though the walk did not: what the name holds now, or the element's
    /// value.
    pub(super) fn widened_candidates(&self, element: Node<'_, '_>) -> Candidates {
        if !self.track_candidates {
            return Candidates::Anything;
        }
        let name = element.tag_name().name();
        // A body whose source alone is far past the budget is not collected
        // only to be dropped; comments in it may make that a decline.
        if element.range().len() > 4 * MAX_CANDIDATE_BYTES {
            return Candidates::Anything;
        }
        let value = collect_element_text(element)
            .map_or(Candidates::Anything, |raw| self.value_candidates(&raw));
        self.candidates_of(name).union(value)
    }

    /// Widen, one write after another, the candidates of every property
    /// `group` writes: a group the walk skipped, which the real build may take.
    pub(super) fn widen_group_candidates(&mut self, group: Node<'_, '_>) {
        if !self.track_candidates {
            return;
        }
        for element in group.children().filter(Node::is_element) {
            let name = element.tag_name().name();
            if self.protected.contains(&name.to_ascii_lowercase())
                || self.ruled_out_without_files(element)
            {
                continue;
            }
            let widened = self.widened_candidates(element);
            self.record_candidates(name, widened);
        }
    }

    /// [`Self::widen_group_candidates`] for every property group in `branch`
    /// (a `<When>` or `<Otherwise>`), nested `<Choose>`s' branches included: a
    /// branch the walk did not take, which the real build may.
    /// A group or a nested branch a gate rules out on every input, decided
    /// without the file system, is skipped, its children unread.
    pub(super) fn widen_branch_candidates(&mut self, branch: Node<'_, '_>) {
        if !self.track_candidates {
            return;
        }
        for child in branch.children().filter(Node::is_element) {
            match child.tag_name().name() {
                "PropertyGroup" if !self.ruled_out_without_files(child) => {
                    self.widen_group_candidates(child);
                }
                "Choose" => {
                    for nested in self.choose_branches_from(child, 0, None, false) {
                        self.widen_branch_candidates(nested);
                    }
                }
                _ => {}
            }
        }
    }

    /// Whether `node`'s gate is false whatever the names the walk is not
    /// certain of hold, decided without the file system
    /// ([`directory_build::decision_without_files`]).
    pub(super) fn ruled_out_without_files(&self, node: Node<'_, '_>) -> bool {
        attribute(node, "Condition").is_some_and(|condition| {
            directory_build::decision_without_files(self, &condition) == Some(false)
        })
    }

    /// Record `name`'s candidates, where the walk tracks them.
    pub(super) fn record_candidates(&mut self, name: &str, candidates: Candidates) {
        if self.track_candidates {
            self.lookup.record_candidates(name, candidates);
        }
    }

    /// Record `name`'s candidates after the walk wrote it. `before` is what it
    /// held before, where the write's gate leaves that in doubt; `value` the
    /// candidates of the value, where it reads names the walk is not certain
    /// of (computed before the write, which may read the name itself); and
    /// `carried_certain` whether the expansion the walk wrote carried no
    /// doubt of its own.
    pub(super) fn record_write_candidates(
        &mut self,
        name: &str,
        before: Option<Candidates>,
        value: Option<Candidates>,
        carried_certain: bool,
    ) {
        if !self.track_candidates {
            return;
        }
        if before.is_none() && value.is_none() && self.held_exactly_for_candidates(name) {
            // What it holds is its only candidate already.
            return;
        }
        let value = value.unwrap_or_else(|| {
            let within_budget = self
                .lookup
                .held_len(name)
                .is_none_or(|len| len <= MAX_CANDIDATE_BYTES);
            match carried_certain && within_budget {
                true => self
                    .lookup
                    .held_candidate(name)
                    .map_or(Candidates::Anything, Candidates::one),
                false => Candidates::Anything,
            }
        });
        let candidates = before.map_or(value.clone(), |before| before.union(value));
        self.record_candidates(name, candidates);
    }
}

/// Whether every `$(` in `raw` opens a plain reference, `$(Name)`, and nothing
/// in it is an item or metadata expression: text whose expansion splices the
/// values it reads and nothing more.
fn splices_plain_references_only(raw: &str) -> bool {
    if raw.contains("@(") || raw.contains("%(") {
        return false;
    }
    let mut rest = raw;
    while let Some(at) = rest.find("$(") {
        let after = &rest[at + 2..];
        let len = after
            .bytes()
            .take_while(|&b| properties::is_name_byte(b))
            .count();
        if len == 0 || after.as_bytes().get(len) != Some(&b')') {
            return false;
        }
        rest = &after[len + 1..];
    }
    true
}

#[cfg(test)]
mod tests {
    use super::splices_plain_references_only;

    #[test]
    fn only_plain_references_splice() {
        for plain in ["", "a", "$(A)", "x$(A)y$(B_c-1)", "a;b", "$ (A)", "%24(A)"] {
            assert!(splices_plain_references_only(plain), "{plain:?}");
        }
        for call in [
            "$(A.Trim())",
            "$([MSBuild]::Add(1, 2))",
            "$(A",
            "$()",
            "@(Compile)",
            "%(Identity)",
            "$(A)$(B.Length)",
        ] {
            assert!(!splices_plain_references_only(call), "{call:?}");
        }
    }
}
