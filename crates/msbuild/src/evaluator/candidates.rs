//! The walk's candidate channel ([`crate::properties::candidates`]): what each
//! name may hold in the real build where the walk is not certain which value.
//!
//! The walk records a name's candidates wherever the real build may hold
//! something other than what the walk does, and the walk can bound it:
//!
//! - a write it ran on a gate it did not decide from certain inputs (its own,
//!   or an enclosing group's, `<Choose>`'s or import's): the candidates the
//!   name held before, and those of the value written;
//! - a write it ran on certain gates, of a value read from names it is not
//!   certain of: the candidates of that value;
//! - a write it skipped, or a `<Choose>` branch it did not take, on a gate it
//!   did not decide from certain inputs: the candidates the name held before,
//!   and those of the value the write would have written.
//!
//! A name with no record reads as the value the walk holds, where it is
//! certain of that, and as [`Candidates::Anything`] otherwise; so do refused
//! and stale names, whose writes the walk could not compute or see, and every
//! name after content the walk could not see (the table drops each record
//! then).
//!
//! A value's candidates are the products of the candidates of the names it
//! reads, expanded as the walk expands the value, where it only splices plain
//! references (`$(A)x$(B)`); where every name it reads is certain, the walk's
//! expansion of it; [`Candidates::Anything`] otherwise, and past
//! [`MAX_CANDIDATES`] or [`MAX_CANDIDATE_BYTES`].
//!
//! The channel shares the walk's assumptions about MSBuild's process: that a
//! relative path the Unix path adjustment probes names nothing in its working
//! directory (`properties::Relative::MissForProjectText`).
//!
//! Nothing decides on candidates yet. `tests/fsproj_candidates_diff.rs` and
//! `tests/fsproj_global_perturbation_diff.rs` hold the channel to MSBuild:
//! under globals that steer gates the walk cannot decide, the value MSBuild
//! ends with is always among a name's candidates.

use std::collections::{BTreeSet, HashMap};

use roxmltree::Node;

use crate::properties::candidates::{Candidate, Candidates, MAX_CANDIDATE_BYTES, MAX_CANDIDATES};
use crate::properties::escaping::Escaped;
use crate::properties::{self, Origin, PropertyMap};

use super::{State, attribute, collect_element_text, directory_build};

impl State<'_> {
    /// What `name` may hold in the real build now.
    pub(super) fn candidates_of(&self, name: &str) -> Candidates {
        let trust = self.trust_of(name);
        if trust.stale().is_some() || trust.refused() {
            return Candidates::Anything;
        }
        if let Some(recorded) = self.lookup.recorded_candidates(name) {
            return recorded.clone();
        }
        if directory_build::is_certain(self, name) {
            return Candidates::one(
                self.lookup
                    .held_candidate(name)
                    .unwrap_or_else(Candidate::undefined),
            );
        }
        Candidates::Anything
    }

    /// Whether every name `raw` reads is one the walk is certain of.
    pub(super) fn reads_only_certain(&self, raw: &str) -> bool {
        properties::property_references(raw).all(|name| directory_build::is_certain(self, name))
    }

    /// Whether the walk is inside a gate it did not decide from certain
    /// inputs: a property group's, a `<Choose>` branch's, or an import's.
    pub(super) fn inside_doubted_gate(&self) -> bool {
        self.reach_doubted > 0 || !directory_build::reached_for_certain(self)
    }

    /// The candidates of a value spelt `raw`.
    pub(super) fn value_candidates(&self, raw: &str) -> Candidates {
        if self.reads_only_certain(raw) {
            let (value, issues) = self.expand_for_candidates(raw, &self.lookup);
            return if issues.is_empty() && value.trust().is_certain() {
                let value = value.into_ignoring_trust();
                if value.as_escaped().len() > MAX_CANDIDATE_BYTES {
                    Candidates::Anything
                } else {
                    Candidates::one(Candidate::new(&value, Origin::Expansion))
                }
            } else {
                Candidates::Anything
            };
        }
        if !splices_plain_references_only(raw) {
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
            let length = raw.len()
                + names
                    .iter()
                    .zip(&choice)
                    .zip(&each)
                    .map(|(((_, count), &at), options)| count * options[at].text.len())
                    .sum::<usize>();
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
        if self.follow_imports {
            properties::substitute_with_fs(raw, table, self.observer)
        } else {
            properties::substitute(raw, table)
        }
    }

    /// The candidates of a property element whose write the real build may
    /// run though the walk did not: what the name holds now, or the element's
    /// value.
    pub(super) fn widened_candidates(&self, element: Node<'_, '_>) -> Candidates {
        let name = element.tag_name().name();
        let value = collect_element_text(element)
            .map_or(Candidates::Anything, |raw| self.value_candidates(&raw));
        self.candidates_of(name).union(value)
    }

    /// Widen, one write after another, the candidates of every property
    /// `group` writes: a group the walk skipped, which the real build may take.
    pub(super) fn widen_group_candidates(&mut self, group: Node<'_, '_>) {
        for element in group.children().filter(Node::is_element) {
            let name = element.tag_name().name();
            if self.protected.contains(&name.to_ascii_lowercase()) {
                continue;
            }
            let widened = self.widened_candidates(element);
            self.lookup.record_candidates(name, widened);
        }
    }

    /// [`Self::widen_group_candidates`] for every property group in `branch`
    /// (a `<When>` or `<Otherwise>`), nested `<Choose>`s' branches included: a
    /// branch the walk did not take, which the real build may.
    pub(super) fn widen_branch_candidates(&mut self, branch: Node<'_, '_>) {
        for child in branch.children().filter(Node::is_element) {
            match child.tag_name().name() {
                "PropertyGroup" => self.widen_group_candidates(child),
                "Choose" => {
                    for nested in child.children().filter(Node::is_element) {
                        self.widen_branch_candidates(nested);
                    }
                }
                _ => {}
            }
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
        if before.is_none() && value.is_none() && directory_build::is_certain(self, name) {
            return;
        }
        let value = value.unwrap_or_else(|| match self.lookup.held_candidate(name) {
            Some(held) if carried_certain => Candidates::one(held),
            _ => Candidates::Anything,
        });
        let candidates = before.map_or(value.clone(), |before| before.union(value));
        self.lookup.record_candidates(name, candidates);
    }
}

/// Whether a property element's own gate is decided from values the walk is
/// certain of: absent, or decided whatever the others hold.
pub(super) fn own_gate_is_certain(state: &State<'_>, element: Node<'_, '_>) -> bool {
    attribute(element, "Condition").is_none_or(|condition| {
        directory_build::decided_from_certain_inputs(state, &condition, &state.entry_project_dir)
    })
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
