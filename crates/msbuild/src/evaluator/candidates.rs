//! The walk's candidate channel ([`crate::properties::candidates`]): what each
//! name the walk is not certain of may hold in the real build.
//!
//! Every property write the walk reaches records its name's candidates:
//!
//! - a write it takes for certain: the candidates of its value;
//! - one under a gate it could not decide, taken or not: the candidates the
//!   name held before, and those of the value it would write;
//! - one it refuses, or one after content it could not see: none, which reads
//!   as [`Candidates::Anything`] (the refused and stale channels say why).
//!
//! A value's candidates are the products of the candidates of the names it
//! reads, expanded as the walk expands the value, where the value only
//! splices plain references (`$(A)x$(B)`); a value that calls a property
//! function has the written value as its one candidate when every name it
//! reads is certain, and [`Candidates::Anything`] otherwise. Past
//! [`MAX_CANDIDATES`] the product is [`Candidates::Anything`] too.
//!
//! Nothing decides on candidates yet. `tests/fsproj_candidates_diff.rs` holds
//! the channel to MSBuild: under globals that steer gates the walk cannot
//! decide, the value MSBuild ends with is always among a name's candidates.

use std::collections::BTreeSet;

use crate::properties::candidates::{Candidate, Candidates, MAX_CANDIDATES};
use crate::properties::escaping::Escaped;
use crate::properties::{self, Origin, PropertyMap};

use super::{State, directory_build};

impl State<'_> {
    /// What `name` may hold in the real build now.
    pub(super) fn candidates_of(&self, name: &str) -> Candidates {
        let trust = self.trust_of(name);
        if trust.stale().is_some() || trust.refused() {
            return Candidates::Anything;
        }
        // A name the walk is certain of holds what it reads.
        if directory_build::is_certain(self, name) {
            return Candidates::one(
                self.lookup
                    .held_candidate(name)
                    .unwrap_or_else(Candidate::undefined),
            );
        }
        self.lookup
            .recorded_candidates(name)
            .cloned()
            .unwrap_or(Candidates::Anything)
    }

    /// The candidates of a value spelt `raw`, which the walk expanded to
    /// `written` (`None` where it wrote nothing: a write it skipped).
    pub(super) fn value_candidates(&self, raw: &str, written: Option<&Candidate>) -> Candidates {
        let mut names: Vec<&str> = Vec::new();
        for name in properties::property_references(raw) {
            if !names.iter().any(|seen| seen.eq_ignore_ascii_case(name)) {
                names.push(name);
            }
        }
        if !splices_plain_references_only(raw) {
            return match written {
                Some(written)
                    if names
                        .iter()
                        .all(|name| directory_build::is_certain(self, name)) =>
                {
                    Candidates::one(written.clone())
                }
                _ => Candidates::Anything,
            };
        }
        let mut each: Vec<Vec<Candidate>> = Vec::with_capacity(names.len());
        let mut product = 1usize;
        for name in &names {
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
            let bindings: Vec<(&str, &Candidate)> = names
                .iter()
                .zip(&choice)
                .zip(&each)
                .map(|((name, &at), options)| (*name, &options[at]))
                .collect();
            let table = PropertyMap::of_candidates(&bindings);
            let (value, issues) = if self.follow_imports {
                properties::substitute_with_fs(raw, &table, self.observer)
            } else {
                properties::substitute(raw, &table)
            };
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

    /// Record `name`'s candidates after a write of `value` (its candidates),
    /// which the walk takes for certain unless `doubted`: then the real build
    /// may also keep `before`, the candidates the name held before it.
    pub(super) fn record_write_candidates(
        &mut self,
        name: &str,
        before: Candidates,
        value: Candidates,
        doubted: bool,
    ) {
        let candidates = if doubted { before.union(value) } else { value };
        self.lookup.record_candidates(name, candidates);
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
