//! The values a property may hold in the real build, where the walk is not
//! certain which: its *candidates* (#1009).
//!
//! The trust channels ([`super::trust`]) say whether the walk knows a value;
//! candidates say what else it may be. They are tracked where the walk can
//! bound them — a write under a gate it could not decide adds its value and
//! keeps the earlier candidates, and a value built from such names is their
//! product — and are [`Candidates::Anything`] wherever it cannot: a refused
//! write, content it did not see, a toolset or environment value it was not
//! handed, a product too large to keep.
//!
//! A candidate is a value as MSBuild stores it: escaped text and the origin
//! that decides whether its backslashes have met the Unix path adjustment
//! ([`super::Origin`]). An undefined name's value is the empty string, which
//! is what every read of it expands to.

use std::collections::BTreeSet;

use super::Origin;
use super::escaping::Escaped;

/// How many candidates a name keeps before it holds [`Candidates::Anything`].
/// A product of names multiplies their counts, so the bound also bounds the
/// work of building one.
pub(crate) const MAX_CANDIDATES: usize = 16;

/// The bytes of escaped text every name's recorded candidates in one table may
/// take together, past which a further record is [`Candidates::Anything`]:
/// each name's are bounded, but copies of one set are not.
pub(crate) const MAX_RECORDED_CANDIDATE_BYTES: usize = 1 << 20;

/// The longest candidate, in bytes of escaped text, a name keeps before it
/// holds [`Candidates::Anything`]. A value that splices a name twice doubles
/// its candidates' length while their count stays put, so the count alone
/// bounds neither the memory nor the work.
pub(crate) const MAX_CANDIDATE_BYTES: usize = 4096;

/// One candidate value: escaped text, and how MSBuild stored it.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Candidate {
    pub(crate) text: String,
    pub(crate) origin: Origin,
}

impl Candidate {
    pub(crate) fn new(value: &Escaped, origin: Origin) -> Self {
        Candidate {
            text: value.as_escaped().to_owned(),
            origin,
        }
    }

    /// The candidate an undefined name reads as.
    pub(crate) fn undefined() -> Self {
        Candidate {
            text: String::new(),
            origin: Origin::Seed,
        }
    }

    pub(crate) fn value(&self) -> Escaped {
        Escaped::from_xml(self.text.clone())
    }
}

/// The values a property may hold at a point of the walk.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Candidates {
    /// Any value at all.
    Anything,
    /// One of these, never more than [`MAX_CANDIDATES`] and never none.
    OneOf(BTreeSet<Candidate>),
}

impl Candidates {
    /// `candidate` alone, or [`Candidates::Anything`] past the byte bound.
    pub(crate) fn one(candidate: Candidate) -> Self {
        Candidates::bounded(BTreeSet::from([candidate]))
    }

    /// The values either may hold.
    pub(crate) fn union(self, other: Candidates) -> Candidates {
        match (self, other) {
            (Candidates::OneOf(mut mine), Candidates::OneOf(theirs)) => {
                mine.extend(theirs);
                Candidates::bounded(mine)
            }
            _ => Candidates::Anything,
        }
    }

    /// `values` as candidates, or [`Candidates::Anything`] past either bound.
    pub(crate) fn bounded(values: BTreeSet<Candidate>) -> Candidates {
        debug_assert!(!values.is_empty(), "a name holds some value");
        if values.len() > MAX_CANDIDATES
            || values
                .iter()
                .any(|candidate| candidate.text.len() > MAX_CANDIDATE_BYTES)
        {
            Candidates::Anything
        } else {
            Candidates::OneOf(values)
        }
    }

    /// The bytes of escaped text the candidates take.
    pub(crate) fn bytes(&self) -> usize {
        match self {
            Candidates::Anything => 0,
            Candidates::OneOf(values) => values.iter().map(|value| value.text.len()).sum(),
        }
    }

    /// The candidates, unless they are [`Candidates::Anything`].
    #[cfg(any(test, feature = "test-support"))]
    pub(crate) fn values(&self) -> Option<&BTreeSet<Candidate>> {
        match self {
            Candidates::Anything => None,
            Candidates::OneOf(values) => Some(values),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn of(texts: &[&str]) -> Candidates {
        Candidates::bounded(
            texts
                .iter()
                .map(|text| Candidate {
                    text: (*text).to_owned(),
                    origin: Origin::Expansion,
                })
                .collect(),
        )
    }

    #[test]
    fn union_keeps_both_sides_and_anything_absorbs() {
        assert_eq!(of(&["a"]).union(of(&["b", "a"])), of(&["a", "b"]));
        assert_eq!(of(&["a"]).union(Candidates::Anything), Candidates::Anything);
        assert_eq!(Candidates::Anything.union(of(&["a"])), Candidates::Anything);
    }

    #[test]
    fn past_the_bound_is_anything() {
        let many: Vec<String> = (0..=MAX_CANDIDATES).map(|i| i.to_string()).collect();
        let many: Vec<&str> = many.iter().map(String::as_str).collect();
        assert_eq!(of(&many), Candidates::Anything);
        assert!(of(&many[..MAX_CANDIDATES]).values().is_some());
    }
}
