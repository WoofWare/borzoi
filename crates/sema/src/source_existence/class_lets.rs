//! The compiled names of a type's `let` bindings.
//!
//! FCS represents a type's `let`s and primary-constructor arguments one at a
//! time (`CheckIncrementalClasses.fs`, `ChooseRepresentation`): the
//! constructor's arguments first, then its `as` self identifier, then each
//! `let` binding in source order. Each takes its logical name unless that
//! name is already taken: by a member binding (its logical, compiled and
//! display names), by a field the type declares, or by an earlier
//! representation. A taken name becomes `basic@line`, where `basic` is the
//! name before its first `@` (unless that is the first character) and
//! `line` is the 1-based line of the binder's identifier, with `-k` after
//! it for the `k`th earlier fresh name of the same `basic` in the type; and
//! that name is taken in turn. A `let` that takes arguments becomes a method
//! val under the name it took, which a C#-style extension row carries.
//!
//! [`LetNames`] is that sequence, over names that may be uncertain: a name
//! only possibly taken (a member whose `[<CompiledName>]` is uncertain), a
//! binder only possibly present (a pattern that may match a union case), or
//! a count of earlier fresh names only bounded. Each binding then has every
//! compiled name it may take, and the walk emits one row per name.

use std::collections::{BTreeMap, BTreeSet};

/// Whether a name is taken.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Taken {
    No,
    Possibly,
    Yes,
}

/// The names a type's representation has taken, as its bindings are
/// represented in order.
#[derive(Debug, Default)]
pub(super) struct LetNames {
    taken: BTreeSet<String>,
    possibly: BTreeSet<String>,
    /// Every name may be taken: a member or argument the walk cannot name.
    opaque: bool,
    /// Fresh names of any `basic` the walk cannot attribute (an argument it
    /// cannot name): each widens every count's upper bound by one.
    unattributed: u32,
    /// Per `basic`, the fewest and most fresh names generated so far.
    counts: BTreeMap<String, (u32, u32)>,
    /// A name with a parenthesis may be a member's display name (an
    /// operator's `(+)`, an active pattern's `(|A|_|)`).
    members_present: bool,
    /// A name with a `.` or `-` may be an interface implementation's
    /// compiled name.
    interface_present: bool,
}

/// The `basic` FCS's `GetBasicNameOfPossibleCompilerGeneratedName` gives:
/// the name before its first `@`, unless that is its first character.
fn basic_name(name: &str) -> &str {
    match name.find('@') {
        None | Some(0) => name,
        Some(n) => &name[..n],
    }
}

/// The `k`th fresh name of `basic` at `line`: `basic@line`, then
/// `basic@line-k`.
fn fresh(basic: &str, line: u32, k: u32) -> String {
    if k == 0 {
        format!("{basic}@{line}")
    } else {
        format!("{basic}@{line}-{k}")
    }
}

impl LetNames {
    /// `name` is taken: a member's logical or compiled name, or a field's.
    pub(super) fn take(&mut self, name: &str) {
        self.taken.insert(name.to_owned());
    }

    /// `name` may be taken.
    pub(super) fn possibly_take(&mut self, name: &str) {
        self.possibly.insert(name.to_owned());
    }

    /// Some name the walk cannot spell may be taken.
    pub(super) fn take_unknown(&mut self) {
        self.opaque = true;
    }

    /// The type has members, whose display names may be taken.
    pub(super) fn members_present(&mut self) {
        self.members_present = true;
    }

    /// The type implements an interface, whose members' compiled names may
    /// be taken.
    pub(super) fn interface_present(&mut self) {
        self.interface_present = true;
    }

    /// A binder the walk cannot name, which takes a name and may generate
    /// a fresh one of any `basic`.
    pub(super) fn bind_unknown(&mut self) {
        self.opaque = true;
        self.unattributed += 1;
    }

    fn taken(&self, name: &str) -> Taken {
        if self.taken.contains(name) {
            return Taken::Yes;
        }
        // A name with an `@` may be one FCS generated that the walk does not
        // track (a static initialisation field's `init@…`).
        let possibly = self.opaque
            || self.possibly.contains(name)
            || name.contains('@')
            || (self.members_present && name.contains(['(', ')']))
            || (self.interface_present && name.contains(['.', '-']));
        if possibly { Taken::Possibly } else { Taken::No }
    }

    /// The fresh names `name` may take at `line`, and the count after.
    fn fresh_names(&self, name: &str, line: u32) -> (Vec<String>, (u32, u32)) {
        let basic = basic_name(name);
        let (lo, hi) = self.counts.get(basic).copied().unwrap_or((0, 0));
        let names = (lo..=hi + self.unattributed)
            .map(|k| fresh(basic, line, k))
            .collect();
        (names, (lo, hi))
    }

    /// Represent a binder certainly named `name` whose identifier is on
    /// `line`: every name it may take.
    pub(super) fn bind(&mut self, name: &str, line: u32) -> Vec<String> {
        let basic = basic_name(name).to_owned();
        match self.taken(name) {
            Taken::No => {
                self.taken.insert(name.to_owned());
                vec![name.to_owned()]
            }
            Taken::Yes => {
                let (names, (lo, hi)) = self.fresh_names(name, line);
                self.counts.insert(basic, (lo + 1, hi + 1));
                self.record(&names);
                names
            }
            Taken::Possibly => {
                // Whichever reading holds, `name` is taken after: by what
                // may have taken it before, or by this binder.
                let (mut names, (lo, hi)) = self.fresh_names(name, line);
                self.counts.insert(basic, (lo, hi + 1));
                self.possibly.extend(names.iter().cloned());
                self.taken.insert(name.to_owned());
                names.insert(0, name.to_owned());
                names
            }
        }
    }

    /// Represent a binder that may or may not be present, named `name` on
    /// `line` if it is (a pattern that may instead match a union case):
    /// every name it may take.
    pub(super) fn possibly_bind(&mut self, name: &str, line: u32) -> Vec<String> {
        let basic = basic_name(name).to_owned();
        let taken = self.taken(name);
        let mut names = Vec::new();
        if taken != Taken::Yes {
            names.push(name.to_owned());
        }
        if taken != Taken::No {
            let (fresh, (lo, hi)) = self.fresh_names(name, line);
            self.counts.insert(basic, (lo, hi + 1));
            names.extend(fresh);
        }
        for n in &names {
            self.possibly.insert(n.clone());
        }
        names
    }

    /// Names a binding took: one certainly, several possibly.
    fn record(&mut self, names: &[String]) {
        match names {
            [one] => {
                self.taken.insert(one.clone());
            }
            _ => self.possibly.extend(names.iter().cloned()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_repeated_name_counts_its_fresh_names() {
        let mut names = LetNames::default();
        assert_eq!(names.bind("f", 5), ["f"]);
        assert_eq!(names.bind("f", 7), ["f@7"]);
        assert_eq!(names.bind("f", 9), ["f@9-1"]);
        // The name FCS generated is taken, under `f`'s count.
        assert_eq!(names.bind("f@7", 11), ["f@11-2"]);
    }

    #[test]
    fn a_member_name_is_taken() {
        let mut names = LetNames::default();
        names.take("Q");
        assert_eq!(names.bind("Q", 3), ["Q@3"]);
    }

    #[test]
    fn a_possible_name_gives_both_readings_and_widens_the_count() {
        let mut names = LetNames::default();
        names.possibly_take("g");
        assert_eq!(names.bind("g", 4), ["g", "g@4"]);
        assert_eq!(names.bind("g", 6), ["g@6", "g@6-1"]);
    }

    #[test]
    fn an_absent_binder_takes_nothing_for_certain() {
        let mut names = LetNames::default();
        assert_eq!(names.possibly_bind("X", 2), ["X"]);
        assert_eq!(names.bind("X", 4), ["X", "X@4"]);
    }

    #[test]
    fn an_unknown_binder_widens_every_count() {
        let mut names = LetNames::default();
        names.bind_unknown();
        assert_eq!(names.bind("h", 3), ["h", "h@3", "h@3-1"]);
    }

    #[test]
    fn the_basic_name_stops_at_the_first_at_sign_after_the_first_character() {
        assert_eq!(basic_name("a@b@c"), "a");
        assert_eq!(basic_name("@a"), "@a");
        assert_eq!(basic_name("plain"), "plain");
    }
}
