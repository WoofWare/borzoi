//! Whether the assembly being checked is a **friend** of a referenced one:
//! named by one of its `[<assembly: InternalsVisibleTo>]` attributes, so that
//! FCS adds the referenced assembly's internal entities to the name
//! environment as it adds its public ones (`AddNonLocalCcu`,
//! `src/Compiler/Checking/CheckDeclarations.fs:325`; for an IL type,
//! `IsTyconAccessibleViaVisibleTo`,
//! `src/Compiler/Checking/AccessibilityLogic.fs:124`).
//!
//! Name resolution reads an assembly through its public view, so the view is
//! the consumer's only when the consumer is provably not a friend
//! ([`Friendship::No`]). The env grades every other assembly's non-public
//! surface as unread ([`super::AssemblyEnv::public_view_incomplete`]).

use borzoi_assembly::{FriendDeclarations, FriendEntry};

/// The simple name of the assembly being checked, as FCS takes it: the name
/// of the output file (`-o:`, MSBuild's `@(IntermediateAssembly)`, so
/// `$(TargetName)$(TargetExt)` by default) up to its last dot
/// (`TcConfigBuilder.DecideNames`, `src/Compiler/Driver/CompilerConfig.fs:942`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ConsumerName {
    /// The name, from trusted values.
    Known(String),
    /// The name is not known: any friend declaration may name it.
    Unknown,
}

impl ConsumerName {
    /// A name no [`FriendEntry::Named`] can equal (`<` is outside the
    /// certified spelling, [`borzoi_assembly::friends::certified_simple_name`]),
    /// for a harness's probe project, which its oracle names after a
    /// temporary file. Under it a declaration set is [`Friendship::No`]
    /// unless an entry is unread.
    pub const PROBE: &'static str = "<probe>";

    /// Whether FCS may give the consumer the name `name`, and how sure that
    /// is.
    fn may_be(&self, name: &str) -> Option<Certainty> {
        match self {
            // FCS compares with `=`: ordinal, case-sensitive.
            ConsumerName::Known(known) => (known == name).then_some(Certainty::Certain),
            ConsumerName::Unknown => Some(Certainty::Possible),
        }
    }
}

/// How sure [`ConsumerName::may_be`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Certainty {
    Certain,
    Possible,
}

/// Whether the assembly being checked sees a referenced assembly's internals.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Friendship {
    /// Some declaration names the consumer.
    Yes,
    /// No declaration names the consumer: the assembly's public view is all
    /// the consumer sees of it.
    No,
    /// Some declaration may name the consumer: its argument, or the
    /// consumer's own name, is unread.
    Unknown,
}

impl Friendship {
    /// The verdict `declarations` give `consumer`.
    ///
    /// [`FriendEntry::Named`] is certain in one direction only: its name is
    /// what FCS reads off the argument, or the argument names nobody. So a
    /// match is `Yes` up to an argument FCS rejects, which costs a decline,
    /// and a mismatch is a sound `No`.
    pub fn of(declarations: &FriendDeclarations, consumer: &ConsumerName) -> Friendship {
        let mut unread = false;
        for entry in &declarations.entries {
            match entry {
                FriendEntry::Named(name) => match consumer.may_be(name) {
                    Some(Certainty::Certain) => return Friendship::Yes,
                    Some(Certainty::Possible) => unread = true,
                    None => {}
                },
                FriendEntry::Unread(_) => unread = true,
            }
        }
        if unread {
            Friendship::Unknown
        } else {
            Friendship::No
        }
    }

    /// Whether the assembly's public view may be less than the consumer
    /// sees of it.
    pub fn may_see_internals(self) -> bool {
        self != Friendship::No
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn decls(entries: &[FriendEntry]) -> FriendDeclarations {
        FriendDeclarations {
            entries: entries.to_vec(),
        }
    }

    fn named(n: &str) -> FriendEntry {
        FriendEntry::Named(n.to_string())
    }

    fn unread() -> FriendEntry {
        FriendEntry::Unread("test".to_string())
    }

    /// The verdict over every declaration list of up to three entries drawn
    /// from {the consumer, another name, the consumer in another case,
    /// unread}, against a reference: `Yes` iff some entry names the consumer
    /// exactly; else `Unknown` iff some entry is unread, or names anyone at
    /// all while the consumer is unknown; else `No`.
    #[test]
    fn friendship_matches_its_reference_over_small_lists() {
        let pool = [named("B"), named("C"), named("b"), unread()];
        let mut lists: Vec<Vec<FriendEntry>> = vec![vec![]];
        for _ in 0..3 {
            let longer: Vec<Vec<FriendEntry>> = lists
                .iter()
                .flat_map(|l| {
                    pool.iter().map(move |e| {
                        let mut l = l.clone();
                        l.push(e.clone());
                        l
                    })
                })
                .collect();
            lists.extend(longer);
        }
        for list in &lists {
            for consumer in [ConsumerName::Known("B".to_string()), ConsumerName::Unknown] {
                let names_b = list.contains(&named("B"));
                let any_unread = list.contains(&unread());
                let expected = match &consumer {
                    ConsumerName::Known(_) if names_b => Friendship::Yes,
                    ConsumerName::Known(_) if any_unread => Friendship::Unknown,
                    ConsumerName::Known(_) => Friendship::No,
                    ConsumerName::Unknown if list.is_empty() => Friendship::No,
                    ConsumerName::Unknown => Friendship::Unknown,
                };
                assert_eq!(
                    Friendship::of(&decls(list), &consumer),
                    expected,
                    "{list:?} for {consumer:?}"
                );
            }
        }
    }
}
