//! The signature screen of one `open`'s folded names
//! (`docs/fsi-signature-restriction-plan.md` Stage 1), with what depends on
//! the opened path alone computed once per open.
//!
//! An open folds hundreds of names, and every top-level block's implicit open
//! of its own namespace folds them again. Each name's screen asks every
//! signature screen the same questions of the opened path. Those answers do
//! not depend on the name, so [`ProjectItems::open_name_screen`] takes them
//! once, and [`OpenNameScreen::screens`] asks each name only what depends on
//! it: a few lookups per signature screen, with nothing allocated.

use crate::hash::{HashMap, HashSet};

use super::model::ProjectItems;

/// The signature screen of every name one open of a path folds
/// ([`ProjectItems::open_name_screen`]).
pub(super) struct OpenNameScreen<'a> {
    screens: Vec<ScreenAtPath<'a>>,
    /// For each name, the latest materialisation rank of a published
    /// signature screen whose exact value exports include the opened path
    /// extended by that name.
    published_exempt: HashMap<&'a str, usize>,
}

/// One signature screen, as it bears on one opened path.
struct ScreenAtPath<'a> {
    /// The screen's over-approximated name set.
    names: &'a HashSet<String>,
    /// The screen's materialisation rank.
    rank: usize,
    /// Whether the screen withholds every name the open folds: the opened
    /// path is under one of its roots with a segment past the root in its
    /// name set, or under a namespace-direct case it exposes.
    every_name: bool,
    /// Whether the screen withholds a folded name that its name set holds:
    /// the opened path is at or under one of its roots, or one of its roots
    /// is strictly under the opened path.
    by_name: bool,
    /// The names whose extension of the opened path the screen exports
    /// exactly: its own exemption.
    exempt: HashSet<&'a str>,
    /// The names of the namespace-direct cases the screen exposes directly
    /// under the opened path.
    case_names: HashSet<&'a str>,
}

impl ProjectItems {
    /// The signature screen of one open of `opened`: for each bare name the
    /// open folds, whether a signature may expose `opened` extended by it.
    ///
    /// [`OpenNameScreen::screens`] answers as
    /// [`ProjectItems::sig_screened_open_name`] does, which states the rule.
    pub(super) fn open_name_screen(&self, opened: &[String]) -> OpenNameScreen<'_> {
        let now = self.item_file_bases.len();
        let child_of_opened =
            |path: &[String]| path.len() == opened.len() + 1 && path.starts_with(opened);
        let mut published_exempt: HashMap<&str, usize> = HashMap::default();
        let screens = self
            .sig_screens
            .iter()
            .map(|(screen, rank)| {
                let exempt: HashSet<&str> = screen
                    .exported_value_paths
                    .iter()
                    .filter(|path| child_of_opened(path))
                    .filter_map(|path| path.last().map(String::as_str))
                    .collect();
                if *rank < now {
                    for &name in &exempt {
                        let latest = published_exempt.entry(name).or_insert(*rank);
                        *latest = (*latest).max(*rank);
                    }
                }
                let mut every_name = false;
                let mut by_name = false;
                for root in &screen.roots {
                    if opened.starts_with(&root.path) {
                        by_name = true;
                        every_name |= opened[root.path.len()..]
                            .iter()
                            .any(|segment| screen.names.contains(segment));
                    } else if root.path.len() > opened.len() && root.path.starts_with(opened) {
                        by_name = true;
                    }
                }
                let mut case_names = HashSet::default();
                for path in &screen.value_paths {
                    if opened.starts_with(path) {
                        every_name = true;
                    } else if child_of_opened(path) {
                        case_names.extend(path.last().map(String::as_str));
                    }
                }
                ScreenAtPath {
                    names: &screen.names,
                    rank: *rank,
                    every_name,
                    by_name,
                    exempt,
                    case_names,
                }
            })
            .collect();
        OpenNameScreen {
            screens,
            published_exempt,
        }
    }
}

impl OpenNameScreen<'_> {
    /// Whether the bare name `name`, folded by this open, is screened: some
    /// signature may expose it, so an assembly entry for it must defer.
    pub(super) fn screens(&self, name: &str) -> bool {
        let published = self.published_exempt.get(name).copied();
        self.screens.iter().any(|screen| {
            !screen.exempt.contains(name)
                && !published.is_some_and(|latest| latest >= screen.rank)
                && (screen.every_name
                    || (screen.by_name && screen.names.contains(name))
                    || screen.case_names.contains(name))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::model::{SigRoot, SigScreen};
    use super::*;
    use proptest::prelude::*;
    use std::sync::Arc;

    /// A segment from an alphabet small enough that generated paths share
    /// prefixes, and names collide with segments, often.
    fn segment() -> impl Strategy<Value = String> {
        prop::sample::select(vec!["a", "b", "c"]).prop_map(str::to_string)
    }

    fn path(max: usize) -> impl Strategy<Value = Vec<String>> {
        prop::collection::vec(segment(), 0..=max)
    }

    fn paths() -> impl Strategy<Value = Vec<Vec<String>>> {
        prop::collection::vec(path(3), 0..4)
    }

    fn screen() -> impl Strategy<Value = (SigScreen, usize)> {
        (
            prop::collection::vec(path(3), 0..3),
            prop::collection::hash_set(segment(), 0..3),
            paths(),
            paths(),
            0usize..4,
        )
            .prop_map(|(roots, names, value_paths, exported, rank)| {
                let screen = SigScreen {
                    roots: roots
                        .into_iter()
                        .map(|path| SigRoot {
                            path,
                            auto_open: false,
                            implicit: false,
                        })
                        .collect(),
                    names: names.into_iter().collect(),
                    auto_open_nested: Vec::new(),
                    auto_open_type_containers: Vec::new(),
                    value_paths,
                    exported_value_paths: exported.into_iter().collect(),
                    exported_case_paths: HashSet::default(),
                    namespaces: HashSet::default(),
                    namespace_slot_type_names: Vec::new(),
                    namespace_unexported_names: Vec::new(),
                    attribute_spellings: HashSet::default(),
                };
                (screen, rank)
            })
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2000))]

        /// The per-open screen answers every name as the per-name rule
        /// does, over generated signature screens, materialisation ranks
        /// either side of the folded file count, and opened paths that sit
        /// at, under, over and beside the screens' roots and case paths.
        #[test]
        fn the_per_open_screen_answers_as_the_per_name_rule(
            screens in prop::collection::vec(screen(), 0..4),
            folded in 0usize..4,
            opened in path(3),
        ) {
            let items = ProjectItems {
                sig_screens: screens
                    .into_iter()
                    .map(|(screen, rank)| (Arc::new(screen), rank))
                    .collect(),
                item_file_bases: vec![0; folded],
                ..ProjectItems::default()
            };
            let per_open = items.open_name_screen(&opened);
            for name in ["a", "b", "c"] {
                prop_assert_eq!(
                    per_open.screens(name),
                    items.sig_screened_open_name(&opened, name),
                    "{:?} folding {:?} under {:#?}",
                    opened,
                    name,
                    items.sig_screens
                );
            }
        }
    }
}
