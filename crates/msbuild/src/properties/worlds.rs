//! What a value is under each directory MSBuild may start in.
//!
//! On a Unix host MSBuild's path adjustment ([`super::path_fixup`]) rewrites
//! an expansion's `\` as `/` when the rewrite's first segment is a directory,
//! and a segment named relatively is probed under MSBuild's **startup
//! directory**: the working directory of the process that started the build.
//! That holds for the entry project and for every project it builds, in-proc or
//! on a worker node, so it is one directory for the whole build (probed against
//! `dotnet msbuild` 10.0 and 11.0 with `-m:1` and `-m:4`, and through `dotnet
//! build`). The exception is `-mt`, the multithreaded mode, which probes under
//! each project's own directory; borzoi models no build run that way.
//!
//! An evaluation the LSP serves models a build nobody launched, so it knows no
//! startup directory ([`Start::Unknown`]). Each relative segment is then a
//! free yes/no — is there a directory of this name where MSBuild started? —
//! and a value is a decision tree over those questions ([`Worlds`]). Most
//! values ask none and are one leaf. An evaluation of a process the caller
//! starts (the restore cone's) knows the directory ([`Start::Known`]) and asks
//! the file system, through the observer, so the read set covers the answer.
//!
//! [`in_every_world`] runs a computation once per assignment it turns out to
//! need: a run that asks about an unassigned segment is repeated with the
//! segment present and absent, and the two results are joined into a
//! [`Worlds::Split`] unless they agree. Asking about more than
//! [`MAX_SEGMENTS`] segments along one path stops the enumeration
//! ([`TooManySegments`]), and the caller declines.

use std::cell::RefCell;
use std::path::Path;
use std::sync::Arc;

use crate::dotnet_io;
use crate::observed::Observer;

/// How many distinct relative segments one computation may ask about along a
/// path of its decision tree before it declines: at most `2^MAX_SEGMENTS`
/// worlds.
///
/// Chosen from the measurement on the pinned corpora (fsharp-src and the
/// project corpus, every `.fsproj` through the SDK chain): no expansion asks
/// about more than three segments along a path (`DefaultItemExcludes` reaches
/// it, through `bin`, `obj` and the `;bin` or `;.` its whole value starts
/// with). Twice that leaves room for a project that
/// composes the SDK's paths further. Each run that meets an unassigned segment
/// is repeated both ways, so the worst case is `2^(MAX_SEGMENTS + 1) - 1` (127)
/// runs.
pub(crate) const MAX_SEGMENTS: usize = 6;

/// A value under each assignment of the relative segments it depends on.
///
/// `Same` is the value under every startup directory. A `Split` asks one
/// segment and holds the value where a directory of that name exists under
/// the startup directory (`present`) and where none does (`absent`).
/// Built only through `Worlds::branch`, which collapses a split whose two
/// sides agree, so a value equal under every assignment is always `Same`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Worlds<T> {
    /// The value whatever MSBuild's startup directory holds.
    Same(T),
    /// The value turns on one relative segment.
    Split(Box<Split<T>>),
}

/// One question of a [`Worlds`] tree and its two answers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Split<T> {
    segment: Arc<str>,
    present: Worlds<T>,
    absent: Worlds<T>,
}

impl<T> Split<T> {
    /// The relative segment asked: a directory of this name under MSBuild's
    /// startup directory, or not.
    pub fn segment(&self) -> &str {
        &self.segment
    }

    /// The value where the directory exists.
    pub fn present(&self) -> &Worlds<T> {
        &self.present
    }

    /// The value where it does not.
    pub fn absent(&self) -> &Worlds<T> {
        &self.absent
    }
}

impl<T: PartialEq> Worlds<T> {
    /// The tree asking `segment`, or the one side when both agree.
    pub(crate) fn branch(segment: Arc<str>, present: Worlds<T>, absent: Worlds<T>) -> Self {
        if present == absent {
            present
        } else {
            Worlds::Split(Box::new(Split {
                segment,
                present,
                absent,
            }))
        }
    }

    /// Whether the value turns on at least one segment.
    pub fn is_split(&self) -> bool {
        matches!(self, Worlds::Split(_))
    }

    /// The value, when it is the same under every startup directory.
    pub fn agreed(&self) -> Option<&T> {
        match self {
            Worlds::Same(value) => Some(value),
            Worlds::Split(_) => None,
        }
    }

    /// Each value taken through `f`, joined again: a consumer that reads only
    /// part of a value (a file name, a full path) collapses the worlds whose
    /// parts agree, and then [`Self::agreed`] answers.
    pub fn map<U: PartialEq>(&self, f: &mut impl FnMut(&T) -> U) -> Worlds<U> {
        match self {
            Worlds::Same(value) => Worlds::Same(f(value)),
            Worlds::Split(split) => {
                let present = split.present.map(f);
                let absent = split.absent.map(f);
                Worlds::branch(split.segment.clone(), present, absent)
            }
        }
    }

    /// Every value the tree holds, present side first.
    pub fn values(&self) -> Vec<&T> {
        let mut out = Vec::new();
        self.collect_values(&mut out);
        out
    }

    fn collect_values<'a>(&'a self, out: &mut Vec<&'a T>) {
        match self {
            Worlds::Same(value) => out.push(value),
            Worlds::Split(split) => {
                split.present.collect_values(out);
                split.absent.collect_values(out);
            }
        }
    }

    /// The value where no segment the tree asks about is a directory under
    /// the startup directory. It stands for the tree only where a reader is
    /// blind to trust by contract (`ParsedProject::properties`), or has
    /// checked that every value agrees on what it reads.
    pub(crate) fn absent_everywhere(&self) -> &T {
        match self {
            Worlds::Same(value) => value,
            Worlds::Split(split) => split.absent.absent_everywhere(),
        }
    }
}

/// What the evaluation knows about MSBuild's startup directory.
#[derive(Clone, Copy)]
pub(crate) enum Start<'a> {
    /// Nothing: the evaluation the LSP serves. Each relative probe is a free
    /// segment of a [`Worlds`] tree.
    Unknown,
    /// The directory a process the caller starts runs in (the restore cone's
    /// `dotnet` child), asked through `observer`, which records the read.
    Known {
        dir: &'a Path,
        observer: &'a Observer,
    },
}

/// One assignment of segments, as one run of an [`in_every_world`]
/// computation sees it.
pub(crate) struct World<'a> {
    start: Start<'a>,
    /// The segments this run's path has fixed, and their answers.
    assigned: Vec<(Arc<str>, bool)>,
    /// The first segment this run asked about and found unassigned. The run
    /// went on as though it were absent; its result is discarded, and the
    /// computation is run again with the segment fixed each way.
    unassigned: RefCell<Option<Arc<str>>>,
}

impl<'a> World<'a> {
    /// Whether `segment` is a directory under MSBuild's startup directory in
    /// this world.
    pub(crate) fn present(&self, segment: &str) -> bool {
        if let Start::Known { dir, observer } = self.start {
            return dotnet_io::directory_exists(observer, &dir.join(segment));
        }
        if let Some((_, present)) = self.assigned.iter().find(|(s, _)| &**s == segment) {
            return *present;
        }
        let mut unassigned = self.unassigned.borrow_mut();
        if unassigned.is_none() {
            *unassigned = Some(segment.into());
        }
        false
    }

    /// The value `worlds` holds in this world.
    pub(crate) fn read<'t, T>(&self, worlds: &'t Worlds<T>) -> &'t T {
        match worlds {
            Worlds::Same(value) => value,
            Worlds::Split(split) => {
                if self.present(&split.segment) {
                    self.read(&split.present)
                } else {
                    self.read(&split.absent)
                }
            }
        }
    }
}

impl World<'static> {
    /// The one world in which no relative segment is a directory under the
    /// startup directory: what a computation that could not be enumerated
    /// ([`TooManySegments`]) reports, beside the issue that says so.
    pub(crate) fn absent_everywhere() -> Self {
        World {
            start: Start::Unknown,
            assigned: Vec::new(),
            unassigned: RefCell::new(None),
        }
    }
}

/// A computation asked about more than [`MAX_SEGMENTS`] segments along one
/// path, so it was not enumerated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TooManySegments;

/// `compute`'s result under every assignment of the relative segments it asks
/// about, from `start`.
pub(crate) fn in_every_world<T: PartialEq>(
    start: Start<'_>,
    mut compute: impl FnMut(&World<'_>) -> T,
) -> Result<Worlds<T>, TooManySegments> {
    enumerate(start, Vec::new(), &mut compute)
}

fn enumerate<T: PartialEq>(
    start: Start<'_>,
    assigned: Vec<(Arc<str>, bool)>,
    compute: &mut impl FnMut(&World<'_>) -> T,
) -> Result<Worlds<T>, TooManySegments> {
    let world = World {
        start,
        assigned,
        unassigned: RefCell::new(None),
    };
    let value = compute(&world);
    let World {
        assigned,
        unassigned,
        ..
    } = world;
    let Some(segment) = unassigned.into_inner() else {
        return Ok(Worlds::Same(value));
    };
    if assigned.len() >= MAX_SEGMENTS {
        return Err(TooManySegments);
    }
    let with = |present: bool| {
        let mut assigned = assigned.clone();
        assigned.push((segment.clone(), present));
        assigned
    };
    let present = enumerate(start, with(true), compute)?;
    let absent = enumerate(start, with(false), compute)?;
    Ok(Worlds::branch(segment, present, absent))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A computation over `segments`: the list of those present.
    fn presence(world: &World<'_>, segments: &[&str]) -> Vec<String> {
        segments
            .iter()
            .filter(|s| world.present(s))
            .map(|s| (*s).to_owned())
            .collect()
    }

    #[test]
    fn a_computation_asking_nothing_is_one_world() {
        let worlds = in_every_world(Start::Unknown, |_| 7).unwrap();
        assert_eq!(worlds, Worlds::Same(7));
    }

    #[test]
    fn each_segment_asked_doubles_the_worlds() {
        let worlds = in_every_world(Start::Unknown, |w| presence(w, &["a", "b"])).unwrap();
        let mut values: Vec<Vec<String>> = worlds.values().into_iter().cloned().collect();
        values.sort();
        assert_eq!(
            values,
            [
                vec![],
                vec!["a".to_owned()],
                vec!["a".into(), "b".into()],
                vec!["b".into()]
            ]
        );
        assert_eq!(worlds.absent_everywhere(), &Vec::<String>::new());
    }

    #[test]
    fn worlds_that_agree_collapse() {
        let worlds =
            in_every_world(Start::Unknown, |w| presence(w, &["a", "b"]).len() < 3).unwrap();
        assert_eq!(worlds, Worlds::Same(true));
        let split = in_every_world(Start::Unknown, |w| presence(w, &["a"])).unwrap();
        assert_eq!(split.map(&mut |v| v.len() < 2), Worlds::Same(true));
    }

    /// The cap, pinned at its edge: a computation asking about
    /// [`MAX_SEGMENTS`] segments is enumerated, one asking one more is not.
    #[test]
    fn the_segment_cap_is_exact() {
        let names: Vec<String> = (0..=MAX_SEGMENTS).map(|i| format!("s{i}")).collect();
        let refs: Vec<&str> = names.iter().map(String::as_str).collect();
        let at_cap = in_every_world(Start::Unknown, |w| presence(w, &refs[..MAX_SEGMENTS]));
        assert_eq!(at_cap.unwrap().values().len(), 1 << MAX_SEGMENTS);
        let over = in_every_world(Start::Unknown, |w| presence(w, &refs));
        assert_eq!(over, Err(TooManySegments));
    }

    #[test]
    fn a_known_start_asks_the_file_system() {
        let tmp = tempfile::TempDir::new().unwrap();
        std::fs::create_dir(tmp.path().join("obj")).unwrap();
        let observer = Observer::new();
        let start = Start::Known {
            dir: tmp.path(),
            observer: &observer,
        };
        let worlds = in_every_world(start, |w| presence(w, &["obj", "bin"])).unwrap();
        assert_eq!(worlds, Worlds::Same(vec!["obj".to_owned()]));
    }
}
