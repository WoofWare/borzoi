//! The census: which hostile dimensions reached a harness's subject.
//!
//! Drawing a hostile value proves nothing. A fixture builder may refuse it, a
//! place may not carry it, a pre-check may drop the case, and the test then
//! passes having checked nothing. So a harness records each drawn value at
//! the point its subject has been run on it ([`Census::reached`]), with what
//! the subject did, and [`Census::finish`] fails unless every dimension the
//! harness declared was reached.
//!
//! A dimension may be left unreached for two reasons only, both stated:
//!
//! - the harness **excludes** it, with the reason no value of the family can
//!   reach this subject (a place that carries text draws no name that is not
//!   UTF-8). An excluded dimension that is reached after all fails too: the
//!   exclusion has gone stale.
//! - the **platform** could not make any value of it on this run
//!   ([`Census::unmakeable`]), which is printed.
//!
//! What each census answers for is pinned as an exact manifest, one keyed
//! line per dimension: `owed`, or `excluded` with the reason. A reviewer sees
//! a dimension gained by the library, or excluded by the harness, as a line
//! of the diff. The manifest does not record what a run saw (whether a
//! platform could make a value, what the subject did with it): that differs
//! between platforms, where the manifest must not, and is what every run
//! checks and prints.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Mutex;

use super::{Dimension, Kind};
use crate::manifest::{self, Manifest};

/// What one census of a harness covers: its harness, its name and the kinds
/// it draws. The coverage table ([`super::coverage::BOUNDARIES`]) is where
/// one is declared.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declared {
    /// The harness's source file, relative to the workspace.
    pub harness: String,
    /// The census's name: unique within its crate, and the stem of its
    /// manifest.
    pub census: String,
    /// The kinds drawn.
    pub kinds: BTreeSet<Kind>,
}

#[derive(Debug, Default)]
struct Counts {
    /// What the subject did with values of each dimension, counted.
    reached: BTreeMap<Dimension, BTreeMap<String, usize>>,
    /// What the subject did with the harness's own values.
    plain: BTreeMap<String, usize>,
    /// Why the platform makes no value at all, per dimension.
    unmakeable: BTreeMap<Dimension, BTreeSet<String>>,
    /// The refusals of single values, which excuse nothing.
    refused: BTreeSet<String>,
}

/// One census. Shared by reference between the threads of a harness.
#[derive(Debug)]
pub struct Census {
    declared: Declared,
    excluded: BTreeMap<Dimension, &'static str>,
    counts: Mutex<Counts>,
    /// Whether dropping the census unfinished is a failure: so for one a
    /// harness opened ([`super::coverage::open`]).
    must_finish: bool,
}

impl Drop for Census {
    fn drop(&mut self) {
        // A census that is opened and never finished has checked nothing,
        // and its pinned manifest would go on saying otherwise.
        if self.must_finish && !std::thread::panicking() {
            panic!(
                "hostile census {} was opened and dropped without `finish`: nothing it recorded \
                 was checked",
                self.declared.census
            );
        }
    }
}

/// The manifest key under which the harness's own values are counted.
const PLAIN_KEY: &str = "plain";

impl Census {
    /// A census of `declared`, excluding `excluded` (each with the reason no
    /// value of the dimension can reach this subject).
    ///
    /// # Panics
    ///
    /// If an excluded dimension is of a kind the census does not draw, is
    /// excluded twice, or has an empty reason.
    pub(super) fn new(declared: Declared, excluded: &[(Dimension, &'static str)]) -> Self {
        let mut map = BTreeMap::new();
        for (dimension, reason) in excluded {
            assert!(
                declared.kinds.contains(&dimension.kind()),
                "census {}: {dimension} is excluded, and the census draws no {}",
                declared.census,
                dimension.kind()
            );
            assert!(
                !reason.trim().is_empty(),
                "census {}: {dimension} is excluded without a reason",
                declared.census
            );
            assert!(
                map.insert(*dimension, *reason).is_none(),
                "census {}: {dimension} is excluded twice",
                declared.census
            );
        }
        Census {
            declared,
            excluded: map,
            counts: Mutex::default(),
            must_finish: false,
        }
    }

    /// The census, which must now be finished: dropping it otherwise panics.
    pub(super) fn owing_a_finish(mut self) -> Self {
        self.must_finish = true;
        self
    }

    /// Every dimension the census owes: those of its kinds, less the
    /// excluded.
    pub fn owed(&self) -> BTreeSet<Dimension> {
        self.declared
            .kinds
            .iter()
            .flat_map(|k| k.dimensions())
            .filter(|d| !self.excluded.contains_key(d))
            .collect()
    }

    fn counts(&self) -> std::sync::MutexGuard<'_, Counts> {
        // A panic elsewhere in the harness must not hide this census's own
        // report behind a poisoned lock.
        self.counts.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// Record that the subject ran on a value of these dimensions, and what
    /// it did (`commit`, `decline`, `refuse`: the harness's own words, which
    /// the report counts). A value of no hostile dimension counts as the
    /// harness's own.
    ///
    /// Call this after the subject has run, never where the value is drawn.
    pub fn reached(&self, hostile: &BTreeSet<Dimension>, outcome: &str) {
        let mut counts = self.counts();
        if hostile.is_empty() {
            *counts.plain.entry(outcome.to_owned()).or_default() += 1;
        }
        for dimension in hostile {
            *counts
                .reached
                .entry(*dimension)
                .or_default()
                .entry(outcome.to_owned())
                .or_default() += 1;
        }
    }

    /// Record what the platform could not make, and print it (once per
    /// distinct refusal).
    ///
    /// Only a refusal that shows the platform makes *no* value of a
    /// dimension excuses the dimension
    /// ([`Unmakeable::excuses`](super::fs::Unmakeable::excuses)). A refusal
    /// of one value (a name holding a NUL) excuses nothing: the dimension's
    /// other values must still reach the subject.
    pub fn unmakeable(&self, refusal: &super::fs::Unmakeable) {
        let text = refusal.to_string();
        let fresh = match refusal.excuses() {
            Some(dimension) => self
                .counts()
                .unmakeable
                .entry(dimension)
                .or_default()
                .insert(text.clone()),
            None => self.counts().refused.insert(text.clone()),
        };
        if fresh {
            eprintln!("hostile census {}: {text}", self.declared.census);
        }
    }

    /// The census as text: each dimension, what met it, and how often.
    pub fn report(&self) -> String {
        let counts = self.counts();
        let tally = |outcomes: &BTreeMap<String, usize>| {
            outcomes
                .iter()
                .map(|(outcome, n)| format!("{outcome} {n}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let mut out = format!("hostile census {}:\n", self.declared.census);
        out.push_str(&format!("  {PLAIN_KEY}: {}\n", tally(&counts.plain)));
        let mut all: BTreeSet<Dimension> = self.owed();
        all.extend(self.excluded.keys());
        all.extend(counts.reached.keys());
        for dimension in all {
            let line = if let Some(outcomes) = counts.reached.get(&dimension) {
                tally(outcomes)
            } else if let Some(reason) = self.excluded.get(&dimension) {
                format!("excluded: {reason}")
            } else if let Some(reasons) = counts.unmakeable.get(&dimension) {
                format!(
                    "not made here: {}",
                    reasons.iter().cloned().collect::<Vec<_>>().join("; ")
                )
            } else {
                "NEVER REACHED".to_owned()
            };
            out.push_str(&format!("  {dimension}: {line}\n"));
        }
        out
    }

    /// What is wrong with the census, if anything: a dimension owed and
    /// never reached, one excluded and reached, or one reached that the
    /// census never declared.
    pub fn violations(&self) -> Vec<String> {
        let counts = self.counts();
        let mut out = Vec::new();
        if counts.plain.is_empty() {
            out.push(
                "no value of the harness's own reached the subject: with nothing plain to \
                 compare, a subject that mishandles everything looks the same"
                    .to_owned(),
            );
        }
        for dimension in self.owed() {
            if !counts.reached.contains_key(&dimension)
                && !counts.unmakeable.contains_key(&dimension)
            {
                out.push(format!(
                    "{dimension} is declared and no value of it reached the subject \
                     ({}). Reach it, or exclude it with the reason it cannot be reached.",
                    dimension.why()
                ));
            }
        }
        for dimension in counts.reached.keys() {
            if let Some(reason) = self.excluded.get(dimension) {
                out.push(format!(
                    "{dimension} is excluded (\"{reason}\") and a value of it reached the \
                     subject: remove the exclusion."
                ));
            } else if !self.declared.kinds.contains(&dimension.kind()) {
                out.push(format!(
                    "{dimension} reached the subject and the census declares no {}: declare \
                     the kind in the coverage table.",
                    dimension.kind()
                ));
            }
        }
        out
    }

    /// The census's manifest: one line per dimension, `owed` or `excluded`
    /// with the reason. It says what the census answers for, not what one
    /// run on one platform saw, so every platform pins the same lines;
    /// [`Self::violations`] is what holds a run to it.
    fn manifest(&self) -> Manifest {
        let mut entries = vec![format!("{PLAIN_KEY}\towed")];
        let mut all: BTreeSet<Dimension> = self.owed();
        all.extend(self.excluded.keys());
        for dimension in all {
            let value = match self.excluded.get(&dimension) {
                Some(reason) => format!("excluded: {reason}"),
                None => "owed".to_owned(),
            };
            entries.push(format!("{}\t{value}", dimension.key()));
        }
        Manifest::from_entries(entries).expect("dimension keys are distinct single lines")
    }

    /// End the census: print it, fail on any violation, and compare what
    /// became of each dimension with the census's pinned manifest
    /// ([`super::coverage::manifest_path`]). `regenerate` is the command
    /// that rewrites it.
    ///
    /// # Panics
    ///
    /// On a violation ([`Self::violations`]), whether or not manifests are
    /// being regenerated, and on any difference from the manifest.
    #[track_caller]
    pub fn finish(self, regenerate: &str) {
        let path = super::coverage::manifest_path(&super::coverage::workspace(), &self.declared);
        self.finish_at(&path, regenerate);
    }

    /// [`Self::finish`] against the manifest at `path`.
    #[track_caller]
    fn finish_at(mut self, path: &Path, regenerate: &str) {
        self.must_finish = false;
        eprint!("{}", self.report());
        let violations = self.violations();
        assert!(
            violations.is_empty(),
            "hostile census {}:\n  {}",
            self.declared.census,
            violations.join("\n  ")
        );
        manifest::check(path, &self.manifest(), regenerate);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn declared(kinds: &[Kind]) -> Declared {
        Declared {
            harness: "crates/demo/tests/x.rs".into(),
            census: "test".into(),
            kinds: kinds.iter().copied().collect(),
        }
    }

    fn reach_all(census: &Census, except: &[Dimension]) {
        census.reached(&BTreeSet::new(), "commit");
        for dimension in census.owed() {
            if !except.contains(&dimension) {
                census.reached(&BTreeSet::from([dimension]), "decline");
            }
        }
    }

    #[test]
    fn a_census_that_reached_everything_has_no_violation() {
        let census = Census::new(declared(&[Kind::FsChange, Kind::WorkingDirectory]), &[]);
        reach_all(&census, &[]);
        assert_eq!(census.violations(), Vec::<String>::new());
        let manifest = census.manifest();
        assert_eq!(
            manifest.entries().len(),
            1 + Kind::FsChange.dimensions().count() + Kind::WorkingDirectory.dimensions().count()
        );
        assert!(manifest.entries().iter().all(|e| e.ends_with("\towed")));
    }

    #[test]
    fn a_declared_dimension_never_reached_is_a_violation() {
        let census = Census::new(declared(&[Kind::FsChange]), &[]);
        reach_all(&census, &[Dimension::Appears]);
        let violations = census.violations();
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(violations[0].starts_with("change.appears is declared and no value"));
        assert!(census.report().contains("change.appears: NEVER REACHED"));
    }

    #[test]
    fn a_census_with_no_plain_value_is_a_violation() {
        let census = Census::new(declared(&[Kind::FsChange]), &[]);
        for dimension in census.owed() {
            census.reached(&BTreeSet::from([dimension]), "decline");
        }
        assert!(census.violations()[0].starts_with("no value of the harness's own"));
    }

    #[test]
    fn an_excluded_dimension_is_not_owed_and_must_stay_unreached() {
        let excluded = [(Dimension::Appears, "the subject is handed one snapshot")];
        let census = Census::new(declared(&[Kind::FsChange]), &excluded);
        reach_all(&census, &[]);
        assert_eq!(census.violations(), Vec::<String>::new());
        assert!(
            census.manifest().entries().contains(
                &"change.appears\texcluded: the subject is handed one snapshot".to_owned()
            )
        );
        census.reached(&BTreeSet::from([Dimension::Appears]), "commit");
        assert!(census.violations()[0].contains("remove the exclusion"));
    }

    #[test]
    fn a_dimension_of_an_undeclared_kind_is_a_violation() {
        let census = Census::new(declared(&[Kind::FsChange]), &[]);
        reach_all(&census, &[]);
        census.reached(&BTreeSet::from([Dimension::Fifo]), "decline");
        assert!(census.violations()[0].contains("declares no fs"));
    }

    #[test]
    fn a_dimension_the_platform_cannot_make_is_excused_and_pinned_alike() {
        let census = Census::new(declared(&[Kind::FsState]), &[]);
        reach_all(&census, &[Dimension::Socket]);
        let refusal = crate::hostile::fs::Unmakeable::State {
            state: crate::hostile::fs::State::Socket,
            reason: "no such thing here".into(),
            whole: true,
        };
        census.unmakeable(&refusal);
        assert_eq!(census.violations(), Vec::<String>::new());
        assert!(census.report().contains("fs.socket: not made here"));
        // The manifest is the one a platform that makes sockets pins.
        let elsewhere = Census::new(declared(&[Kind::FsState]), &[]);
        reach_all(&elsewhere, &[]);
        assert_eq!(census.manifest(), elsewhere.manifest());
    }

    /// A refusal of one value excuses nothing: the rest of its dimension is
    /// still owed.
    #[test]
    fn a_refusal_of_one_value_does_not_excuse_its_dimension() {
        use crate::hostile::fs::{NameRefusal, State, Unmakeable};
        let census = Census::new(declared(&[Kind::FileName, Kind::FsState]), &[]);
        reach_all(
            &census,
            &[Dimension::DotName, Dimension::NonUtf8, Dimension::Socket],
        );
        census.unmakeable(&Unmakeable::Name {
            why: NameRefusal::NotAComponent(crate::hostile::name::NotAComponent::Dots),
        });
        census.unmakeable(&Unmakeable::Name {
            why: NameRefusal::NotUtf8,
        });
        census.unmakeable(&Unmakeable::State {
            state: State::Socket,
            reason: "the path is too long".into(),
            whole: false,
        });
        let violations = census.violations();
        assert_eq!(violations.len(), 2, "{violations:?}");
        assert!(violations[0].starts_with("name.dot-name is declared"));
        assert!(violations[1].starts_with("fs.socket is declared"));
    }

    #[test]
    fn a_census_owing_a_finish_panics_if_dropped_unfinished() {
        let dropped = std::panic::catch_unwind(|| {
            let _guard = crate::panic_silence::silence_panics_here();
            let census = Census::new(declared(&[Kind::FsChange]), &[]).owing_a_finish();
            reach_all(&census, &[]);
        });
        let message = dropped.unwrap_err();
        let message = message.downcast_ref::<String>().expect("a formatted panic");
        assert!(message.contains("dropped without `finish`"), "{message}");
        // Finished, it is quiet.
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("census.txt");
        let first = Census::new(declared(&[Kind::FsChange]), &[]);
        reach_all(&first, &[]);
        manifest::compare_with(&path, &first.manifest(), "regen", true).unwrap();
        let census = Census::new(declared(&[Kind::FsChange]), &[]).owing_a_finish();
        reach_all(&census, &[]);
        census.finish_at(&path, "regen");
    }

    #[test]
    fn finishing_pins_the_manifest_and_fails_on_movement() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("census.txt");
        let run = |excluded: &[(Dimension, &'static str)]| {
            let census = Census::new(declared(&[Kind::FsChange]), excluded);
            reach_all(&census, &[]);
            manifest::compare_with(&path, &census.manifest(), "regen", false)
        };
        // Written once, as a regeneration does.
        let first = Census::new(declared(&[Kind::FsChange]), &[]);
        reach_all(&first, &[]);
        manifest::compare_with(&path, &first.manifest(), "regen", true).unwrap();
        assert_eq!(run(&[]), Ok(()));
        // Excluding a dimension moves its line.
        let moved = run(&[(Dimension::Appears, "why")]).unwrap_err();
        assert!(moved.contains("change.appears"), "{moved}");
        // The whole of `finish`, against the same file.
        let whole = Census::new(declared(&[Kind::FsChange]), &[]);
        reach_all(&whole, &[]);
        whole.finish_at(&path, "regen");
    }

    #[test]
    #[should_panic(expected = "the census draws no fs")]
    fn excluding_a_dimension_of_an_undeclared_kind_is_refused() {
        Census::new(declared(&[Kind::FsChange]), &[(Dimension::Fifo, "why")]);
    }

    #[test]
    #[should_panic(expected = "without a reason")]
    fn excluding_without_a_reason_is_refused() {
        Census::new(declared(&[Kind::FsChange]), &[(Dimension::Appears, " ")]);
    }
}
