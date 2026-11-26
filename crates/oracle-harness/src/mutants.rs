//! A mutation run's exact manifest: one line per mutant cargo-mutants graded,
//! keyed by the mutant and valued by its verdict.
//!
//! `tools/mutants/inner.sh` runs cargo-mutants over one set of
//! `tools/mutants/sets.tsv` inside the sandbox; the `mutants-manifest` binary
//! then reads its `outcomes.json` through [`parse_outcomes`], turns it into a
//! [`Manifest`] with [`manifest_items`], and checks it against
//! `tools/mutants/manifests/<set>.txt`.
//!
//! # Keys
//!
//! A key is cargo-mutants' name for the mutant with the line and column taken
//! out (`crates/nuget/src/range.rs: replace VersionRange::satisfies -> bool
//! with true`), so an edit elsewhere in the file moves no key. Two mutants that
//! still share a name — one operator deleted at two places in one function —
//! are told apart by a ` #<n>` suffix numbering them in source order, the
//! first unnumbered.
//!
//! # Verdicts
//!
//! `caught`, `missed`, `timeout` and `unviable` are cargo-mutants' own. A
//! missed mutant listed in `tools/mutants/equivalent.tsv` is
//! `equivalent: <reason>` instead: a mutation no test can observe, with the
//! argument for why. A row names its mutant by key *and* by site, a
//! fingerprint of the source lines the mutation replaces ([`site_of`]): a
//! key's ` #<n>` moves to another mutant when one with the same description
//! is added before it, and an edit to the code the argument covers may make
//! the mutation observable; neither may leave the row standing. A row whose
//! key has another site now, whose mutant this run did not miss, or that names
//! no mutant at all is stale and fails the run, printing the site the key has
//! now.
//!
//! # Scope
//!
//! What the run graded with is part of the manifest too: `scope: package`,
//! `scope: files` and one `scope: skip <filter>` entry per test filter the set
//! skips, valued by its reason. So a change to which tests face the set's
//! mutants moves the manifest even when no verdict moves.
//!
//! # Vacuity
//!
//! A run grades nothing when it lists no mutant, when the mutants it graded are
//! not exactly the ones it listed, or when it catches none: each is a failure,
//! never an empty or all-`missed` manifest.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use serde::Deserialize;

use crate::manifest::{EntryError, Manifest};

/// What the tests made of one mutant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Verdict {
    /// A test failed.
    Caught,
    /// Every test passed.
    Missed,
    /// The tests ran past cargo-mutants' timeout.
    Timeout,
    /// The mutant did not build.
    Unviable,
}

impl Verdict {
    /// The manifest's spelling.
    pub fn as_str(self) -> &'static str {
        match self {
            Verdict::Caught => "caught",
            Verdict::Missed => "missed",
            Verdict::Timeout => "timeout",
            Verdict::Unviable => "unviable",
        }
    }
}

/// One graded mutant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Graded {
    /// The file it mutates, relative to the workspace root.
    pub file: String,
    /// Where the mutation starts: line, then column, both 1-based.
    pub start: (u32, u32),
    /// The 1-based line the mutation ends on.
    pub end_line: u32,
    /// cargo-mutants' description of the mutation, without the file and
    /// position (`replace f -> bool with true`).
    pub description: String,
    /// The verdict.
    pub verdict: Verdict,
    /// The fingerprint of the lines the mutation replaces ([`site_of`]);
    /// `None` until the caller reads them. Shared, as mutants of one span
    /// have one site.
    pub site: Option<Arc<str>>,
}

/// What `outcomes.json` said, as [`parse_outcomes`] reads it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcomes {
    /// Whether the unmutated baseline passed. `None` when the run has no
    /// baseline outcome (`--baseline skip`).
    pub baseline_passed: Option<bool>,
    /// Every graded mutant, in the file's order.
    pub mutants: Vec<Graded>,
}

#[derive(Deserialize)]
struct RawOutcomes {
    outcomes: Vec<RawOutcome>,
}

#[derive(Deserialize)]
struct RawOutcome {
    scenario: RawScenario,
    summary: String,
}

#[derive(Deserialize)]
enum RawScenario {
    Baseline,
    Mutant(RawMutant),
}

#[derive(Deserialize)]
struct RawMutant {
    file: String,
    name: String,
    span: RawSpan,
}

#[derive(Deserialize)]
struct RawSpan {
    start: RawPosition,
    end: RawPosition,
}

#[derive(Deserialize)]
struct RawPosition {
    line: u32,
    column: u32,
}

/// Read cargo-mutants' `mutants.out/outcomes.json`.
pub fn parse_outcomes(json: &str) -> Result<Outcomes, String> {
    let raw: RawOutcomes = serde_json::from_str(json).map_err(|e| format!("outcomes.json: {e}"))?;
    let mut baseline_passed = None;
    let mut mutants = Vec::new();
    for o in raw.outcomes {
        match o.scenario {
            RawScenario::Baseline => {
                if baseline_passed.is_some() {
                    return Err("outcomes.json: two baseline outcomes".into());
                }
                baseline_passed = Some(o.summary == "Success");
            }
            RawScenario::Mutant(m) => {
                let verdict = match o.summary.as_str() {
                    "CaughtMutant" => Verdict::Caught,
                    "MissedMutant" => Verdict::Missed,
                    "Timeout" => Verdict::Timeout,
                    "Unviable" => Verdict::Unviable,
                    other => {
                        return Err(format!(
                            "outcomes.json: mutant {:?} has the summary {other:?}, which is no verdict",
                            m.name
                        ));
                    }
                };
                let start = (m.span.start.line, m.span.start.column);
                let prefix = format!("{}:{}:{}: ", m.file, start.0, start.1);
                let Some(description) = m.name.strip_prefix(&prefix) else {
                    return Err(format!(
                        "outcomes.json: mutant name {:?} does not start {prefix:?}",
                        m.name
                    ));
                };
                if m.span.end.line < start.0 {
                    return Err(format!(
                        "outcomes.json: mutant {:?} ends before it starts",
                        m.name
                    ));
                }
                mutants.push(Graded {
                    description: description.to_string(),
                    file: m.file,
                    start,
                    end_line: m.span.end.line,
                    verdict,
                    site: None,
                });
            }
        }
    }
    Ok(Outcomes {
        baseline_passed,
        mutants,
    })
}

/// The site of a mutation spanning 1-based lines `start..=end` of `source`:
/// `fnv1a64:` and the 64-bit FNV-1a hash of those lines' exact text, joined
/// by line feeds, in hex. Whole lines, every character kept, so any edit to
/// the code the mutation replaces moves the site. `None` when the span is not
/// within `source`.
pub fn site_of(source: &str, start: u32, end: u32) -> Option<String> {
    let first = usize::try_from(start).ok()?.checked_sub(1)?;
    let count = usize::try_from(end.checked_sub(start)?).ok()? + 1;
    let lines: Vec<&str> = source.lines().skip(first).take(count).collect();
    if lines.len() != count {
        return None;
    }
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in lines.join("\n").bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    Some(format!("fnv1a64:{hash:016x}"))
}

/// The files whose sites `set`'s equivalence rows need: the file part of each
/// row's key. A site matters only to a row, so no other file need be read.
pub fn equivalence_files<'a>(set: &str, equivalents: &'a [Equivalent]) -> BTreeSet<&'a str> {
    equivalents
        .iter()
        .filter(|e| e.set == set)
        .filter_map(|e| e.key.split_once(": ").map(|(file, _)| file))
        .collect()
}

/// Gives each mutant in one of `sources`' files (path to text) its site, made
/// once per span and shared; mutants in other files keep `None`.
pub fn attach_sites(mutants: &mut [Graded], sources: &BTreeMap<&str, String>) {
    let mut sites: BTreeMap<(String, u32, u32), Option<Arc<str>>> = BTreeMap::new();
    for m in mutants {
        let Some(text) = sources.get(m.file.as_str()) else {
            continue;
        };
        let site = sites
            .entry((m.file.clone(), m.start.0, m.end_line))
            .or_insert_with(|| site_of(text, m.start.0, m.end_line).map(Arc::from));
        m.site = site.clone();
    }
}

/// One row of `tools/mutants/equivalent.tsv`: a mutant of `set` that no test
/// can observe, and why.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Equivalent {
    /// The set the mutant belongs to.
    pub set: String,
    /// The mutant's manifest key.
    pub key: String,
    /// The mutant's site ([`site_of`]).
    pub site: String,
    /// The one-line argument that no test can tell the mutant from the
    /// original.
    pub reason: String,
}

/// The set names `tools/mutants/sets.tsv` declares: the second field of each
/// `set` record.
pub fn declared_sets(sets_tsv: &str) -> BTreeSet<String> {
    sets_tsv
        .lines()
        .filter_map(|l| l.strip_prefix("set\t"))
        .filter_map(|rest| rest.split('\t').next())
        .map(str::to_string)
        .collect()
}

/// A run's scope ([the module docs](self)) from its parts: the package, the
/// file globs as `sets.tsv` spells them (whitespace-separated), and each
/// skipped test filter with its reason.
pub fn scope_of(package: &str, files: &str, skips: &[(String, String)]) -> Vec<(String, String)> {
    let mut scope = vec![
        ("package".to_string(), package.to_string()),
        (
            "files".to_string(),
            files.split_whitespace().collect::<Vec<_>>().join(" "),
        ),
    ];
    scope.extend(
        skips
            .iter()
            .map(|(filter, reason)| (format!("skip {filter}"), reason.clone())),
    );
    scope
}

/// The scope `tools/mutants/sets.tsv` declares for `set` ([`scope_of`]), or
/// `None` when it declares no such set. Records split at every tab, as
/// `tools/mutants/sets.sh` splits them; a malformed one is `tools/mutants/sets.sh`'s
/// to refuse, so here it simply does not match.
pub fn set_scope(sets_tsv: &str, set: &str) -> Option<Vec<(String, String)>> {
    let mut found = None;
    let mut skips = Vec::new();
    for line in sets_tsv.lines() {
        match line.split('\t').collect::<Vec<_>>().as_slice() {
            ["set", name, package, files] if *name == set => found = Some((*package, *files)),
            ["skip", name, filter, reason] if *name == set => {
                skips.push((filter.to_string(), reason.to_string()))
            }
            _ => {}
        }
    }
    found.map(|(package, files)| scope_of(package, files, &skips))
}

/// Read `tools/mutants/equivalent.tsv`: `set<TAB>key<TAB>site<TAB>reason`
/// lines, with blank and `#` lines skipped.
pub fn parse_equivalents(text: &str) -> Result<Vec<Equivalent>, String> {
    let mut out = Vec::new();
    for (i, line) in text.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let fields: Vec<&str> = line.split('\t').collect();
        let [set, key, site, reason] = fields.as_slice() else {
            return Err(format!(
                "equivalent.tsv:{}: {} fields, not 4 (set, key, site, reason)",
                i + 1,
                fields.len()
            ));
        };
        if [set, key, site, reason].iter().any(|f| f.trim().is_empty()) {
            return Err(format!("equivalent.tsv:{}: an empty field", i + 1));
        }
        out.push(Equivalent {
            set: set.to_string(),
            key: key.to_string(),
            site: site.to_string(),
            reason: reason.to_string(),
        });
    }
    Ok(out)
}

/// The manifest keys of `mutants`, in their order: `file: description`, with
/// ` #<n>` on the second and later mutants sharing one, numbered in source
/// order.
pub fn keys(mutants: &[Graded]) -> Vec<String> {
    let mut order: Vec<usize> = (0..mutants.len()).collect();
    order.sort_by_key(|&i| (&mutants[i].file, mutants[i].start, i));
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut keys = vec![String::new(); mutants.len()];
    for i in order {
        let base = format!("{}: {}", mutants[i].file, mutants[i].description);
        let n = seen.entry(base.clone()).or_default();
        *n += 1;
        keys[i] = if *n == 1 {
            base
        } else {
            format!("{base} #{n}")
        };
    }
    keys
}

/// Why a run cannot be a manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RunError {
    /// The unmutated baseline failed, so no verdict means anything.
    BaselineFailed,
    /// The run has no baseline outcome, so a test that fails on the original
    /// tree is indistinguishable from one that caught a mutant.
    NoBaseline,
    /// The run graded no mutant.
    NoMutants,
    /// The mutants graded are not the mutants `--list` named, by full name
    /// (file, line, column and mutation).
    ListMismatch {
        /// Listed, and graded fewer times than listed.
        ungraded: Vec<String>,
        /// Graded more times than listed.
        unlisted: Vec<String>,
    },
    /// The tests caught no mutant: the run cannot tell its tests from none.
    NothingCaught,
    /// An `equivalent.tsv` row for this set names a key no mutant has.
    UnknownEquivalent(String),
    /// An `equivalent.tsv` row names a set `sets.tsv` does not declare, so no
    /// run would ever read it.
    UndeclaredSet(String),
    /// An `equivalent.tsv` row names a mutant the run did not miss.
    StaleEquivalent {
        /// The row's key.
        key: String,
        /// What the run made of it.
        verdict: Verdict,
    },
    /// Two `equivalent.tsv` rows for one mutant.
    DuplicateEquivalent(String),
    /// An `equivalent.tsv` row's mutant shares its file, mutation and site
    /// with another, so a reordering could move the row's key to a mutant its
    /// argument never covered.
    AmbiguousEquivalent(String),
    /// An `equivalent.tsv` row's key belongs to a mutant at another site: its
    /// argument was about a different mutation.
    MovedEquivalent {
        /// The row's key.
        key: String,
        /// The site the row names.
        row: String,
        /// The site the key's mutant has now, if the caller read it.
        now: Option<String>,
    },
    /// A key or verdict is not a manifest entry.
    Entry(EntryError),
}

impl std::fmt::Display for RunError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RunError::BaselineFailed => write!(f, "the unmutated baseline failed"),
            RunError::NoBaseline => write!(f, "the run has no unmutated baseline"),
            RunError::NoMutants => write!(f, "the run graded no mutant"),
            RunError::ListMismatch { ungraded, unlisted } => write!(
                f,
                "the mutants graded are not the mutants listed: listed but not graded \
                 {ungraded:?}; graded but not listed {unlisted:?}"
            ),
            RunError::NothingCaught => write!(
                f,
                "the tests caught no mutant, so the run cannot tell them from no tests"
            ),
            RunError::UndeclaredSet(s) => write!(
                f,
                "equivalent.tsv has a row for {s:?}, which sets.tsv does not declare"
            ),
            RunError::UnknownEquivalent(k) => {
                write!(
                    f,
                    "equivalent.tsv names {k:?}, which is no mutant of the set"
                )
            }
            RunError::StaleEquivalent { key, verdict } => write!(
                f,
                "equivalent.tsv calls {key:?} equivalent, but the run says {}",
                verdict.as_str()
            ),
            RunError::DuplicateEquivalent(k) => write!(f, "equivalent.tsv lists {k:?} twice"),
            RunError::AmbiguousEquivalent(k) => write!(
                f,
                "equivalent.tsv argues {k:?}, but another mutant has its file, mutation and \
                 site, so the row cannot say which it covers"
            ),
            RunError::MovedEquivalent { key, row, now } => write!(
                f,
                "equivalent.tsv argues {key:?} at {row:?}, but that key's mutant is now at \
                 {now:?}; review the argument for the mutant it now names"
            ),
            RunError::Entry(e) => write!(f, "{e}"),
        }
    }
}

/// What starts a scope entry's key. No mutant key starts so: each starts with
/// its file's path.
const SCOPE_PREFIX: &str = "scope: ";

/// cargo-mutants' full name for `m`, as `--list` prints it.
pub fn full_name(m: &Graded) -> String {
    format!("{}:{}:{}: {}", m.file, m.start.0, m.start.1, m.description)
}

/// The manifest of one set's run. `listed` is every mutant cargo-mutants'
/// `--list` named for the set before the run, by full name; `scope` is the
/// run's `(name, value)` scope ([the module docs](self)); `declared` is every
/// set `sets.tsv` declares; `equivalents` is every row of `equivalent.tsv`,
/// each of which must name a declared set, and of which only `set`'s are read.
pub fn manifest_items(
    set: &str,
    outcomes: &Outcomes,
    listed: &[String],
    scope: &[(String, String)],
    declared: &BTreeSet<String>,
    equivalents: &[Equivalent],
) -> Result<Manifest, RunError> {
    if let Some(e) = equivalents.iter().find(|e| !declared.contains(&e.set)) {
        return Err(RunError::UndeclaredSet(e.set.clone()));
    }
    match outcomes.baseline_passed {
        Some(true) => {}
        Some(false) => return Err(RunError::BaselineFailed),
        None => return Err(RunError::NoBaseline),
    }
    if outcomes.mutants.is_empty() {
        return Err(RunError::NoMutants);
    }
    let mut balance: BTreeMap<String, i64> = BTreeMap::new();
    for name in listed {
        *balance.entry(name.clone()).or_default() += 1;
    }
    for m in &outcomes.mutants {
        *balance.entry(full_name(m)).or_default() -= 1;
    }
    let names_where = |keep: fn(i64) -> bool| -> Vec<String> {
        balance
            .iter()
            .filter(|(_, n)| keep(**n))
            .map(|(k, _)| k.clone())
            .collect()
    };
    let (ungraded, unlisted) = (names_where(|n| n > 0), names_where(|n| n < 0));
    if !ungraded.is_empty() || !unlisted.is_empty() {
        return Err(RunError::ListMismatch { ungraded, unlisted });
    }
    if !outcomes
        .mutants
        .iter()
        .any(|m| m.verdict == Verdict::Caught)
    {
        return Err(RunError::NothingCaught);
    }
    let keys = keys(&outcomes.mutants);
    let by_key: BTreeMap<&str, &Graded> = keys
        .iter()
        .map(String::as_str)
        .zip(outcomes.mutants.iter())
        .collect();
    let mut reasons: BTreeMap<&str, &str> = BTreeMap::new();
    let mut listed_twice = BTreeSet::new();
    for e in equivalents.iter().filter(|e| e.set == set) {
        if reasons.insert(&e.key, &e.reason).is_some() {
            listed_twice.insert(e.key.clone());
        }
    }
    if let Some(k) = listed_twice.into_iter().next() {
        return Err(RunError::DuplicateEquivalent(k));
    }
    for e in equivalents.iter().filter(|e| e.set == set) {
        let Some(m) = by_key.get(e.key.as_str()) else {
            return Err(RunError::UnknownEquivalent(e.key.clone()));
        };
        if m.site.as_deref() != Some(e.site.as_str()) {
            return Err(RunError::MovedEquivalent {
                key: e.key.clone(),
                row: e.site.clone(),
                now: m.site.as_deref().map(str::to_string),
            });
        }
        let twins = outcomes
            .mutants
            .iter()
            .filter(|o| o.file == m.file && o.description == m.description && o.site == m.site)
            .count();
        if twins > 1 {
            return Err(RunError::AmbiguousEquivalent(e.key.clone()));
        }
        if m.verdict != Verdict::Missed {
            return Err(RunError::StaleEquivalent {
                key: e.key.clone(),
                verdict: m.verdict,
            });
        }
    }
    let verdict_items = keys.iter().zip(&outcomes.mutants).map(|(key, m)| {
        let value = match reasons.get(key.as_str()) {
            Some(reason) => format!("equivalent: {reason}"),
            None => m.verdict.as_str().to_string(),
        };
        (key.clone(), value)
    });
    let scope_items = scope
        .iter()
        .map(|(name, value)| (format!("{SCOPE_PREFIX}{name}"), value.clone()));
    Manifest::from_keyed(verdict_items.chain(scope_items)).map_err(RunError::Entry)
}

/// How many mutant entries of `manifest` carry each verdict, for the run's
/// report: `caught`, `missed`, `timeout`, `unviable` and `equivalent`, in that
/// order. Scope entries are not mutants, whatever their values say.
pub fn tally(manifest: &Manifest) -> [(&'static str, usize); 5] {
    let mut out = [
        ("caught", 0),
        ("missed", 0),
        ("timeout", 0),
        ("unviable", 0),
        ("equivalent", 0),
    ];
    for entry in manifest.entries() {
        let (key, value) = entry
            .split_once(crate::manifest::KEY_SEPARATOR)
            .unwrap_or((entry, ""));
        if key.starts_with(SCOPE_PREFIX) {
            continue;
        }
        let verdict = value.split(':').next().unwrap_or("");
        if let Some(slot) = out.iter_mut().find(|(name, _)| *name == verdict) {
            slot.1 += 1;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    /// Runs one of `tools/mutants/`'s shell tests, so `cargo test` holds the
    /// sandbox canary and the set reader to them wherever it runs.
    fn shell_test(name: &str) {
        let script = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tools/mutants")
            .join(name);
        let mut cmd = std::process::Command::new("bash");
        cmd.arg(&script);
        let out = borzoi_spawn::BoundedCommand::new(cmd)
            .timeout(std::time::Duration::from_secs(600))
            .run()
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        assert!(
            out.status.success(),
            "{name} failed:\n{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
    }

    #[test]
    fn the_canary_shell_test_passes() {
        shell_test("canary.test.sh");
    }

    #[test]
    fn the_sets_shell_test_passes() {
        shell_test("sets.test.sh");
    }

    #[test]
    fn the_stage_shell_test_passes() {
        shell_test("stage.test.sh");
    }

    /// A graded mutant whose site is `line <line>`.
    fn graded(file: &str, line: u32, description: &str, verdict: Verdict) -> Graded {
        Graded {
            file: file.into(),
            start: (line, 5),
            end_line: line,
            description: description.into(),
            verdict,
            site: Some(format!("line {line}").into()),
        }
    }

    fn outcomes(mutants: Vec<Graded>) -> Outcomes {
        Outcomes {
            baseline_passed: Some(true),
            mutants,
        }
    }

    #[test]
    fn parses_cargo_mutants_outcomes() {
        let json = r#"{"outcomes": [
            {"scenario": "Baseline", "summary": "Success"},
            {"scenario": {"Mutant": {"file": "src/a.rs", "name": "src/a.rs:3:9: replace f -> bool with true",
              "span": {"start": {"line": 3, "column": 9}, "end": {"line": 3, "column": 20}}}},
             "summary": "MissedMutant"},
            {"scenario": {"Mutant": {"file": "src/a.rs", "name": "src/a.rs:7:1: delete ! in g",
              "span": {"start": {"line": 7, "column": 1}, "end": {"line": 7, "column": 2}}}},
             "summary": "CaughtMutant"}
        ]}"#;
        let parsed = parse_outcomes(json).unwrap();
        assert_eq!(parsed.baseline_passed, Some(true));
        assert_eq!(
            parsed.mutants,
            vec![
                graded_at(
                    "src/a.rs",
                    (3, 9),
                    "replace f -> bool with true",
                    Verdict::Missed
                ),
                graded_at("src/a.rs", (7, 1), "delete ! in g", Verdict::Caught),
            ]
        );
    }

    fn graded_at(file: &str, start: (u32, u32), description: &str, verdict: Verdict) -> Graded {
        Graded {
            file: file.into(),
            start,
            end_line: start.0,
            description: description.into(),
            verdict,
            site: None,
        }
    }

    #[test]
    fn a_summary_that_is_no_verdict_fails() {
        let json = r#"{"outcomes": [
            {"scenario": {"Mutant": {"file": "a.rs", "name": "a.rs:1:1: delete ! in g",
              "span": {"start": {"line": 1, "column": 1}, "end": {"line": 1, "column": 2}}}}, "summary": "Failure"}
        ]}"#;
        assert!(parse_outcomes(json).unwrap_err().contains("no verdict"));
    }

    #[test]
    fn a_name_not_at_its_span_fails() {
        let json = r#"{"outcomes": [
            {"scenario": {"Mutant": {"file": "a.rs", "name": "a.rs:2:1: delete ! in g",
              "span": {"start": {"line": 1, "column": 1}, "end": {"line": 1, "column": 2}}}}, "summary": "CaughtMutant"}
        ]}"#;
        assert!(parse_outcomes(json).unwrap_err().contains("does not start"));
    }

    fn decl() -> BTreeSet<String> {
        ["s", "other"].map(String::from).into()
    }

    fn listed_of(o: &Outcomes) -> Vec<String> {
        o.mutants.iter().map(full_name).collect()
    }

    /// `manifest_items` for set `s` of a run that graded exactly what it
    /// listed, with no scope.
    fn items(o: &Outcomes, equivalents: &[Equivalent]) -> Result<Manifest, RunError> {
        manifest_items("s", o, &listed_of(o), &[], &decl(), equivalents)
    }

    #[test]
    fn a_failed_or_missing_baseline_is_no_manifest() {
        let mut o = outcomes(vec![graded("a.rs", 1, "x", Verdict::Caught)]);
        o.baseline_passed = Some(false);
        assert_eq!(items(&o, &[]), Err(RunError::BaselineFailed));
        o.baseline_passed = None;
        assert_eq!(items(&o, &[]), Err(RunError::NoBaseline));
    }

    #[test]
    fn an_equivalent_of_an_undeclared_set_fails_every_run() {
        let o = outcomes(vec![graded("a.rs", 1, "x", Verdict::Caught)]);
        assert_eq!(
            items(&o, &[eq("renamed", "b.rs: y", 1)]),
            Err(RunError::UndeclaredSet("renamed".into()))
        );
    }

    #[test]
    fn set_scope_reads_the_set_and_its_skips() {
        let tsv = "# set\ts\tx\ty\nset\ts\tp\ta.rs  b/*.rs\nskip\ts\tnet_\twhy\n\
                   skip\to\tslow\tother\nset\to\tq\tc.rs\n";
        assert_eq!(
            set_scope(tsv, "s"),
            Some(vec![
                ("package".into(), "p".into()),
                ("files".into(), "a.rs b/*.rs".into()),
                ("skip net_".into(), "why".into()),
            ])
        );
        assert_eq!(set_scope(tsv, "missing"), None);
        assert_eq!(
            set_scope(tsv, "s"),
            Some(scope_of(
                "p",
                "a.rs b/*.rs",
                &[("net_".into(), "why".into())]
            ))
        );
    }

    #[test]
    fn declared_sets_reads_set_records_only() {
        let tsv = "# set\tcomment\tx\ty\nset\ta\tp\tf.rs\nskip\tb\tt\twhy\nset\tc\tp\tg.rs\n";
        assert_eq!(declared_sets(tsv), ["a", "c"].map(String::from).into());
    }

    #[test]
    fn vacuous_runs_fail() {
        assert_eq!(items(&outcomes(vec![]), &[]), Err(RunError::NoMutants));
        let missed = outcomes(vec![graded("a.rs", 1, "x", Verdict::Missed)]);
        assert_eq!(items(&missed, &[]), Err(RunError::NothingCaught));
    }

    #[test]
    fn graded_mutants_must_be_exactly_the_listed_ones() {
        let caught = outcomes(vec![
            graded("a.rs", 1, "x", Verdict::Caught),
            graded("a.rs", 2, "x", Verdict::Caught),
        ]);
        let listed = listed_of(&caught);
        // One listed mutant graded twice, in place of another: same count.
        let mut doubled = caught.clone();
        doubled.mutants[1] = doubled.mutants[0].clone();
        assert_eq!(
            manifest_items("s", &doubled, &listed, &[], &decl(), &[]),
            Err(RunError::ListMismatch {
                ungraded: vec!["a.rs:2:5: x".into()],
                unlisted: vec!["a.rs:1:5: x".into()],
            })
        );
        // One listed mutant never graded.
        let mut short = caught.clone();
        short.mutants.pop();
        assert_eq!(
            manifest_items("s", &short, &listed, &[], &decl(), &[]),
            Err(RunError::ListMismatch {
                ungraded: vec!["a.rs:2:5: x".into()],
                unlisted: vec![],
            })
        );
        assert!(manifest_items("s", &caught, &listed, &[], &decl(), &[]).is_ok());
    }

    #[test]
    fn the_scope_is_compared_with_the_verdicts() {
        let o = outcomes(vec![graded("a.rs", 1, "x", Verdict::Caught)]);
        let scope = [
            ("package".to_string(), "p".to_string()),
            (
                "skip net_".to_string(),
                "timeout: over the job's budget".to_string(),
            ),
        ];
        let m = manifest_items("s", &o, &listed_of(&o), &scope, &decl(), &[]).unwrap();
        assert_eq!(
            m.entries(),
            &[
                "a.rs: x\tcaught".to_string(),
                "scope: package\tp".to_string(),
                "scope: skip net_\ttimeout: over the job's budget".to_string(),
            ]
        );
        assert_eq!(tally(&m)[0], ("caught", 1));
        // A scope value that reads like a verdict counts as none.
        assert_eq!(tally(&m)[2], ("timeout", 0));
    }

    fn eq(set: &str, key: &str, line: u32) -> Equivalent {
        Equivalent {
            set: set.into(),
            key: key.into(),
            site: format!("line {line}"),
            reason: "no caller reads it".into(),
        }
    }

    #[test]
    fn equivalents_annotate_missed_mutants_of_their_set_only() {
        let o = outcomes(vec![
            graded("a.rs", 1, "x", Verdict::Caught),
            graded("a.rs", 2, "y", Verdict::Missed),
        ]);
        let m = items(&o, &[eq("s", "a.rs: y", 2), eq("other", "b.rs: z", 9)]).unwrap();
        assert_eq!(
            m.entries(),
            &[
                "a.rs: x\tcaught".to_string(),
                "a.rs: y\tequivalent: no caller reads it".to_string()
            ]
        );
        assert_eq!(tally(&m)[0], ("caught", 1));
        assert_eq!(tally(&m)[4], ("equivalent", 1));
    }

    #[test]
    fn stale_unknown_and_duplicate_equivalents_fail() {
        let o = outcomes(vec![
            graded("a.rs", 1, "x", Verdict::Caught),
            graded("a.rs", 2, "y", Verdict::Missed),
        ]);
        assert_eq!(
            items(&o, &[eq("s", "a.rs: x", 1)]),
            Err(RunError::StaleEquivalent {
                key: "a.rs: x".into(),
                verdict: Verdict::Caught
            })
        );
        assert_eq!(
            items(&o, &[eq("s", "a.rs: gone", 3)]),
            Err(RunError::UnknownEquivalent("a.rs: gone".into()))
        );
        assert_eq!(
            items(&o, &[eq("s", "a.rs: y", 2), eq("s", "a.rs: y", 2)]),
            Err(RunError::DuplicateEquivalent("a.rs: y".into()))
        );
    }

    #[test]
    fn an_equivalence_stays_with_its_site_when_ordinals_shift() {
        // `y` at line 5 is argued equivalent as `a.rs: y`. A new missed `y`
        // at line 2 takes that key, and the argued one becomes `a.rs: y #2`.
        let before = outcomes(vec![
            graded("a.rs", 1, "x", Verdict::Caught),
            graded("a.rs", 5, "y", Verdict::Missed),
        ]);
        let row = [eq("s", "a.rs: y", 5)];
        assert!(items(&before, &row).is_ok());
        let after = outcomes(vec![
            graded("a.rs", 1, "x", Verdict::Caught),
            graded("a.rs", 2, "y", Verdict::Missed),
            graded("a.rs", 5, "y", Verdict::Missed),
        ]);
        assert_eq!(
            items(&after, &row),
            Err(RunError::MovedEquivalent {
                key: "a.rs: y".into(),
                row: "line 5".into(),
                now: Some("line 2".into()),
            })
        );
        // A site the caller never read matches no row.
        let mut unread = before.clone();
        unread.mutants[1].site = None;
        assert!(matches!(
            items(&unread, &row),
            Err(RunError::MovedEquivalent { now: None, .. })
        ));
    }

    #[test]
    fn an_equivalence_whose_site_repeats_is_refused() {
        // Two identical guards in one function: same file, mutation and site.
        let mut o = outcomes(vec![
            graded("a.rs", 1, "x", Verdict::Caught),
            graded("a.rs", 2, "y", Verdict::Missed),
            graded("a.rs", 3, "y", Verdict::Missed),
        ]);
        for m in &mut o.mutants[1..] {
            m.site = Some("if !ok {".into());
        }
        let row = Equivalent {
            set: "s".into(),
            key: "a.rs: y".into(),
            site: "if !ok {".into(),
            reason: "no caller reads it".into(),
        };
        assert_eq!(
            items(&o, &[row]),
            Err(RunError::AmbiguousEquivalent("a.rs: y".into()))
        );
    }

    #[test]
    fn sites_are_read_only_for_the_files_rows_name_and_shared_per_line() {
        let rows = [eq("s", "a.rs: y", 2), eq("other", "b.rs: z", 1)];
        assert_eq!(
            equivalence_files("s", &rows),
            ["a.rs"].into_iter().collect::<BTreeSet<_>>()
        );
        let mut mutants = vec![
            graded_at("a.rs", (2, 1), "y", Verdict::Missed),
            graded_at("a.rs", (2, 9), "z", Verdict::Caught),
            graded_at("b.rs", (1, 1), "z", Verdict::Missed),
        ];
        let src = "fn f() {\n  if  !x {\n";
        let sources: BTreeMap<&str, String> = [("a.rs", src.to_string())].into();
        attach_sites(&mut mutants, &sources);
        assert_eq!(mutants[0].site.as_deref(), site_of(src, 2, 2).as_deref());
        assert!(Arc::ptr_eq(
            mutants[0].site.as_ref().unwrap(),
            mutants[1].site.as_ref().unwrap()
        ));
        assert_eq!(mutants[2].site, None);
    }

    #[test]
    fn a_site_covers_every_character_of_its_span_and_nothing_else() {
        let src = "fn f(n: u8) -> bool {\n    let m = u16::from(n);\n    m < 256\n}\nfn g() {}\n";
        let site = site_of(src, 1, 4).unwrap();
        assert!(site.starts_with("fnv1a64:") && site.len() == "fnv1a64:".len() + 16);
        // An edit on a later line of the span moves it, a literal included.
        assert_ne!(site_of(&src.replace("256", "255"), 1, 4).unwrap(), site);
        // So does whitespace inside the span.
        assert_ne!(
            site_of(&src.replace("m < 256", "m <  256"), 1, 4).unwrap(),
            site
        );
        // An edit outside it does not.
        assert_eq!(
            site_of(&src.replace("fn g() {}", "fn g() { }"), 1, 4).unwrap(),
            site
        );
        // A span past the end, or turned around, has no site.
        assert_eq!(site_of(src, 0, 1), None);
        assert_eq!(site_of(src, 5, 6), None);
        assert_eq!(site_of(src, 3, 2), None);
    }

    #[test]
    fn a_span_that_ends_before_it_starts_fails() {
        let json = r#"{"outcomes": [
            {"scenario": {"Mutant": {"file": "a.rs", "name": "a.rs:3:1: delete ! in g",
              "span": {"start": {"line": 3, "column": 1}, "end": {"line": 2, "column": 1}}}},
             "summary": "CaughtMutant"}
        ]}"#;
        assert!(parse_outcomes(json).unwrap_err().contains("ends before"));
    }

    #[test]
    fn equivalents_tsv_needs_four_nonempty_fields() {
        assert!(parse_equivalents("s\tk\twhy").is_err());
        assert!(parse_equivalents("s\tk\tline\t ").is_err());
        assert_eq!(
            parse_equivalents("# c\n\ns\tk\tfnv1a64:0123456789abcdef\twhy\n").unwrap(),
            vec![Equivalent {
                set: "s".into(),
                key: "k".into(),
                site: "fnv1a64:0123456789abcdef".into(),
                reason: "why".into()
            }]
        );
    }

    fn mutant_list() -> impl Strategy<Value = Vec<Graded>> {
        // Few files and descriptions, so names collide often.
        let one = (
            prop::sample::select(vec!["a.rs", "b.rs"]),
            1u32..40,
            1u32..5,
            prop::sample::select(vec!["delete ! in f", "replace f -> bool with true"]),
        );
        prop::collection::vec(one, 0..24).prop_map(|v| {
            let mut seen = BTreeSet::new();
            v.into_iter()
                // cargo-mutants never puts two mutants with one name at one place.
                .filter(|(f, l, c, d)| seen.insert((*f, *l, *c, *d)))
                .map(|(f, l, c, d)| graded_at(f, (l, c), d, Verdict::Caught))
                .collect()
        })
    }

    proptest! {
        // Keys are distinct, whatever collides.
        #[test]
        fn keys_are_distinct(mutants in mutant_list()) {
            let keys = keys(&mutants);
            let distinct: BTreeSet<&String> = keys.iter().collect();
            prop_assert_eq!(distinct.len(), mutants.len());
        }

        // Moving every mutant of one file by the same number of lines, as an
        // edit above them does, moves no mutant's key; neither does the order
        // cargo-mutants reports them in. Each mutant is followed by its index,
        // so a key that moves to another mutant fails too.
        #[test]
        fn keys_ignore_shifts_and_report_order(
            mutants in mutant_list(),
            shift in 0u32..1000,
            rotate in 0usize..24,
        ) {
            let before = keys(&mutants);
            let mut shifted: Vec<(usize, Graded)> = mutants
                .iter()
                .cloned()
                .map(|mut m| {
                    if m.file == "a.rs" {
                        m.start.0 += shift;
                    }
                    m
                })
                .enumerate()
                .collect();
            if !shifted.is_empty() {
                let r = rotate % shifted.len();
                shifted.rotate_left(r);
            }
            let reordered: Vec<Graded> = shifted.iter().map(|(_, m)| m.clone()).collect();
            for ((original, _), key) in shifted.iter().zip(keys(&reordered)) {
                prop_assert_eq!(&before[*original], &key);
            }
        }
    }
}
