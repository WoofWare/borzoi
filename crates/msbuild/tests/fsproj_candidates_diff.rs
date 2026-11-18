//! The candidate channel held to MSBuild (#1009): the value a property ends
//! with in the real build is always among the walk's candidates for it, or the
//! walk says it may hold anything.
//!
//! Generated projects write a few properties from literals and from each
//! other, under gates the walk decides, gates it cannot decide, and `<Choose>`
//! branches of either kind. The gates the walk cannot decide read a global,
//! `G`, through a property function it does not model, and MSBuild decides
//! them on `G`; each project is evaluated under several values of `G`, so that
//! across the runs MSBuild takes both arms of every such gate. Under each, the
//! walk (handed the same globals) must name MSBuild's final value of every
//! property among its candidates.

mod common;

use std::collections::{BTreeSet, HashMap};
use std::fmt::Write as _;

use borzoi_msbuild::test_support::{ReadProbe, parse_fsproj_reads};
use common::{Oracle, SplitMix64, soak_parameters};
use tempfile::TempDir;

/// The names written and read back. `G` is the global: MSBuild ignores a
/// project's writes to it.
const NAMES: &[&str] = &["Alpha", "Beta", "Gamma", "G"];
const GLOBALS: &[&str] = &["x", "y", "z"];

fn value(rng: &mut SplitMix64) -> String {
    rng.pick(&[
        "",
        "a",
        "b",
        "$(Alpha)",
        "$(Beta)",
        "$(Alpha)$(Beta)",
        "x$(Gamma)",
        "$(Alpha)y",
        "a;b",
        "%61%3B",
        "a\\b",
        "$(Alpha)\\c",
        "$(G)",
        "$(Alpha.Trim())",
        "$([MSBuild]::ValueOrDefault('$(Beta)', 'd'))",
        "$(Gamma.ToUpperInvariant())",
    ])
    .to_string()
}

/// A gate: none, decided either way, decided by MSBuild on `G` through a
/// function the walk does not model, or reading a generated name, which the
/// walk decides on the value it holds, certain of it or not.
fn gate(rng: &mut SplitMix64) -> String {
    rng.pick(&[
        "",
        " Condition=\"'$(Alpha)' == 'a'\"",
        " Condition=\"'$(Beta)' != ''\"",
        " Condition=\"'$(Gamma)' == ''\"",
        " Condition=\"'$(Alpha)$(Beta)' == 'ab'\"",
        " Condition=\"'k' == 'k'\"",
        " Condition=\"'k' == 'j'\"",
        " Condition=\"'$(G.ToUpperInvariant())' == 'X'\"",
        " Condition=\"'$(G.ToUpperInvariant())' != 'X'\"",
        " Condition=\"'$(G.ToUpperInvariant())' == 'Y'\"",
    ])
    .to_string()
}

fn writes(rng: &mut SplitMix64, out: &mut String) {
    for _ in 0..1 + rng.below(2) {
        let name = rng.pick(NAMES);
        let own = if rng.below(3) == 0 {
            gate(rng)
        } else {
            String::new()
        };
        let _ = write!(out, "<{name}{own}>{}</{name}>", value(rng));
    }
}

fn project(rng: &mut SplitMix64) -> String {
    let mut body = String::new();
    for _ in 0..3 + rng.below(5) {
        if rng.below(4) == 0 {
            body.push_str("<Choose>");
            for _ in 0..1 + rng.below(2) {
                let _ = write!(body, "<When{}><PropertyGroup>", {
                    let mut g = gate(rng);
                    if g.is_empty() {
                        g = " Condition=\"'k' == 'k'\"".to_owned();
                    }
                    g
                });
                writes(rng, &mut body);
                body.push_str("</PropertyGroup></When>");
            }
            if rng.below(2) == 0 {
                body.push_str("<Otherwise><PropertyGroup>");
                writes(rng, &mut body);
                body.push_str("</PropertyGroup></Otherwise>");
            }
            body.push_str("</Choose>");
        } else {
            let _ = write!(body, "<PropertyGroup{}>", gate(rng));
            writes(rng, &mut body);
            body.push_str("</PropertyGroup>");
        }
    }
    format!("<Project>{body}</Project>")
}

#[derive(Debug, Default)]
struct Census {
    cases: usize,
    /// Reads where the walk named more than one candidate.
    several: usize,
    /// Names whose MSBuild value differed between runs, each named among
    /// several candidates: a gate the walk could not decide went both ways.
    both_arms: usize,
    /// Reads where the walk said a name may hold anything.
    anything: usize,
}

fn sweep(oracle: &mut Oracle, rng: &mut SplitMix64, cases: usize) -> Census {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let names: Vec<String> = NAMES.iter().map(|n| (*n).to_owned()).collect();
    let probe = ReadProbe {
        properties: names.clone(),
        ..ReadProbe::default()
    };
    let mut census = Census::default();
    for _ in 0..cases {
        let xml = project(rng);
        std::fs::write(&path, &xml).unwrap();
        census.cases += 1;
        let mut seen: HashMap<&str, BTreeSet<String>> = HashMap::new();
        let mut several_names: BTreeSet<&str> = BTreeSet::new();
        for g in GLOBALS {
            let globals = vec![("G".to_owned(), (*g).to_owned())];
            let Some(theirs) = oracle.project(&xml, &names, Some(&path), &globals) else {
                continue;
            };
            let extra: HashMap<String, String> = globals.iter().cloned().collect();
            let (_, reads) = parse_fsproj_reads(
                &xml,
                &path,
                &extra,
                &common::oracle_environment(),
                None,
                None,
                None,
                &probe,
            )
            .expect("well-formed");
            for name in NAMES {
                let real = theirs.get(*name).cloned().unwrap_or_default();
                seen.entry(name).or_default().insert(real.clone());
                match &reads.candidates[*name] {
                    None => census.anything += 1,
                    Some(candidates) => {
                        assert!(
                            candidates.contains(&real),
                            "MSBuild ends with {name} = {real:?} under G={g}, which is not \
                             among the walk's candidates {candidates:?}\n{xml}"
                        );
                        if candidates.len() > 1 {
                            census.several += 1;
                            several_names.insert(name);
                        }
                    }
                }
            }
        }
        census.both_arms += several_names
            .iter()
            .filter(|name| seen.get(*name).is_some_and(|values| values.len() > 1))
            .count();
    }
    census
}

/// [`sweep`] at a fixed seed.
#[test]
fn candidates_contain_what_msbuild_ends_with() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0x0c4a_d1da_7e55);
    let census = sweep(&mut oracle, &mut rng, 300);
    eprintln!("candidates: {census:?}");
    // Anti-vacuity: the channel names several candidates, and MSBuild takes
    // more than one of them across the runs.
    assert!(census.several >= 100, "{census:?}");
    assert!(census.both_arms >= 30, "{census:?}");
}

/// Fresh-seed twin of [`candidates_contain_what_msbuild_ends_with`].
#[test]
#[ignore = "fresh-seed soak; run it when touching the candidate channel"]
fn candidates_soak() {
    let (seed, cases) = soak_parameters("candidates", 3_000);
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let census = sweep(&mut oracle, &mut rng, cases);
    eprintln!("candidates soak: {census:?}");
}
