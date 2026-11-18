//! Gates decided on values the walk holds from before content it could not
//! see (#1037), held certain-implies-exact to MSBuild.
//!
//! Each generated project binds some names, then imports `hidden.props` under
//! a gate the walk cannot decide (`'$(G.ToUpperInvariant())' == 'X'`, which
//! MSBuild decides on the global `G`): the walk passes it unseen and the values
//! it holds go stale. The hidden file rewrites some of those names, and may
//! take a caller global back from the caller (`TreatAsLocalProperty="G"`) and
//! rewrite it. After it come the routes by which a gate decides what the walk
//! evaluates, each gated on a name the hidden file may have rewritten:
//!
//! - a property's own gate;
//! - a `<PropertyGroup>`'s gate;
//! - a `<Choose>`'s `<When>`s, with or without an `<Otherwise>`;
//! - an `<Import>`'s gate, and an `<ImportGroup>`'s, over a sibling file that
//!   writes the names;
//! - a group the walk cannot evaluate at all, holding a child with its own
//!   gate.
//!
//! The walk decides each gate on the value it holds, and may take a branch or
//! skip one that MSBuild, holding the rewritten value, does the opposite with.
//! Each project is evaluated under three values of `G`, of which one takes the
//! hidden file, so every gate sees both the value the walk holds and the
//! rewritten one. Under each, whatever the walk commits, as served and through
//! the read probe, must be MSBuild's value.

#![cfg(unix)]

mod common;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;
use std::path::Path;

use borzoi_msbuild::test_support::{PropertyRead, ReadProbe, parse_fsproj_reads};
use common::{Oracle, SplitMix64, parse_fsproj_with_imports, soak_parameters};
use tempfile::TempDir;

/// The gate the walk cannot decide, and MSBuild decides on `G`.
const UNDECIDABLE: &str = "'$(G.ToUpperInvariant())' == 'X'";
const GLOBALS: &[&str] = &["x", "y", "z"];
/// The names the routes gate on, which the hidden file may rewrite.
const GATES: &[&str] = &["Gate", "Flag"];
/// The names the routes write.
const WRITTEN: &[&str] = &["A", "B", "C"];
/// Every name read back: the written ones, the gates, the global, and copies
/// of a written name and the global made after every route.
const READ: &[&str] = &["A", "B", "C", "Gate", "Flag", "G", "CopyA", "CopyG"];
const SIDES: &[&str] = &["side0.props", "side1.props"];

/// The routes, for the census.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Route {
    OwnGate,
    Group,
    Choose,
    Import,
    ImportGroup,
    UnsupportedGroup,
}

const ROUTES: &[Route] = &[
    Route::OwnGate,
    Route::Group,
    Route::Choose,
    Route::Import,
    Route::ImportGroup,
    Route::UnsupportedGroup,
];

/// A gate on a name the hidden file may rewrite.
fn stale_gate(rng: &mut SplitMix64) -> String {
    let name = rng.pick(GATES);
    let value = rng.pick(&["yes", "no", ""]);
    let op = rng.pick(&["==", "!="]);
    format!(" Condition=\"'$({name})' {op} '{value}'\"")
}

fn literal(rng: &mut SplitMix64) -> &'static str {
    rng.pick(&["yes", "no", "", "v1", "v2"])
}

fn write_one(rng: &mut SplitMix64, out: &mut String) {
    let name = rng.pick(WRITTEN);
    let value = rng.pick(&["w1", "w2", "", "$(Gate)", "$(A)x"]);
    let _ = write!(out, "<{name}>{value}</{name}>");
}

fn route(rng: &mut SplitMix64, route: Route, out: &mut String) {
    match route {
        Route::OwnGate => {
            let name = rng.pick(WRITTEN);
            let _ = write!(
                out,
                "<PropertyGroup><{name}{}>own</{name}></PropertyGroup>",
                stale_gate(rng)
            );
        }
        Route::Group => {
            let _ = write!(out, "<PropertyGroup{}>", stale_gate(rng));
            write_one(rng, out);
            out.push_str("</PropertyGroup>");
        }
        Route::Choose => {
            out.push_str("<Choose>");
            for _ in 0..1 + rng.below(2) {
                // Now and then a gate the walk cannot decide at all, after
                // which every branch is in doubt.
                let gate = if rng.below(4) == 0 {
                    format!(" Condition=\"{UNDECIDABLE}\"")
                } else {
                    stale_gate(rng)
                };
                let _ = write!(out, "<When{gate}><PropertyGroup>");
                write_one(rng, out);
                out.push_str("</PropertyGroup></When>");
            }
            if rng.below(2) == 0 {
                out.push_str("<Otherwise><PropertyGroup>");
                write_one(rng, out);
                out.push_str("</PropertyGroup></Otherwise>");
            }
            out.push_str("</Choose>");
        }
        Route::Import => {
            let _ = write!(
                out,
                "<Import Project=\"{}\"{} />",
                rng.pick(SIDES),
                stale_gate(rng)
            );
        }
        Route::ImportGroup => {
            let _ = write!(
                out,
                "<ImportGroup{}><Import Project=\"{}\" /></ImportGroup>",
                stale_gate(rng),
                rng.pick(SIDES)
            );
        }
        Route::UnsupportedGroup => {
            let name = rng.pick(WRITTEN);
            let _ = write!(
                out,
                "<PropertyGroup Condition=\"{UNDECIDABLE}\"><{name}{}>unsupported</{name}></PropertyGroup>",
                stale_gate(rng)
            );
        }
    }
}

struct Case {
    project: String,
    hidden: String,
    sides: Vec<String>,
    routes: BTreeSet<Route>,
}

fn case(rng: &mut SplitMix64) -> Case {
    // What the walk holds before the hidden file: every gate name and some
    // written ones.
    let mut project = String::from("<Project><PropertyGroup>");
    for name in GATES {
        let _ = write!(project, "<{name}>{}</{name}>", literal(rng));
    }
    for name in WRITTEN {
        if rng.below(2) == 0 {
            let _ = write!(project, "<{name}>{}</{name}>", literal(rng));
        }
    }
    project.push_str("</PropertyGroup>");
    let _ = write!(
        project,
        "<Import Project=\"hidden.props\" Condition=\"{UNDECIDABLE}\" />"
    );
    // Written names bound again after it are fresh, so the walk commits them
    // unless a route below leaves them in doubt; the gate names stay stale.
    project.push_str("<PropertyGroup>");
    for name in WRITTEN {
        if rng.below(4) != 0 {
            let _ = write!(project, "<{name}>{}</{name}>", literal(rng));
        }
    }
    project.push_str("</PropertyGroup>");
    let mut routes = BTreeSet::new();
    for _ in 0..1 + rng.below(4) {
        let chosen = *rng.pick(ROUTES);
        routes.insert(chosen);
        route(rng, chosen, &mut project);
    }
    project.push_str(
        "<PropertyGroup><CopyA>$(A)</CopyA><CopyG>$(G)</CopyG></PropertyGroup></Project>",
    );

    let local = rng.below(3) == 0;
    let mut hidden = String::from(if local {
        "<Project TreatAsLocalProperty=\"G\"><PropertyGroup><G>local</G>"
    } else {
        "<Project><PropertyGroup>"
    });
    for name in GATES.iter().chain(WRITTEN) {
        if rng.below(2) == 0 {
            let _ = write!(hidden, "<{name}>{}</{name}>", literal(rng));
        }
    }
    hidden.push_str("</PropertyGroup></Project>");

    let sides = SIDES
        .iter()
        .map(|_| {
            let mut side = String::from("<Project><PropertyGroup>");
            write_one(rng, &mut side);
            side.push_str("</PropertyGroup></Project>");
            side
        })
        .collect();
    Case {
        project,
        hidden,
        sides,
        routes,
    }
}

/// What the walk commits for `name`, if anything: a value, or the empty
/// string of a name it holds undefined in the real build too.
fn committed(read: &PropertyRead) -> Option<&str> {
    match read {
        PropertyRead::Value(value) => Some(value),
        PropertyRead::Unset => Some(""),
        PropertyRead::UnsetInexact(_) | PropertyRead::Untrusted(_) => None,
    }
}

/// One certain-implies-exact violation, with the routes its case held.
struct Violation {
    routes: BTreeSet<Route>,
    name: &'static str,
    report: String,
}

#[derive(Debug, Default)]
struct Census {
    cases: usize,
    /// Per route: cases holding it where MSBuild's value of some written name
    /// moved across the globals, which only the hidden file can move.
    live: BTreeMap<Route, usize>,
    /// Per route: cases holding it where the walk still committed some written
    /// name, so declining is not all the walk does there.
    committing: BTreeMap<Route, usize>,
    /// Committed `(case, global, name)` points.
    commits: usize,
}

fn sweep(
    oracle: &mut Oracle,
    rng: &mut SplitMix64,
    cases: usize,
    violations: &mut Vec<Violation>,
) -> Census {
    let tmp = TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    let path = dir.join("Demo.fsproj");
    let names: Vec<String> = READ.iter().map(|n| (*n).to_owned()).collect();
    let probe = ReadProbe {
        properties: names.clone(),
        ..ReadProbe::default()
    };
    let mut census = Census::default();
    for _ in 0..cases {
        let case = case(rng);
        std::fs::write(&path, &case.project).unwrap();
        std::fs::write(dir.join("hidden.props"), &case.hidden).unwrap();
        for (name, side) in SIDES.iter().zip(&case.sides) {
            std::fs::write(dir.join(name), side).unwrap();
        }
        census.cases += 1;
        let mut theirs_by_name: BTreeMap<&str, BTreeSet<String>> = BTreeMap::new();
        let mut ours_by_name: BTreeSet<&str> = BTreeSet::new();
        for g in GLOBALS {
            let globals = vec![("G".to_owned(), (*g).to_owned())];
            let Some(theirs) = oracle.project(&case.project, &names, Some(&path), &globals) else {
                continue;
            };
            let extra: HashMap<String, String> = globals.iter().cloned().collect();
            let served = parse_fsproj_with_imports(
                &case.project,
                &path,
                &extra,
                &common::oracle_environment(),
                None,
                None,
            )
            .expect("well-formed");
            let (_, reads) = parse_fsproj_reads(
                &case.project,
                &path,
                &extra,
                &common::oracle_environment(),
                None,
                None,
                None,
                &probe,
            )
            .expect("well-formed");
            for name in READ {
                let real = theirs.get(*name).cloned().unwrap_or_default();
                theirs_by_name.entry(name).or_default().insert(real.clone());
                for (how, read) in [
                    ("served", served.property(name)),
                    ("probed", reads.properties[*name].clone()),
                ] {
                    if let Some(ours) = committed(&read) {
                        census.commits += 1;
                        ours_by_name.insert(name);
                        if ours != real {
                            violations.push(Violation {
                                routes: case.routes.clone(),
                                name,
                                report: format!(
                                    "certain-implies-exact violated for ${name} under G={g} \
                                     ({how}): we commit {ours:?}, MSBuild ends with {real:?}\n\
                                     --- project ---\n{}\n--- hidden.props ---\n{}\n\
                                     --- sides ---\n{}",
                                    case.project,
                                    case.hidden,
                                    case.sides.join("\n")
                                ),
                            });
                        }
                    }
                }
            }
        }
        let live = WRITTEN.iter().any(|name| {
            theirs_by_name
                .get(name)
                .is_some_and(|values| values.len() > 1)
        });
        let committing = WRITTEN.iter().any(|name| ours_by_name.contains(name));
        for route in &case.routes {
            if live {
                *census.live.entry(*route).or_default() += 1;
            }
            if committing {
                *census.committing.entry(*route).or_default() += 1;
            }
        }
    }
    census
}

/// Fail on any violation, naming how many there were per route set and per
/// name, with the smallest few in full.
fn assert_none(mut violations: Vec<Violation>) {
    if violations.is_empty() {
        return;
    }
    let mut by_routes: BTreeMap<String, usize> = BTreeMap::new();
    let mut by_name: BTreeMap<&str, usize> = BTreeMap::new();
    for violation in &violations {
        *by_routes
            .entry(format!("{:?}", violation.routes))
            .or_default() += 1;
        *by_name.entry(violation.name).or_default() += 1;
    }
    violations.sort_by_key(|violation| violation.report.len());
    let examples: Vec<&str> = violations
        .iter()
        .take(3)
        .map(|violation| violation.report.as_str())
        .collect();
    panic!(
        "{} certain-implies-exact violations\nby routes: {by_routes:#?}\nby name: {by_name:?}\n\n{}",
        violations.len(),
        examples.join("\n\n")
    );
}

/// [`sweep`] at a fixed seed.
#[test]
fn stale_gates_are_exact_or_declined() {
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(0x1037_57a1_e6a7);
    let mut violations = Vec::new();
    let census = sweep(&mut oracle, &mut rng, 400, &mut violations);
    eprintln!("stale gates: {census:?}");
    assert_none(violations);
    // Anti-vacuity: every route sits in cases where the hidden file moves
    // what MSBuild ends with, and in cases where the walk still commits.
    assert!(census.commits >= 1000, "{census:?}");
    for route in ROUTES {
        assert!(
            census.live.get(route).copied().unwrap_or(0) >= 10,
            "{route:?} is rarely live: {census:?}"
        );
        assert!(
            census.committing.get(route).copied().unwrap_or(0) >= 10,
            "{route:?} rarely commits: {census:?}"
        );
    }
}

/// Fresh-seed twin of [`stale_gates_are_exact_or_declined`].
#[test]
#[ignore = "fresh-seed soak; run it when touching how the walk skips or takes content"]
fn stale_gates_soak() {
    let (seed, cases) = soak_parameters("stale gates", 3_000);
    let mut oracle = Oracle::spawn();
    let mut rng = SplitMix64(seed);
    let mut violations = Vec::new();
    let census = sweep(&mut oracle, &mut rng, cases, &mut violations);
    eprintln!("stale gates soak: {census:?}");
    assert_none(violations);
}

/// The four shapes of #1037, an import and an import group taken on a stale
/// gate, and a `<Choose>` branch decided on one before an undecided gate, each
/// with what MSBuild ends with when the hidden file is taken (`G=x`): the walk
/// must commit that or nothing.
#[test]
fn issue_1037_shapes_are_exact_or_declined() {
    let hidden_gate = format!("<Import Project=\"hidden.props\" Condition=\"{UNDECIDABLE}\" />");
    let gate_yes = "<Project><PropertyGroup><Gate>yes</Gate></PropertyGroup></Project>";
    let gate_no = "<Project><PropertyGroup><Gate>no</Gate></PropertyGroup></Project>";
    let shapes: Vec<(&str, String, &str, &str, &[(&str, &str)])> = vec![
        (
            "a group skipped on a stale gate",
            format!(
                "<Project><PropertyGroup><Gate>no</Gate></PropertyGroup>{hidden_gate}\
                 <PropertyGroup><A>initial</A></PropertyGroup>\
                 <PropertyGroup Condition=\"'$(Gate)' == 'yes'\"><A>other</A></PropertyGroup>\
                 <PropertyGroup><B>$(A)</B></PropertyGroup></Project>"
            ),
            gate_yes,
            "<Project />",
            &[("A", "other"), ("B", "other")],
        ),
        (
            "an import skipped on a stale gate",
            format!(
                "<Project><PropertyGroup><Gate>no</Gate></PropertyGroup>{hidden_gate}\
                 <PropertyGroup><P>initial</P></PropertyGroup>\
                 <Import Project=\"side0.props\" Condition=\"'$(Gate)' == 'yes'\" />\
                 <PropertyGroup><Q>$(P)</Q></PropertyGroup></Project>"
            ),
            gate_yes,
            "<Project><PropertyGroup><P>new</P></PropertyGroup></Project>",
            &[("P", "new"), ("Q", "new")],
        ),
        (
            "a caller global taken back by hidden content",
            format!(
                "<Project>{hidden_gate}<PropertyGroup><Copy>$(G)</Copy></PropertyGroup></Project>"
            ),
            "<Project TreatAsLocalProperty=\"G\"><PropertyGroup><G>local</G></PropertyGroup></Project>",
            "<Project />",
            &[("G", "local"), ("Copy", "local")],
        ),
        (
            "an unsupported group's child on a stale gate",
            format!(
                "<Project><PropertyGroup><Gate>no</Gate></PropertyGroup>{hidden_gate}\
                 <PropertyGroup><A>initial</A></PropertyGroup>\
                 <PropertyGroup Condition=\"{UNDECIDABLE}\">\
                 <A Condition=\"'$(Gate)' == 'yes'\">other</A></PropertyGroup>\
                 <PropertyGroup><B>$(A)</B></PropertyGroup></Project>"
            ),
            gate_yes,
            "<Project />",
            &[("A", "other"), ("B", "other")],
        ),
        (
            "an import taken on a stale gate",
            format!(
                "<Project><PropertyGroup><Gate>yes</Gate></PropertyGroup>{hidden_gate}\
                 <PropertyGroup><P>initial</P></PropertyGroup>\
                 <Import Project=\"side0.props\" Condition=\"'$(Gate)' == 'yes'\" />\
                 <PropertyGroup><Q>$(P)</Q></PropertyGroup></Project>"
            ),
            gate_no,
            "<Project><PropertyGroup><P>new</P></PropertyGroup></Project>",
            &[("P", "initial"), ("Q", "initial")],
        ),
        (
            "an import group taken on a stale gate",
            format!(
                "<Project><PropertyGroup><Gate>yes</Gate></PropertyGroup>{hidden_gate}\
                 <PropertyGroup><P>initial</P></PropertyGroup>\
                 <ImportGroup Condition=\"'$(Gate)' == 'yes'\"><Import Project=\"side0.props\" /></ImportGroup>\
                 <PropertyGroup><Q>$(P)</Q></PropertyGroup></Project>"
            ),
            gate_no,
            "<Project><PropertyGroup><P>new</P></PropertyGroup></Project>",
            &[("P", "initial"), ("Q", "initial")],
        ),
        (
            "a <Choose> branch on a stale gate before an undecided one",
            format!(
                "<Project><PropertyGroup><Gate>no</Gate></PropertyGroup>{hidden_gate}\
                 <PropertyGroup><D>initial</D></PropertyGroup>\
                 <Choose><When Condition=\"'$(Gate)' == 'yes'\"><PropertyGroup><D>other</D></PropertyGroup></When>\
                 <When Condition=\"{UNDECIDABLE}\"><PropertyGroup><F>z</F></PropertyGroup></When></Choose>\
                 <PropertyGroup><E>$(D)</E></PropertyGroup></Project>"
            ),
            gate_yes,
            "<Project />",
            &[("D", "other"), ("E", "other")],
        ),
    ];
    let mut oracle = Oracle::spawn();
    let mut failures = Vec::new();
    for (label, project, hidden, side0, expected) in shapes {
        let tmp = TempDir::new().unwrap();
        let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
        let path = dir.join("Demo.fsproj");
        std::fs::write(&path, &project).unwrap();
        std::fs::write(dir.join("hidden.props"), hidden).unwrap();
        std::fs::write(dir.join("side0.props"), side0).unwrap();
        let names: Vec<String> = expected.iter().map(|(n, _)| (*n).to_owned()).collect();
        for g in GLOBALS {
            let globals = vec![("G".to_owned(), (*g).to_owned())];
            let theirs = oracle
                .project(&project, &names, Some(&path), &globals)
                .expect("MSBuild evaluates the shape");
            if *g == "x" {
                for (name, value) in expected {
                    assert_eq!(
                        theirs.get(*name).map(String::as_str),
                        Some(*value),
                        "{label}: the pinned MSBuild value of ${name} is wrong, so the case \
                         does not take its route"
                    );
                }
            }
            failures.extend(check_exact(
                &project, &path, &globals, &theirs, &names, label,
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

fn check_exact(
    project: &str,
    path: &Path,
    globals: &[(String, String)],
    theirs: &HashMap<String, String>,
    names: &[String],
    label: &str,
) -> Vec<String> {
    let mut failures = Vec::new();
    let extra: HashMap<String, String> = globals.iter().cloned().collect();
    let served = parse_fsproj_with_imports(
        project,
        path,
        &extra,
        &common::oracle_environment(),
        None,
        None,
    )
    .expect("well-formed");
    for name in names {
        let real = theirs.get(name).map(String::as_str).unwrap_or_default();
        if let Some(ours) = committed(&served.property(name))
            && ours != real
        {
            failures.push(format!(
                "{label}: certain-implies-exact violated for ${name} under {globals:?}: \
                 we commit {ours:?}, MSBuild ends with {real:?}"
            ));
        }
    }
    failures
}
