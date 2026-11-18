//! Gates decided on values the walk holds from before content it could not
//! see (#1037), held certain-implies-exact to MSBuild.
//!
//! Each generated project binds the gate names, then imports `hidden.props`
//! under a gate the walk cannot decide (`'$(G.ToUpperInvariant())' == 'X'`,
//! which MSBuild decides on the global `G`): the walk passes it unseen and the
//! values it holds go stale. The hidden file rewrites some gate names, and may
//! take a caller global back from the caller (`TreatAsLocalProperty="G"`) and
//! rewrite it. After it, each route's output is bound afresh, and then come the
//! routes by which a gate decides what the walk evaluates, each gated on a name
//! the hidden file may have rewritten and each writing an output no other
//! route, and not the hidden file, writes:
//!
//! - a property's own gate;
//! - a `<PropertyGroup>`'s gate;
//! - a `<Choose>`'s `<When>`s, with or without an `<Otherwise>`, among gates
//!   decided either way and gates the walk cannot decide;
//! - an `<Import>`'s gate, and an `<ImportGroup>`'s, over a sibling file that
//!   writes the output;
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
/// Every name read back: each route's output, the gates, the global, and
/// copies of the outputs and the global made after every route.
const READ: &[&str] = &[
    "ROwn",
    "RGroup",
    "RChoose",
    "RImport",
    "RImportGroup",
    "RUnsupported",
    "Fresh",
    "Gate",
    "Flag",
    "G",
    "CopyAll",
    "CopyG",
];

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

impl Route {
    /// The name only this route writes.
    fn output(self) -> &'static str {
        match self {
            Route::OwnGate => "ROwn",
            Route::Group => "RGroup",
            Route::Choose => "RChoose",
            Route::Import => "RImport",
            Route::ImportGroup => "RImportGroup",
            Route::UnsupportedGroup => "RUnsupported",
        }
    }

    /// The sibling file an import route takes, writing its output.
    fn side(self) -> Option<&'static str> {
        match self {
            Route::Import => Some("side_import.props"),
            Route::ImportGroup => Some("side_group.props"),
            _ => None,
        }
    }
}

/// A gate on a name the hidden file may rewrite.
fn stale_gate(rng: &mut SplitMix64) -> String {
    let name = rng.pick(GATES);
    let value = rng.pick(&["yes", "no", ""]);
    let op = rng.pick(&["==", "!="]);
    format!(" Condition=\"'$({name})' {op} '{value}'\"")
}

/// A route's gate: mostly a stale one; now and then one decided on certain
/// values, under which the walk must go on committing what the route leaves
/// alone.
fn route_gate(rng: &mut SplitMix64) -> String {
    if rng.below(4) == 0 {
        certain_gate(rng).to_owned()
    } else {
        stale_gate(rng)
    }
}

/// A gate decided on certain values, either way.
fn certain_gate(rng: &mut SplitMix64) -> &'static str {
    rng.pick(&[" Condition=\"'k' == 'k'\"", " Condition=\"'k' == 'j'\""])
}

fn literal(rng: &mut SplitMix64) -> &'static str {
    rng.pick(&["yes", "no", "", "v1", "v2"])
}

/// A write of `name`, now and then under a gate decided on certain values.
fn write_output(rng: &mut SplitMix64, name: &str, out: &mut String) {
    let value = rng.pick(&["w1", "w2", "", "$(Gate)", "$(ROwn)x"]);
    let own = if rng.below(4) == 0 {
        certain_gate(rng)
    } else {
        ""
    };
    let _ = write!(out, "<{name}{own}>{value}</{name}>");
}

fn route(rng: &mut SplitMix64, route: Route, out: &mut String) {
    let name = route.output();
    match route {
        Route::OwnGate => {
            let _ = write!(
                out,
                "<PropertyGroup><{name}{}>own</{name}></PropertyGroup>",
                route_gate(rng)
            );
        }
        Route::Group => {
            let _ = write!(out, "<PropertyGroup{}>", route_gate(rng));
            write_output(rng, name, out);
            out.push_str("</PropertyGroup>");
        }
        Route::Choose => choose(rng, name, 0, out),
        Route::Import => {
            let _ = write!(
                out,
                "<Import Project=\"{}\"{} />",
                route.side().expect("an import route"),
                route_gate(rng)
            );
        }
        Route::ImportGroup => {
            let _ = write!(out, "<ImportGroup{}>", route_gate(rng));
            for _ in 0..1 + rng.below(2) {
                let own = if rng.below(3) == 0 {
                    certain_gate(rng)
                } else {
                    ""
                };
                let _ = write!(
                    out,
                    "<Import Project=\"{}\"{own} />",
                    route.side().expect("an import route")
                );
            }
            out.push_str("</ImportGroup>");
        }
        Route::UnsupportedGroup => {
            let _ = write!(
                out,
                "<PropertyGroup Condition=\"{UNDECIDABLE}\"><{name}{}>unsupported</{name}></PropertyGroup>",
                route_gate(rng)
            );
        }
    }
}

/// A `<Choose>` writing `name` in its branches, nesting one more inside a
/// branch now and then.
fn choose(rng: &mut SplitMix64, name: &str, depth: usize, out: &mut String) {
    out.push_str("<Choose>");
    for _ in 0..1 + rng.below(3) {
        // Mostly stale gates; now and then one the walk cannot decide at all,
        // or one decided on certain values either way.
        let gate = match rng.below(6) {
            0 => format!(" Condition=\"{UNDECIDABLE}\""),
            1 => certain_gate(rng).to_owned(),
            _ => stale_gate(rng),
        };
        let _ = write!(out, "<When{gate}>");
        branch(rng, name, depth, out);
        out.push_str("</When>");
    }
    if rng.below(2) == 0 {
        out.push_str("<Otherwise>");
        branch(rng, name, depth, out);
        out.push_str("</Otherwise>");
    }
    out.push_str("</Choose>");
}

/// A `<Choose>` branch's body. Now and then it writes `Fresh` before a write
/// gated on it, which only a branch taken whole can run: judged on the value
/// from before the branch, the gate would rule the write out.
fn branch(rng: &mut SplitMix64, name: &str, depth: usize, out: &mut String) {
    let group = if rng.below(4) == 0 {
        certain_gate(rng)
    } else {
        ""
    };
    let _ = write!(out, "<PropertyGroup{group}>");
    if rng.below(3) == 0 {
        let _ = write!(
            out,
            "<Fresh>yes</Fresh><{name} Condition=\"'$(Fresh)' == 'yes'\">enabled</{name}>"
        );
    } else {
        write_output(rng, name, out);
    }
    out.push_str("</PropertyGroup>");
    if depth == 0 && rng.below(4) == 0 {
        choose(rng, name, depth + 1, out);
    }
}

struct Case {
    project: String,
    hidden: String,
    /// Each import route's sibling file, by name.
    sides: Vec<(&'static str, String)>,
    routes: BTreeSet<Route>,
}

fn case(rng: &mut SplitMix64) -> Case {
    // What the walk holds before the hidden file: the gate names.
    let mut project = String::from("<Project><PropertyGroup>");
    for name in GATES {
        let _ = write!(project, "<{name}>{}</{name}>", literal(rng));
    }
    project.push_str("</PropertyGroup>");
    let _ = write!(
        project,
        "<Import Project=\"hidden.props\" Condition=\"{UNDECIDABLE}\" />"
    );
    // The outputs bound after it are fresh, so the walk commits them unless a
    // route below leaves them in doubt; the gate names stay stale. So is
    // `Fresh`, which only `<Choose>` branches write.
    project.push_str("<PropertyGroup><Fresh>no</Fresh>");
    for route in ROUTES {
        if rng.below(4) != 0 {
            let name = route.output();
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
    let all: Vec<String> = ROUTES
        .iter()
        .map(|route| format!("$({})", route.output()))
        .collect();
    let _ = write!(
        project,
        "<PropertyGroup><CopyAll>{}</CopyAll><CopyG>$(G)</CopyG></PropertyGroup></Project>",
        all.join("|")
    );

    let local = rng.below(3) == 0;
    let mut hidden = String::from(if local {
        "<Project TreatAsLocalProperty=\"G\"><PropertyGroup><G>local</G>"
    } else {
        "<Project><PropertyGroup>"
    });
    for name in GATES {
        if rng.below(4) != 0 {
            let _ = write!(hidden, "<{name}>{}</{name}>", literal(rng));
        }
    }
    hidden.push_str("</PropertyGroup></Project>");

    let sides = ROUTES
        .iter()
        .filter_map(|route| {
            let side = route.side()?;
            let mut text = String::from("<Project><PropertyGroup>");
            write_output(rng, route.output(), &mut text);
            text.push_str("</PropertyGroup></Project>");
            Some((side, text))
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
    /// Per route: cases holding it where MSBuild's value of its output moved
    /// across the globals, which only the route can move.
    live: BTreeMap<Route, usize>,
    /// Per route: cases holding it where the walk still committed its output,
    /// so declining is not all the walk does there.
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
        for (name, side) in &case.sides {
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
                            let sides: Vec<String> = case
                                .sides
                                .iter()
                                .map(|(name, text)| format!("{name}: {text}"))
                                .collect();
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
                                    sides.join("\n")
                                ),
                            });
                        }
                    }
                }
            }
        }
        for route in &case.routes {
            let output = route.output();
            if theirs_by_name
                .get(output)
                .is_some_and(|values| values.len() > 1)
            {
                *census.live.entry(*route).or_default() += 1;
            }
            if ours_by_name.contains(output) {
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
    let census = sweep(&mut oracle, &mut rng, 800, &mut violations);
    eprintln!("stale gates: {census:?}");
    assert_none(violations);
    // Anti-vacuity: every route moves its own output in MSBuild across the
    // globals in some cases, and leaves it committed in others.
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

/// A pinned shape: what it shows, the project, `hidden.props`, `side0.props`,
/// and what MSBuild ends with when the hidden file is taken.
type Shape = (
    &'static str,
    String,
    &'static str,
    &'static str,
    &'static [(&'static str, &'static str)],
);

/// The four shapes of #1037, an import and an import group taken on a stale
/// gate, and a `<Choose>` branch decided on one before an undecided gate, each
/// with what MSBuild ends with when the hidden file is taken (`G=x`): the walk
/// must commit that or nothing.
#[test]
fn issue_1037_shapes_are_exact_or_declined() {
    let hidden_gate = format!("<Import Project=\"hidden.props\" Condition=\"{UNDECIDABLE}\" />");
    let gate_yes = "<Project><PropertyGroup><Gate>yes</Gate></PropertyGroup></Project>";
    let gate_no = "<Project><PropertyGroup><Gate>no</Gate></PropertyGroup></Project>";
    let shapes: Vec<Shape> = vec![
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
