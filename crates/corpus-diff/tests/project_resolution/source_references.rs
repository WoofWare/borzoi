//! D1(G, C), the project-graph oracle held to itself
//! (`borzoi_oracle_harness::project_graph`): over generated graphs G, FCS
//! checking a consumer B with each referenced project from source (an
//! `FSharpReference` whose `-r:` names no file) answers, in currency C (B's
//! whole-project file records and diagnostics), exactly what it answers with
//! each referenced project as the DLL FCS's compiler built on the same
//! argument vector. Its one assumption: FCS's check and FCS's compile agree
//! on one argument vector. Later stages that hold a DLL-derived oracle to the
//! source walk rest on this, each adding D1 in its own currency.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use borzoi_corpus_diff::{FcsInvokeError, ProjectGraphOracle};
use borzoi_oracle_harness::project_graph::{
    FixtureFile, FixtureProject, GraphResponse, PlainName, ProjectGraphFixture, Target,
    framework_references,
};
use serde_json::Value;

use super::source_reference_gen::{
    ANCHOR_USE, Case, DEFINED_USE, LIBRARY_DEFINE, anchor_module, consumer_files, generate, kinds,
    library_files, middle_files,
};

fn name(s: &str) -> PlainName {
    PlainName::new(s).expect("a plain name")
}

fn project(n: &str, sources: Vec<(String, String)>, refs: &[&str]) -> FixtureProject {
    FixtureProject {
        project_refs: refs.iter().map(|r| name(r)).collect(),
        ..FixtureProject::new(
            name(n),
            sources
                .into_iter()
                .map(|(name, text)| FixtureFile { name, text })
                .collect(),
        )
    }
}

/// The uses of every checked file in `response`.
fn uses(response: &GraphResponse) -> impl Iterator<Item = &Value> {
    response
        .files
        .iter()
        .flat_map(|f| f["Uses"].as_array().into_iter().flatten())
}

/// The error-severity diagnostics of every checked file in `response`.
fn errors(response: &GraphResponse) -> Vec<&Value> {
    response
        .files
        .iter()
        .flat_map(|f| f["Diagnostics"].as_array().into_iter().flatten())
        .filter(|d| d["Severity"] == "Error")
        .collect()
}

fn binds(response: &GraphResponse, full_name: &str, assembly: &str) -> bool {
    uses(response).any(|u| u["FullName"] == full_name && u["Assembly"] == assembly)
}

/// The elements of `xs` that `ys` does not match, as a multiset.
fn unmatched(xs: &[Value], ys: &[Value]) -> Vec<String> {
    let mut pool: BTreeMap<String, usize> = BTreeMap::new();
    for y in ys {
        *pool.entry(y.to_string()).or_default() += 1;
    }
    xs.iter()
        .map(Value::to_string)
        .filter(|x| match pool.get_mut(x) {
            Some(n) if *n > 0 => {
                *n -= 1;
                false
            }
            _ => true,
        })
        .collect()
}

/// Where two answers differ in currency C: the whole-project diagnostics,
/// and each file's records and diagnostics, as multisets.
fn answer_diff(source: &GraphResponse, dll: &GraphResponse) -> Vec<String> {
    let mut out = Vec::new();
    for x in unmatched(&source.diagnostics, &dll.diagnostics) {
        out.push(format!("project diagnostic only from source: {x}"));
    }
    for y in unmatched(&dll.diagnostics, &source.diagnostics) {
        out.push(format!("project diagnostic only with the DLL: {y}"));
    }
    if source.files.len() != dll.files.len() {
        out.push(format!(
            "{} files from source, {} with the DLL",
            source.files.len(),
            dll.files.len()
        ));
    }
    for (s, d) in source.files.iter().zip(&dll.files) {
        // Every record carries all three fields: a missing one is not an
        // empty one.
        let field_of = |record: &'_ Value, field: &str| -> Result<Vec<Value>, String> {
            record[field]
                .as_array()
                .cloned()
                .ok_or_else(|| format!("a file record has no {field} array: {record}"))
        };
        let (Some(path), Some(dll_path)) = (s["Path"].as_str(), d["Path"].as_str()) else {
            out.push(format!("a file record has no Path: {s} / {d}"));
            continue;
        };
        if path != dll_path {
            out.push(format!(
                "file {path} from source is {dll_path} with the DLL"
            ));
            continue;
        }
        for field in ["Diagnostics", "Uses"] {
            let (xs, ys) = match (field_of(s, field), field_of(d, field)) {
                (Ok(xs), Ok(ys)) => (xs, ys),
                (Err(e), _) | (_, Err(e)) => {
                    out.push(e);
                    continue;
                }
            };
            let (xs, ys) = (&xs, &ys);
            for x in unmatched(xs, ys) {
                out.push(format!("{path} {field} only from source: {x}"));
            }
            for y in unmatched(ys, xs) {
                out.push(format!("{path} {field} only with the DLL: {y}"));
            }
        }
    }
    out
}

/// One D1 comparison: `check`'s answer with every project of its closure
/// from source, and where it differs from the answer with every one as the
/// DLL FCS's compiler built.
struct D1 {
    source: GraphResponse,
    /// Where the two disagree, or a premise failed.
    problems: Vec<String>,
}

/// Compile every project of `check`'s closure, dependencies first, each
/// against the DLLs compiled before it. A compile error is a fixture bug.
fn compile_closure(
    oracle: &mut ProjectGraphOracle,
    fixture: &ProjectGraphFixture,
    check: &PlainName,
) -> BTreeMap<PlainName, PathBuf> {
    let framework = framework_references();
    let mut compiled = BTreeMap::new();
    for q in fixture.closure(check) {
        let answer = oracle
            .compile(&fixture.compile_request(&q, framework, &compiled))
            .unwrap_or_else(|e| panic!("compile {q}: {e}"));
        let errors: Vec<&Value> = answer.errors().collect();
        assert!(errors.is_empty(), "{q} does not compile: {errors:#?}");
        let output = answer
            .output
            .unwrap_or_else(|| panic!("{q} compiled without an output"));
        assert!(output.is_file(), "{q}: no {}", output.display());
        compiled.insert(q, output);
    }
    compiled
}

/// [`D1`] for `check` in `fixture`. Premises, each a problem when broken:
/// the source answer reads every project of the closure from source (and
/// FCS's check of each finds no error, since each compiled), and the DLL
/// answer reads none.
fn d1(oracle: &mut ProjectGraphOracle, fixture: &ProjectGraphFixture, check: &PlainName) -> D1 {
    let framework = framework_references();
    let compiled = compile_closure(oracle, fixture, check);
    let source = oracle
        .check(&fixture.request(check, framework, &BTreeMap::new()))
        .unwrap_or_else(|e| panic!("the source check of {check} failed: {e}"));
    let dll = oracle
        .check(&fixture.request(check, framework, &compiled))
        .unwrap_or_else(|e| panic!("the DLL check of {check} failed: {e}"));
    let mut problems = answer_diff(&source, &dll);
    let closure: BTreeSet<String> = fixture
        .closure(check)
        .iter()
        .map(|q| q.as_str().to_owned())
        .collect();
    let from_source: BTreeSet<String> = source.referenced.iter().map(|r| r.id.clone()).collect();
    if from_source != closure {
        problems.push(format!(
            "the source answer read {from_source:?} from source, the closure is {closure:?}"
        ));
    }
    if !dll.referenced.is_empty() {
        problems.push("the DLL answer read a project from source".to_owned());
    }
    for r in &source.referenced {
        problems.extend(r.errors().map(|e| format!("{} from source: {e}", r.id)));
    }
    D1 { source, problems }
}

/// The default run's seed, fixed so it is the same run everywhere.
const DEFAULT_SEED: u64 = 0x005e_ed0f_5ce5;

/// How many cases the default run generates.
const DEFAULT_CASES: usize = 24;

/// Indices of [`DEFAULT_SEED`] beyond [`DEFAULT_CASES`] the default run adds,
/// so that every kind of qualified use binds into A somewhere in it.
const PINNED_CASES: &[usize] = &[77, 92, 129];

/// A generated case's fixture: A (under [`LIBRARY_DEFINE`]), the middle
/// project when there is one, and B.
fn case_fixture(case: &Case) -> ProjectGraphFixture {
    let library = case.library.as_str();
    let mut projects = vec![FixtureProject {
        defines: vec![LIBRARY_DEFINE.to_owned()],
        ..project(library, library_files(case), &[])
    }];
    let consumer_refs: Vec<&str> = match middle_files(case) {
        Some((middle, files)) => {
            projects.push(project(&middle, files, &[library]));
            vec![case.middle.as_deref().expect("a middle case")]
        }
        None => vec![library],
    };
    projects.push(project(
        &case.consumer,
        consumer_files(case),
        &consumer_refs,
    ));
    ProjectGraphFixture::materialise(projects).expect("a generated graph")
}

/// The lines of B's `Use.fs`, 1-based, on which `answer` has an error.
fn error_lines(answer: &GraphResponse) -> BTreeSet<u64> {
    errors(answer)
        .into_iter()
        .filter_map(|d| d["Range"]["Start"]["Line"].as_u64())
        .collect()
}

/// What one case's uses cover, from FCS's own records. A use tag is a
/// declaration kind, marked when its name collides with FSharp.Core's; bare
/// uses (and extension members called on a receiver) are left out, since
/// they may rightly bind elsewhere.
struct UseCoverage {
    /// Every qualified use's tag.
    made: BTreeSet<String>,
    /// The tags with a qualified use FCS accepted whose intended symbol
    /// binds into A.
    bound: BTreeSet<String>,
    /// Each qualified use of a non-colliding kind FCS accepted with no
    /// record of its intended symbol binding into A there. Such a use names
    /// A's item by a path no other assembly declares, so it can resolve
    /// nowhere else.
    unbound: Vec<String>,
}

fn use_coverage(case: &Case, source: &GraphResponse) -> UseCoverage {
    let text = &consumer_files(case)[0].1;
    let line_of = |u: &str| -> u64 {
        let i = text
            .lines()
            .position(|l| l == u)
            .expect("each use is a line of Use.fs");
        u64::try_from(i + 1).expect("a small file")
    };
    let bad = error_lines(source);
    // Whether a record on `line` of B's Use.fs is A's symbol `name`: the
    // symbol the generator wrote there, not merely any record of A (a
    // qualifier such as `N.M` would do).
    let binds_at = |line: u64, name: &str| {
        uses(source).any(|u| {
            u["Assembly"] == case.library.as_str()
                && u["Range"]["Start"]["Line"].as_u64() == Some(line)
                && u["Range"]["File"]
                    .as_str()
                    .is_some_and(|f| f.ends_with("/Use.fs"))
                && (u["SymbolName"] == name
                    || u["LogicalName"] == name
                    || u["FullName"]
                        .as_str()
                        .is_some_and(|f| f.ends_with(&format!(".{name}"))))
        })
    };
    let mut coverage = UseCoverage {
        made: BTreeSet::new(),
        bound: BTreeSet::new(),
        unbound: Vec::new(),
    };
    for ((u, tag), symbol) in case.uses.iter().zip(&case.use_tags).zip(&case.use_names) {
        if tag.ends_with("(bare)") {
            continue;
        }
        coverage.made.insert(tag.clone());
        let line = line_of(u);
        if bad.contains(&line) {
            continue;
        }
        if binds_at(line, symbol) {
            coverage.bound.insert(tag.clone());
        } else if !tag.ends_with("(colliding)") {
            coverage.unbound.push(format!("`{u}` ({tag}, {symbol})"));
        }
    }
    coverage
}

/// Run D1 over `cases` (each a seed and an index), failing on any
/// disagreement, broken premise or vacuous case, and unless every kind of
/// qualified use the run makes binds into A somewhere in it.
fn d1_over_generated_cases(cases: &[(u64, usize)]) {
    println!("D1 over {} generated cases: {cases:?}", cases.len());
    let mut oracle = ProjectGraphOracle::default();
    let mut failures = Vec::new();
    let mut into_library: BTreeMap<String, usize> = BTreeMap::new();
    let (mut made, mut bound) = (BTreeSet::new(), BTreeSet::new());
    for &(seed, i) in cases {
        let case = generate(seed, i);
        let fixture = case_fixture(&case);
        let D1 {
            source,
            mut problems,
        } = d1(&mut oracle, &fixture, &name(&case.consumer));
        let anchor = format!("{}.anchor", anchor_module(&case));
        if !binds(&source, &anchor, &case.library) {
            problems.push(format!(
                "`{ANCHOR_USE}{anchor}` does not bind into {}",
                case.library
            ));
        }
        // The define-dependent export binds into A at the type A's define
        // gives it, so a define lost on both sides fails too.
        let defined = format!("{}.defined", anchor_module(&case));
        let defined_type = uses(&source)
            .find(|u| {
                u["FullName"] == defined.as_str()
                    && u["Assembly"] == case.library.as_str()
                    && u["IsFromDefinition"] == false
            })
            .and_then(|u| u["Value"]["TypeCanon"].as_str());
        if !defined_type.is_some_and(|t| t.contains("Int32")) {
            problems.push(format!(
                "`{DEFINED_USE}{defined}` does not bind into {} as the int {LIBRARY_DEFINE} makes it: {defined_type:?}",
                case.library
            ));
        }
        if let Some(middle) = &case.middle
            && !binds(&source, &format!("{middle}.token"), middle)
        {
            problems.push(format!("`{middle}.token` does not bind into {middle}"));
        }
        let coverage = use_coverage(&case, &source);
        for use_ in &coverage.unbound {
            problems.push(format!(
                "the accepted qualified use {use_} does not bind into {}",
                case.library
            ));
        }
        made.extend(coverage.made);
        bound.extend(coverage.bound);
        if !problems.is_empty() {
            let sources: String = library_files(&case)
                .into_iter()
                .chain(middle_files(&case).into_iter().flat_map(|(_, f)| f))
                .chain(consumer_files(&case))
                .map(|(n, t)| format!("--- {n}\n{t}"))
                .collect();
            failures.push(format!(
                "case {i} of seed {seed:#x}:\n  {}\n{sources}",
                problems.join("\n  ")
            ));
        }
        for u in uses(&source).filter(|u| u["Assembly"] == case.library.as_str()) {
            let kind = u["SymbolKind"].as_str().unwrap_or("?").to_owned();
            *into_library.entry(kind).or_default() += 1;
        }
    }
    println!("uses binding into the library by kind: {into_library:?}");
    println!("use kinds binding into the library: {bound:?}");
    let never: Vec<&String> = made.difference(&bound).collect();
    if !never.is_empty() {
        failures.push(format!(
            "no qualified use of these kinds binds into the library in the run: {never:?}"
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// D1 over the default run.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn source_references_equal_compiled_dlls_on_generated_graphs() {
    let cases: Vec<(u64, usize)> = (0..DEFAULT_CASES)
        .chain(PINNED_CASES.iter().copied())
        .map(|i| (DEFAULT_SEED, i))
        .collect();
    d1_over_generated_cases(&cases);
}

/// D1 over a wider run: `BORZOI_SOURCE_REF_SEED` and `BORZOI_SOURCE_REF_CASES`
/// choose it (default: the default seed's first 200 cases).
#[test]
#[ignore = "deep: hundreds of FCS compiles; run by hand"]
fn deep_source_references_equal_compiled_dlls_on_generated_graphs() {
    let seed = std::env::var("BORZOI_SOURCE_REF_SEED").map_or(DEFAULT_SEED, |s| {
        s.parse().expect("BORZOI_SOURCE_REF_SEED is a u64")
    });
    let count = std::env::var("BORZOI_SOURCE_REF_CASES").map_or(200, |s| {
        s.parse().expect("BORZOI_SOURCE_REF_CASES is a count")
    });
    let cases: Vec<(u64, usize)> = (0..count).map(|i| (seed, i)).collect();
    d1_over_generated_cases(&cases);
}

/// The generator's coverage over the default run: every declaration kind A
/// can export occurs, and so does each dimension that decides what B sees.
/// Pure, so it runs without FCS.
#[test]
fn the_generated_graphs_cover_every_declaration_kind() {
    let mut seen = BTreeSet::new();
    for i in 0..DEFAULT_CASES {
        seen.extend(kinds(&generate(DEFAULT_SEED, i)));
    }
    let want = [
        "namespace",
        "module",
        "auto-open module",
        "rqa module",
        "value",
        "literal",
        "function",
        "compiled-name function",
        "active pattern",
        "record",
        "union",
        "class",
        "interface",
        "enum",
        "delegate",
        "struct",
        "abbreviation",
        "exception",
        "measure",
        "optional extension",
        "C#-style extension",
        "fsi-hidden item",
        "internal item",
        "IVT to the consumer",
        "IVT to another assembly",
        "assembly-level auto-open",
        "transitive reference through a middle project",
    ];
    let missing: Vec<&str> = want.iter().copied().filter(|k| !seen.contains(k)).collect();
    assert!(
        missing.is_empty(),
        "never generated: {missing:?}; seen {seen:?}"
    );
}

/// The must-bind-internal cell, and D1 over it: a friend's use of an
/// internal binds only when the consumer's assembly name is the one the
/// library's `InternalsVisibleTo` names.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn a_friend_binds_an_internal_only_under_its_assembly_name() {
    let friend = |assembly: &str| {
        let library = project(
            "Ay",
            vec![(
                "Lib.fs".into(),
                "namespace Alpha\n\nmodule internal Hidden =\n    let secret = 42\n\n\
                 module Visible =\n    let shown = 1\n\n\
                 module Attributes =\n    \
                 [<assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"Bee\")>]\n    \
                 do ()\n"
                    .into(),
            )],
            &[],
        );
        let consumer = FixtureProject {
            assembly_name: name(assembly),
            ..project(
                "Bee",
                vec![(
                    "Use.fs".into(),
                    "module Use\n\nlet s = Alpha.Hidden.secret\nlet v = Alpha.Visible.shown\n"
                        .into(),
                )],
                &["Ay"],
            )
        };
        ProjectGraphFixture::materialise(vec![library, consumer]).expect("a graph")
    };
    let mut oracle = ProjectGraphOracle::default();
    let named = d1(&mut oracle, &friend("Bee"), &name("Bee"));
    assert!(named.problems.is_empty(), "{}", named.problems.join("\n"));
    assert!(
        binds(&named.source, "Alpha.Hidden.secret", "Ay"),
        "{:#?}",
        named.source
    );
    assert!(
        errors(&named.source).is_empty() && named.source.errors().next().is_none(),
        "{:#?}",
        named.source
    );

    let other = d1(&mut oracle, &friend("NotBee"), &name("Bee"));
    assert!(other.problems.is_empty(), "{}", other.problems.join("\n"));
    assert!(
        error_lines(&other.source).contains(&3),
        "under another assembly name the internal is inaccessible: {:#?}",
        other.source
    );
}

/// Two references that declare one name: FCS takes the later one, so a
/// project passed from source keeps its DLL's place in the reference order.
/// Both from source, both DLLs, and each mix bind alike.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn a_reference_from_source_keeps_its_place_in_the_order() {
    let declares = |n: &str| {
        project(
            n,
            vec![(
                "Lib.fs".into(),
                format!("namespace Duplicate\n\nmodule Mod =\n    let x = \"{n}\"\n"),
            )],
            &[],
        )
    };
    let fixture = ProjectGraphFixture::materialise(vec![
        declares("Ay"),
        declares("Zed"),
        project(
            "App",
            vec![(
                "Use.fs".into(),
                "module Use\n\nlet y = Duplicate.Mod.x\n".into(),
            )],
            &["Ay", "Zed"],
        ),
    ])
    .expect("a graph");
    let mut oracle = ProjectGraphOracle::default();
    let compiled = compile_closure(&mut oracle, &fixture, &name("App"));
    let framework = framework_references();
    for from_dll in [
        BTreeMap::new(),
        compiled.clone(),
        compiled
            .iter()
            .filter(|(q, _)| q.as_str() == "Ay")
            .map(|(q, p)| (q.clone(), p.clone()))
            .collect(),
        compiled
            .iter()
            .filter(|(q, _)| q.as_str() == "Zed")
            .map(|(q, p)| (q.clone(), p.clone()))
            .collect(),
    ] {
        let answer = oracle
            .check(&fixture.request(&name("App"), framework, &from_dll))
            .expect("the graph oracle answers");
        let dlls: Vec<&str> = from_dll.keys().map(PlainName::as_str).collect();
        assert!(
            binds(&answer, "Duplicate.Mod.x", "Zed") && !binds(&answer, "Duplicate.Mod.x", "Ay"),
            "with {dlls:?} as DLLs, the later reference wins: {answer:#?}"
        );
    }
}

/// The file records describe the code the compile compiles. FCS's per-file
/// check defines `EDITING`, which the compile does not; here A and B each
/// say one thing under `EDITING` and another without, and the records must
/// read the compiled branch.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn file_records_read_the_branch_the_build_compiled() {
    let fixture = ProjectGraphFixture::materialise(vec![
        project(
            "Lib",
            vec![(
                "Lib.fs".into(),
                "module Lib\n\n#if EDITING\nlet x = \"\"\n#else\nlet x = 1\n#endif\n".into(),
            )],
            &[],
        ),
        project(
            "App",
            vec![(
                "App.fs".into(),
                "module App\n\n#if EDITING\nlet onlyEditing : string = Lib.x\n#else\nlet onlyBuild : int = Lib.x\n#endif\n"
                    .into(),
            )],
            &["Lib"],
        ),
    ])
    .expect("a graph");
    let mut oracle = ProjectGraphOracle::default();
    let D1 {
        source, problems, ..
    } = d1(&mut oracle, &fixture, &name("App"));
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    assert!(
        errors(&source).is_empty() && source.errors().next().is_none(),
        "no record holds an error: {source:#?}"
    );
    let named = |n: &str| uses(&source).any(|u| u["FullName"] == format!("App.{n}"));
    assert!(
        named("onlyBuild"),
        "the compiled branch is recorded: {source:#?}"
    );
    assert!(
        !named("onlyEditing"),
        "the EDITING branch is not: {source:#?}"
    );
}

/// Puts `path`'s modification time back to `stamp`.
fn set_modified(path: &Path, stamp: std::time::SystemTime) {
    std::fs::File::options()
        .write(true)
        .open(path)
        .and_then(|f| f.set_modified(stamp))
        .unwrap_or_else(|e| panic!("put {}'s timestamp back: {e}", path.display()));
}

/// The resident oracle never answers from anything an earlier request read:
/// a referenced project's source, and a referenced DLL, each rewritten with
/// its timestamp put back, are read afresh.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn a_rewritten_reference_is_read_afresh_whatever_its_timestamp() {
    let lib = |ty: &str, value: &str| {
        project(
            "Lib",
            vec![(
                "Lib.fs".into(),
                format!("module Lib\n\nlet x : {ty} = {value}\n"),
            )],
            &[],
        )
    };
    let app = || {
        project(
            "App",
            vec![("Use.fs".into(), "module Use\n\nlet y = Lib.x\n".into())],
            &["Lib"],
        )
    };
    let fixture = ProjectGraphFixture::materialise(vec![lib("int", "1"), app()]).expect("a graph");
    let rewritten =
        ProjectGraphFixture::materialise(vec![lib("string", "\"\""), app()]).expect("a graph");
    let type_of_x = |answer: &GraphResponse| -> String {
        uses(answer)
            .find(|u| u["FullName"] == "Lib.x" && u["IsFromDefinition"] == false)
            .and_then(|u| u["Value"]["TypeCanon"].as_str())
            .unwrap_or_else(|| panic!("no typed use of Lib.x: {answer:#?}"))
            .to_owned()
    };
    let mut oracle = ProjectGraphOracle::default();
    let framework = framework_references();
    let compiled = compile_closure(&mut oracle, &fixture, &name("App"));
    let source = fixture.request(&name("App"), framework, &BTreeMap::new());
    let dll = fixture.request(&name("App"), framework, &compiled);
    let mut check = |request| type_of_x(&oracle.check(request).expect("the graph oracle answers"));
    assert!(check(&source).contains("Int32"));
    assert!(check(&dll).contains("Int32"));

    let lib_fs = fixture.paths(&name("Lib")).remove(0);
    let stamp = std::fs::metadata(&lib_fs)
        .and_then(|m| m.modified())
        .expect("a timestamp");
    std::fs::write(&lib_fs, "module Lib\n\nlet x : string = \"\"\n").expect("rewrite");
    set_modified(&lib_fs, stamp);
    let after = check(&source);
    assert!(
        after.contains("String"),
        "the source rewrite must be seen: {after}"
    );

    let mut other = ProjectGraphOracle::default();
    let rewritten_dll = compile_closure(&mut other, &rewritten, &name("App"));
    let dll_path = &compiled[&name("Lib")];
    let stamp = std::fs::metadata(dll_path)
        .and_then(|m| m.modified())
        .expect("a timestamp");
    std::fs::copy(&rewritten_dll[&name("Lib")], dll_path).expect("rewrite the DLL");
    set_modified(dll_path, stamp);
    let after = check(&dll);
    assert!(
        after.contains("String"),
        "the DLL rewrite must be seen: {after}"
    );

    // Two compiles in a row, the reference rewritten between them and no
    // check to clear anything: the second must see the rewrite too.
    let pinned = ProjectGraphFixture::materialise(vec![
        lib("int", "1"),
        project(
            "Pin",
            vec![(
                "Pin.fs".into(),
                "module Pin\n\nlet y : int = Lib.x\n".into(),
            )],
            &["Lib"],
        ),
    ])
    .expect("a graph");
    let mut two = ProjectGraphOracle::default();
    let compiled = compile_closure(&mut two, &pinned, &name("Pin"));
    let pin = pinned.compile_request(&name("Pin"), framework, &compiled);
    let first = two.compile(&pin).expect("the compiler answers");
    assert_eq!(first.errors().count(), 0, "{first:#?}");
    let dll_path = &compiled[&name("Lib")];
    let stamp = std::fs::metadata(dll_path)
        .and_then(|m| m.modified())
        .expect("a timestamp");
    std::fs::copy(&rewritten_dll[&name("Lib")], dll_path).expect("rewrite the DLL");
    set_modified(dll_path, stamp);
    let second = two.compile(&pin).expect("the compiler answers");
    assert!(
        second.errors().count() > 0,
        "the second compile must read the rewritten DLL, where `x` is a string: {second:#?}"
    );
}

/// A DLL reference is an assembly, read from its manifest at the boundary:
/// `fcs-dump` refuses a DLL and a project reference of one assembly name
/// (which leave FCS to pick one, and which the request type cannot express),
/// a DLL that does not exist (FCS would check against its own FSharp.Core),
/// a DLL whose manifest names another assembly than its file, and a FIFO
/// named like a DLL (unopened). The graph check runs through the guarded
/// project check the other project-check oracles use, so it also refuses two
/// sources FCS takes for one file and a line directive. A raw request is only
/// ever a check.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn the_oracle_refuses_references_it_cannot_identify() {
    let fixture = ProjectGraphFixture::materialise(vec![
        project(
            "Lib",
            vec![("Lib.fs".into(), "module Lib\n\nlet x = 1\n".into())],
            &[],
        ),
        project(
            "App",
            vec![("Use.fs".into(), "module Use\n\nlet y = Lib.x\n".into())],
            &["Lib"],
        ),
    ])
    .expect("a graph");
    let mut oracle = ProjectGraphOracle::default();
    let compiled = compile_closure(&mut oracle, &fixture, &name("App"));
    let valid: Value = serde_json::from_str(
        &fixture
            .request(&name("App"), framework_references(), &BTreeMap::new())
            .to_json_line(),
    )
    .expect("json");
    assert!(oracle.check_value(&valid).is_ok());
    // App references Lib's DLL and Lib from source.
    let mut both = valid.clone();
    let lib_dll = compiled[&name("Lib")].to_str().expect("UTF-8").to_owned();
    both["projects"][1]["references"]
        .as_array_mut()
        .expect("references")
        .insert(0, serde_json::json!({ "dll": lib_dll }));
    match oracle.check_value(&both) {
        Err(FcsInvokeError::Refused(why)) if why.contains("assembly") => {}
        other => panic!("two references of assembly Lib must be refused: {other:?}"),
    }
    // FSharp.Core named by a path that does not exist.
    let mut missing = valid.clone();
    for r in missing["projects"][1]["references"]
        .as_array_mut()
        .expect("references")
    {
        if r["dll"]
            .as_str()
            .is_some_and(|p| p.ends_with("/FSharp.Core.dll"))
        {
            r["dll"] = Value::String("/nonexistent/FSharp.Core.dll".to_owned());
        }
    }
    match oracle.check_value(&missing) {
        Err(FcsInvokeError::Refused(why)) if why.contains("does not exist") => {}
        other => panic!("a missing DLL must be refused: {other:?}"),
    }
    // Lib's DLL under another file name, beside Lib from source.
    let renamed = compiled[&name("Lib")].with_file_name("Renamed.dll");
    std::fs::copy(&compiled[&name("Lib")], &renamed).expect("copy the DLL");
    let mut aliased = valid.clone();
    aliased["projects"][1]["references"]
        .as_array_mut()
        .expect("references")
        .insert(
            0,
            serde_json::json!({ "dll": renamed.to_str().expect("UTF-8") }),
        );
    match oracle.check_value(&aliased) {
        Err(FcsInvokeError::Refused(why)) if why.contains("is assembly Lib") => {}
        other => panic!("a DLL named apart from its manifest must be refused: {other:?}"),
    }
    let mut compile = valid.clone();
    compile["op"] = Value::String("compile".to_owned());
    match oracle.check_value(&compile) {
        Err(FcsInvokeError::Refused(why)) if why.contains("must be a check") => {}
        other => panic!("a raw request is only a check: {other:?}"),
    }
    // A FIFO named like a DLL: refused before anything opens it.
    let fifo = fixture.root().join("Fifo.dll");
    let mut mkfifo = std::process::Command::new("mkfifo");
    mkfifo.arg(&fifo);
    let made = borzoi_spawn::BoundedCommand::new(mkfifo)
        .run()
        .expect("run mkfifo");
    assert!(made.status.success(), "mkfifo: {made:?}");
    let mut piped = valid.clone();
    piped["projects"][1]["references"]
        .as_array_mut()
        .expect("references")
        .insert(
            0,
            serde_json::json!({ "dll": fifo.to_str().expect("UTF-8") }),
        );
    match oracle.check_value(&piped) {
        Err(FcsInvokeError::Refused(why)) if why.contains("not a regular file") => {}
        other => panic!("a FIFO must be refused unopened: {other:?}"),
    }
    // Two sources FCS takes for one file (they differ by a soft hyphen).
    let use_fs = fixture.paths(&name("App")).remove(0);
    let conflated = use_fs.with_file_name("U\u{ad}se.fs");
    std::fs::write(&conflated, "module Use2\n").expect("write the second source");
    let mut twice = valid.clone();
    twice["projects"][1]["sources"]
        .as_array_mut()
        .expect("sources")
        .push(Value::String(conflated.to_str().expect("UTF-8").to_owned()));
    match oracle.check_value(&twice) {
        Err(FcsInvokeError::Refused(why)) if why.contains("one file to FCS") => {}
        other => panic!("sources FCS conflates must be refused: {other:?}"),
    }
    // A reference set missing the primary assembly: FCS would find one by
    // itself, so the oracle refuses what it resolved beyond the request.
    let mut short = valid.clone();
    short["projects"][1]["references"]
        .as_array_mut()
        .expect("references")
        .retain(|r| {
            !r["dll"]
                .as_str()
                .is_some_and(|p| p.ends_with("/System.Runtime.dll"))
        });
    for p in short["projects"].as_array_mut().expect("projects") {
        p["references"]
            .as_array_mut()
            .expect("references")
            .retain(|r| {
                !r["dll"]
                    .as_str()
                    .is_some_and(|p| p.ends_with("/System.Runtime.dll"))
            });
    }
    match oracle.check_value(&short) {
        Err(FcsInvokeError::Refused(why)) if why.contains("does not name") => {}
        other => panic!("an assembly FCS resolved by itself must be refused: {other:?}"),
    }
    // A FIFO named like a source.
    let fifo_fs = fixture.root().join("Fifo.fs");
    let mut mkfifo = std::process::Command::new("mkfifo");
    mkfifo.arg(&fifo_fs);
    let made = borzoi_spawn::BoundedCommand::new(mkfifo)
        .run()
        .expect("run mkfifo");
    assert!(made.status.success(), "mkfifo: {made:?}");
    let mut piped_source = valid.clone();
    piped_source["projects"][1]["sources"]
        .as_array_mut()
        .expect("sources")
        .insert(
            0,
            Value::String(fifo_fs.to_str().expect("UTF-8").to_owned()),
        );
    match oracle.check_value(&piped_source) {
        Err(FcsInvokeError::Refused(why)) if why.contains("not a regular file") => {}
        other => panic!("a FIFO source must be refused unopened: {other:?}"),
    }
    // A line directive, which moves the ranges the check reports elsewhere.
    std::fs::write(&use_fs, "module Use\n\n# 1 \"Other.fs\"\nlet y = Lib.x\n").expect("rewrite");
    match oracle.check_value(&valid) {
        Err(FcsInvokeError::Refused(why)) if why.contains("line directive") => {}
        other => panic!("a line directive must be refused: {other:?}"),
    }
}

/// An executable compiles under the same template a library does.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn an_executable_compiles() {
    let fixture = ProjectGraphFixture::materialise(vec![FixtureProject {
        target: Target::Exe,
        ..project(
            "Tool",
            vec![(
                "Main.fs".into(),
                "module Main\n\n[<EntryPoint>]\nlet main _ = 0\n".into(),
            )],
            &[],
        )
    }])
    .expect("a graph");
    let answer = ProjectGraphOracle::default()
        .compile(&fixture.compile_request(&name("Tool"), framework_references(), &BTreeMap::new()))
        .expect("the compiler answers");
    assert_eq!(answer.errors().count(), 0, "{answer:#?}");
    assert!(
        answer.output.as_ref().is_some_and(|o| o.is_file()),
        "{answer:#?}"
    );
}

/// A failed compile names no output, even where an earlier compile left a
/// DLL in place.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn a_failed_compile_names_no_output() {
    let fixture = ProjectGraphFixture::materialise(vec![
        project(
            "Lib",
            vec![("Lib.fs".into(), "module Lib\n\nlet x = 1\n".into())],
            &[],
        ),
        project(
            "App",
            vec![("Use.fs".into(), "module Use\n\nlet y = Lib.x\n".into())],
            &["Lib"],
        ),
    ])
    .expect("a graph");
    let mut oracle = ProjectGraphOracle::default();
    let compiled = compile_closure(&mut oracle, &fixture, &name("App"));
    assert!(compiled[&name("Lib")].is_file());
    let lib_fs = fixture.paths(&name("Lib")).remove(0);
    std::fs::write(&lib_fs, "module Lib\n\nlet x : int = \"\"\n").expect("break Lib");
    let answer = oracle
        .compile(&fixture.compile_request(&name("Lib"), framework_references(), &BTreeMap::new()))
        .expect("the compiler answers");
    assert!(answer.errors().count() > 0, "{answer:#?}");
    assert_eq!(answer.output, None, "{answer:#?}");
}

/// The #1001 shape, pinned: A declares its own `List` module in a namespace
/// B opens. `List.mine` binds into A and `List.map` into FSharp.Core, from
/// source as with the DLL.
#[test]
#[ignore = "drives FCS; use --ignored for oracle smoke"]
fn a_referenced_projects_own_list_module_binds_beside_fsharp_core() {
    let fixture = ProjectGraphFixture::materialise(vec![
        project(
            "Lib",
            vec![(
                "Lib.fs".into(),
                "namespace Lib\n\nmodule List =\n    let mine (x: int) = x\n\nmodule Seq =\n    let ours (x: int) = x\n"
                    .into(),
            )],
            &[],
        ),
        project(
            "App",
            vec![(
                "Use.fs".into(),
                "module Use\n\nopen Lib\n\nlet a = List.mine 1\nlet b = List.map id [ 1 ]\n\
                 let c = Seq.ours 1\nlet d = Seq.length [ 1 ]\n"
                    .into(),
            )],
            &["Lib"],
        ),
    ])
    .expect("a graph");
    let mut oracle = ProjectGraphOracle::default();
    let D1 {
        source, problems, ..
    } = d1(&mut oracle, &fixture, &name("App"));
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    assert!(
        errors(&source).is_empty() && source.errors().next().is_none(),
        "{source:#?}"
    );
    assert!(binds(&source, "Lib.List.mine", "Lib"), "{source:#?}");
    assert!(binds(&source, "Lib.Seq.ours", "Lib"), "{source:#?}");
    assert!(
        binds(
            &source,
            "Microsoft.FSharp.Collections.ListModule.map",
            "FSharp.Core"
        ) || uses(&source).any(|u| u["Assembly"] == "FSharp.Core"
            && u["FullName"]
                .as_str()
                .is_some_and(|n| n.ends_with("List.map"))),
        "List.map binds into FSharp.Core: {source:#?}"
    );
}
