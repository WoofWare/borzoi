//! The project-graph oracle (`fcs-dump uses-project-graph-batch`) against
//! itself: FCS with each F# project reference passed from source, as an IDE
//! passes it, must answer exactly what it answers with the reference built
//! fresh and passed as a DLL.
//!
//! A fresh DLL's signature is the same CCU signature the source reference
//! exports (`tcsCcuSig`, pickled), so the two readings can differ only where
//! FCS's IDE path and its compiler path read a project differently: the
//! assembly's name, its assembly-level attributes (`AutoOpen`,
//! `InternalsVisibleTo`), what a `.fsi` hides. Later stages hold borzoi's
//! source-derived surface to the built DLL's, and that oracle rests on this
//! equality.

use std::collections::BTreeMap;

use borzoi_corpus_diff::ProjectGraphOracle;
use borzoi_oracle_harness::project_graph::{
    FixtureFile, FixtureProject, GraphProject, GraphRequest, GraphResponse, PlainName,
    ProjectGraphFixture, build_fixtures,
};
use serde_json::Value;

use super::source_reference_gen::{
    ANCHOR_USE, Case, anchor_module, consumer_files, generate, kinds, library_files, middle_files,
};

fn name(s: &str) -> PlainName {
    PlainName::new(s).expect("a plain name")
}

fn files(sources: Vec<(String, String)>) -> Vec<FixtureFile> {
    sources
        .into_iter()
        .map(|(name, text)| FixtureFile { name, text })
        .collect()
}

/// The uses of every checked file in `response`.
fn uses(response: &GraphResponse) -> impl Iterator<Item = &Value> {
    response
        .files
        .iter()
        .flat_map(|f| f["Uses"].as_array().into_iter().flatten())
}

fn errors(response: &GraphResponse) -> Vec<&Value> {
    response
        .files
        .iter()
        .flat_map(|f| f["Diagnostics"].as_array().into_iter().flatten())
        .filter(|d| d["Severity"] == "Error")
        .collect()
}

/// A library granting its internals to `Bee`, and a consumer using one. The
/// consumer's last file is `Program.fs` and the library's `Lib.fs`, so FCS's
/// default assembly names (`Program`, `Lib`) match neither.
fn friend_fixture() -> ProjectGraphFixture {
    ProjectGraphFixture::materialise(vec![
        FixtureProject {
            name: name("Ay"),
            files: files(vec![(
                "Lib.fs".into(),
                "namespace Alpha\n\n\
                 module internal Hidden =\n    let secret = 42\n\n\
                 module Visible =\n    let shown = 1\n\n\
                 module Attributes =\n    \
                 [<assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"Bee\")>]\n    \
                 do ()\n"
                    .into(),
            )]),
            project_refs: Vec::new(),
            defines: Vec::new(),
        },
        FixtureProject {
            name: name("Bee"),
            files: files(vec![
                (
                    "Use.fs".into(),
                    "module Use\n\nlet s = Alpha.Hidden.secret\nlet v = Alpha.Visible.shown\n"
                        .into(),
                ),
                ("Program.fs".into(), "module Program\n\nlet z = 0\n".into()),
            ]),
            project_refs: vec![name("Ay")],
            defines: Vec::new(),
        },
    ])
    .expect("a graph")
}

/// `request` with the checked project renamed to `assembly`.
fn renamed(request: &GraphRequest, assembly: &str) -> GraphRequest {
    let projects: Vec<GraphProject> = request
        .projects()
        .iter()
        .map(|p| {
            let mut p = p.clone();
            if &p.id == request.check() {
                p.assembly_name = name(assembly);
            }
            p
        })
        .collect();
    GraphRequest::new(projects, request.check().clone()).expect("still a graph")
}

fn binds(response: &GraphResponse, full_name: &str, assembly: &str) -> bool {
    uses(response).any(|u| u["FullName"] == full_name && u["Assembly"] == assembly)
}

/// The must-bind-internal cell. A friend's use of an internal binds only when
/// both assembly names reach FCS: the library's, which its `-o:` sets and its
/// `InternalsVisibleTo` is matched against the consumer's, which the
/// consumer's `-o:` sets. It also pins that the referenced project's output
/// path is never written, so the oracle needs no build.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_friend_binds_an_internal_only_under_its_pinned_assembly_name() {
    let fixture = friend_fixture();
    let mut oracle = ProjectGraphOracle::default();
    let request = fixture.source_request(&name("Bee"));

    let friend = oracle.check(&request).expect("the graph oracle answers");
    assert_eq!(errors(&friend), Vec::<&Value>::new(), "{friend:#?}");
    assert!(
        binds(&friend, "Alpha.Hidden.secret", "Ay"),
        "the friend's use of an internal must bind into Ay: {friend:#?}"
    );
    let [library] = friend.referenced.as_slice() else {
        panic!("one referenced project: {:#?}", friend.referenced)
    };
    assert_eq!(library.assembly_name, "Ay");
    assert_eq!(library.errors().count(), 0, "{library:#?}");
    assert!(
        !library.output_path.exists(),
        "a source reference's output path is a name, never a file: {}",
        library.output_path.display()
    );

    // The control: renamed, the consumer is no friend, so the internal's use
    // (line 3) is an access error, and the public value's (line 4) is not.
    // FCS still records a use at an inaccessible name, so the records alone
    // do not tell the two apart.
    let stranger = oracle
        .check(&renamed(&request, "NotBee"))
        .expect("the graph oracle answers");
    let error_lines: Vec<u64> = errors(&stranger)
        .iter()
        .filter_map(|d| d["Range"]["Start"]["Line"].as_u64())
        .collect();
    assert!(
        !error_lines.is_empty() && error_lines.iter().all(|&l| l == 3),
        "a non-friend's use of the internal, and only it, is an error: {stranger:#?}"
    );
    assert!(binds(&stranger, "Alpha.Visible.shown", "Ay"));
}

/// Cases the generated differential runs: `BORZOI_SOURCE_REF_CASES`, else 24.
fn case_count() -> usize {
    std::env::var("BORZOI_SOURCE_REF_CASES")
        .ok()
        .map(|s| s.parse().expect("BORZOI_SOURCE_REF_CASES is a count"))
        .unwrap_or(24)
}

/// The run's seed: `BORZOI_SOURCE_REF_SEED`, else a fixed one, so the default
/// run is the same run everywhere.
fn seed() -> u64 {
    std::env::var("BORZOI_SOURCE_REF_SEED")
        .ok()
        .map(|s| s.parse().expect("BORZOI_SOURCE_REF_SEED is a u64"))
        .unwrap_or(0x005e_ed0f_5ce5)
}

fn case_fixture(case: &Case) -> ProjectGraphFixture {
    let library = name(&case.library);
    let mut projects = vec![FixtureProject {
        name: library.clone(),
        files: files(library_files(case)),
        project_refs: Vec::new(),
        defines: Vec::new(),
    }];
    let consumer_refs = match middle_files(case) {
        Some((middle, sources)) => {
            projects.push(FixtureProject {
                name: name(&middle),
                files: files(sources),
                project_refs: vec![library],
                defines: Vec::new(),
            });
            vec![name(&middle)]
        }
        None => vec![library],
    };
    projects.push(FixtureProject {
        name: name(&case.consumer),
        files: files(consumer_files(case)),
        project_refs: consumer_refs,
        defines: Vec::new(),
    });
    ProjectGraphFixture::materialise(projects).expect("a generated case is a graph")
}

/// Each JSON value of `xs` not matched by an equal one in `ys`, as text.
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

/// What differs between the two answers' records, file by file.
fn answer_diff(source: &GraphResponse, dll: &GraphResponse) -> Vec<String> {
    let mut out = Vec::new();
    if source.files.len() != dll.files.len() {
        out.push(format!(
            "{} files from source, {} with the DLL",
            source.files.len(),
            dll.files.len()
        ));
    }
    for (s, d) in source.files.iter().zip(&dll.files) {
        let path = s["Path"].as_str().unwrap_or("?");
        for field in ["Diagnostics", "Uses"] {
            let empty = Vec::new();
            let xs = s[field].as_array().unwrap_or(&empty);
            let ys = d[field].as_array().unwrap_or(&empty);
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

/// D1 of the source-references review: on generated two-project fixtures,
/// FCS with the library as an `FSharpReference` answers exactly what it
/// answers with the library built fresh and referenced as a DLL, every
/// consumer record and diagnostic compared. Every library is built by one
/// `dotnet build`.
///
/// Each case must also commit its anchor (a public value every library
/// declares) on both sides, so a case that silently grades nothing fails.
#[test]
#[ignore = "builds fixtures and runs FCS; use --ignored for oracle smoke"]
fn source_references_equal_fresh_dlls_on_generated_graphs() {
    let seed = seed();
    let cases: Vec<Case> = (0..case_count()).map(|i| generate(seed, i)).collect();
    let fixtures: Vec<ProjectGraphFixture> = cases.iter().map(case_fixture).collect();
    build_fixtures(
        &cases
            .iter()
            .zip(&fixtures)
            .flat_map(|(c, f)| {
                f.closure(&name(&c.consumer))
                    .into_iter()
                    .map(|p| f.fsproj(&p.name))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>(),
    );

    let mut oracle = ProjectGraphOracle::default();
    let mut failures = Vec::new();
    let mut into_library: BTreeMap<String, usize> = BTreeMap::new();
    let mut consumer_errors = 0usize;
    for (i, (case, fixture)) in cases.iter().zip(&fixtures).enumerate() {
        let consumer = name(&case.consumer);
        let source = oracle
            .check(&fixture.source_request(&consumer))
            .unwrap_or_else(|e| panic!("case {i}: the source check failed: {e}"));
        let dll = oracle
            .check(&fixture.dll_request(&consumer))
            .unwrap_or_else(|e| panic!("case {i}: the DLL check failed: {e}"));
        let mut problems = answer_diff(&source, &dll);
        for r in &source.referenced {
            // It built cleanly, so a source check that finds errors in it reads
            // it differently from the compiler.
            problems.extend(r.errors().map(|e| format!("{} from source: {e}", r.id)));
        }
        let anchor = format!("{}.anchor", anchor_module(case));
        for (side, answer) in [("source", &source), ("DLL", &dll)] {
            if !binds(answer, &anchor, &case.library) {
                problems.push(format!(
                    "the {side} answer does not bind `{ANCHOR_USE}{anchor}` into {}",
                    case.library
                ));
            }
            // FS0074: a type reached through the middle project lives in an
            // assembly the consumer was not handed.
            if errors(answer).iter().any(|e| e["ErrorNumber"] == 74) {
                problems.push(format!(
                    "the {side} answer misses a transitive reference (FS0074)"
                ));
            }
        }
        if !problems.is_empty() {
            let sources: String = library_files(case)
                .into_iter()
                .chain(middle_files(case).into_iter().flat_map(|(_, f)| f))
                .chain(consumer_files(case))
                .map(|(n, t)| format!("--- {n}\n{t}"))
                .collect();
            failures.push(format!(
                "case {i} (seed {seed}):\n  {}\n{sources}",
                problems.join("\n  ")
            ));
        }
        consumer_errors += errors(&source).len();
        for u in uses(&source).filter(|u| u["Assembly"] == case.library.as_str()) {
            let kind = u["SymbolKind"].as_str().unwrap_or("?").to_owned();
            *into_library.entry(kind).or_default() += 1;
        }
    }
    println!(
        "source references vs fresh DLLs: {} cases, {} consumer errors, uses binding into the library by kind: {into_library:?}",
        cases.len(),
        consumer_errors
    );
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// The generator's coverage: over the default run, every declaration kind
/// the library can export occurs, and so does each dimension that decides
/// what a consumer sees (hiding, `internal`, both `InternalsVisibleTo`
/// targets, assembly-level `AutoOpen`). Pure, so it runs without FCS and pins
/// what the differential above covers.
#[test]
fn the_generated_graphs_cover_every_declaration_kind() {
    let seed = seed();
    let mut seen = std::collections::BTreeSet::new();
    for i in 0..case_count() {
        seen.extend(kinds(&generate(seed, i)));
    }
    let want = [
        "namespace",
        "module",
        "auto-open module",
        "rqa module",
        "top-level module",
        "auto-open top-level module",
        "value",
        "literal",
        "function",
        "compiled-name function",
        "active pattern",
        "record",
        "union",
        "class",
        "interface",
        "abbreviation",
        "exception",
        "measure",
        "optional extension",
        "C#-style extension",
        "fsi-hidden item",
        "internal item",
        "assembly-level auto-open",
        "IVT to the consumer",
        "IVT to another assembly",
        "transitive reference through a middle project",
    ];
    let missing: Vec<&str> = want.iter().copied().filter(|k| !seen.contains(k)).collect();
    assert!(
        missing.is_empty(),
        "the run of {} cases (seed {seed}) never generates: {missing:?}",
        case_count()
    );
}

/// The not-built census: each dependent project of
/// `BORZOI_NOT_BUILT_PROJECT_LIST` (colon-separated `.fsproj` paths, restored,
/// their references not built) through the LSP's runtime path, graded against
/// FCS with every F# reference passed from source. Prints the measurement and
/// asserts nothing about it; `tools/not-built-census.sh` materialises the
/// projects and runs it.
#[test]
#[ignore = "a hand-run measurement; set BORZOI_NOT_BUILT_PROJECT_LIST (tools/not-built-census.sh)"]
fn not_built_census() {
    use borzoi_corpus_diff::not_built::{measure_not_built, render_not_built_totals};
    let list = std::env::var("BORZOI_NOT_BUILT_PROJECT_LIST")
        .expect("BORZOI_NOT_BUILT_PROJECT_LIST names the dependent projects to measure");
    let mut oracle = ProjectGraphOracle::default();
    let reports: Vec<_> = list
        .split(':')
        .filter(|p| !p.is_empty())
        .map(|p| {
            let report = measure_not_built(std::path::Path::new(p), &mut oracle);
            println!("{report}");
            report
        })
        .collect();
    println!("{}", render_not_built_totals(&reports));
}
