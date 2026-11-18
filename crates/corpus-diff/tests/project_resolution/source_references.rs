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

use borzoi_corpus_diff::{FcsInvokeError, ProjectGraphOracle};
use borzoi_oracle_harness::project_graph::{
    FixtureFile, FixtureProject, GraphProject, GraphReference, GraphRequest, GraphResponse,
    PlainName, ProjectGraphFixture, build_fixtures,
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

/// The default run's seed, fixed so it is the same run everywhere.
const DEFAULT_SEED: u64 = 0x005e_ed0f_5ce5;

/// How many cases the default run generates.
const DEFAULT_CASES: usize = 24;

/// The `(seed, index)` of every case the differential runs: the default run,
/// always, and, when `BORZOI_SOURCE_REF_SEED` or `BORZOI_SOURCE_REF_CASES` is
/// set, that many cases of that seed besides (each defaulting to the default
/// run's), so widening the sweep never drops the cases whose coverage
/// [`the_generated_graphs_cover_every_declaration_kind`] pins.
fn cases() -> Vec<(u64, usize)> {
    let seed = std::env::var("BORZOI_SOURCE_REF_SEED")
        .ok()
        .map(|s| s.parse::<u64>().expect("BORZOI_SOURCE_REF_SEED is a u64"));
    let count = std::env::var("BORZOI_SOURCE_REF_CASES").ok().map(|s| {
        s.parse::<usize>()
            .expect("BORZOI_SOURCE_REF_CASES is a count")
    });
    let mut cases: Vec<(u64, usize)> = (0..DEFAULT_CASES).map(|i| (DEFAULT_SEED, i)).collect();
    if seed.is_some() || count.is_some() {
        let seed = seed.unwrap_or(DEFAULT_SEED);
        for i in 0..count.unwrap_or(DEFAULT_CASES) {
            if !cases.contains(&(seed, i)) {
                cases.push((seed, i));
            }
        }
    }
    cases
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
    for x in unmatched(&source.diagnostics, &dll.diagnostics) {
        out.push(format!("project Diagnostics only from source: {x}"));
    }
    for y in unmatched(&dll.diagnostics, &source.diagnostics) {
        out.push(format!("project Diagnostics only with the DLL: {y}"));
    }
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
    let seeds = cases();
    // Projects of one build are named apart, whichever seed made them.
    let cases: Vec<Case> = seeds
        .iter()
        .enumerate()
        .map(|(ordinal, &(seed, i))| {
            let mut case = generate(seed, i);
            case.library = format!("Ay{ordinal}");
            if case.middle.is_some() {
                case.middle = Some(format!("Mid{ordinal}"));
            }
            case
        })
        .collect();
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
    for ((case, fixture), &(seed, i)) in cases.iter().zip(&fixtures).zip(&seeds) {
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
            // The value reached through the middle project, whose type lives
            // in the library, must bind into the middle project with no error
            // on its line: a missing transitive reference is FS0074 there.
            if let Some(middle) = &case.middle {
                let line = consumer_files(case)[0]
                    .1
                    .lines()
                    .position(|l| l.starts_with("let throughMiddle"))
                    .expect("a middle case uses its middle project")
                    + 1;
                if !binds(answer, &format!("{middle}.token"), middle) {
                    problems.push(format!(
                        "the {side} answer does not bind `{middle}.token` into {middle}"
                    ));
                }
                let on_line = errors(answer)
                    .into_iter()
                    .filter(|e| e["Range"]["Start"]["Line"].as_u64() == Some(line as u64))
                    .count();
                if on_line > 0 {
                    problems.push(format!(
                        "the {side} answer has {on_line} error(s) on the line through {middle}"
                    ));
                }
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
                "case {i} of seed {seed}:\n  {}\n{sources}",
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
    let mut seen = std::collections::BTreeSet::new();
    for i in 0..DEFAULT_CASES {
        seen.extend(kinds(&generate(DEFAULT_SEED, i)));
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
        "assembly-level auto-open",
        "IVT to the consumer",
        "IVT to another assembly",
        "transitive reference through a middle project",
    ];
    let missing: Vec<&str> = want.iter().copied().filter(|k| !seen.contains(k)).collect();
    assert!(
        missing.is_empty(),
        "the default run of {DEFAULT_CASES} cases (seed {DEFAULT_SEED}) never generates: {missing:?}"
    );
}

/// A referenced project is checked as the library its build makes, so a file
/// a library's build rejects (top-level code with no module or namespace,
/// FS0222) is an error from source too, rather than an executable's implicit
/// module the consumer could bind into.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_referenced_library_is_checked_as_a_library() {
    let fixture = ProjectGraphFixture::materialise(vec![
        FixtureProject {
            name: name("Lib"),
            files: files(vec![("Lib.fs".into(), "let x = 42\n".into())]),
            project_refs: Vec::new(),
            defines: Vec::new(),
        },
        FixtureProject {
            name: name("App"),
            files: files(vec![("Use.fs".into(), "module Use\n\nlet y = 1\n".into())]),
            project_refs: vec![name("Lib")],
            defines: Vec::new(),
        },
    ])
    .expect("a graph");
    let answer = ProjectGraphOracle::default()
        .check(&fixture.source_request(&name("App")))
        .expect("the graph oracle answers");
    let [library] = answer.referenced.as_slice() else {
        panic!("one referenced project: {:#?}", answer.referenced)
    };
    assert!(
        library.errors().any(|e| e["ErrorNumber"] == 222),
        "a library's top-level code is FS0222 from source as in its build: {library:#?}"
    );
}

/// Two references that declare one name: FCS takes the later one, so a
/// project passed from source must keep its DLL's place in the order. With
/// the first reference from source and the second a DLL, the consumer binds
/// exactly as with both DLLs, and as with both from source.
#[test]
#[ignore = "builds fixtures and runs FCS; use --ignored for oracle smoke"]
fn a_reference_from_source_keeps_its_place_in_the_order() {
    let library = |n: &str, ty: &str, value: &str| FixtureProject {
        name: name(n),
        files: files(vec![(
            "Lib.fs".into(),
            format!("namespace Duplicate\n\nmodule Mod =\n    let x : {ty} = {value}\n"),
        )]),
        project_refs: Vec::new(),
        defines: Vec::new(),
    };
    let fixture = ProjectGraphFixture::materialise(vec![
        library("Ay", "int", "1"),
        library("Zed", "string", "\"z\""),
        FixtureProject {
            name: name("Bee"),
            files: files(vec![(
                "Use.fs".into(),
                "module Use\n\nlet y = Duplicate.Mod.x\n".into(),
            )]),
            project_refs: vec![name("Ay"), name("Zed")],
            defines: Vec::new(),
        },
    ])
    .expect("a graph");
    build_fixtures(&[fixture.fsproj(&name("Ay")), fixture.fsproj(&name("Zed"))]);

    let bee = name("Bee");
    let source = fixture.source_request(&bee);
    let dll = fixture.dll_request(&bee);
    // Ay from source, Zed as its DLL, in the same order.
    let mixed = {
        let projects: Vec<GraphProject> = source
            .projects()
            .iter()
            .filter(|p| p.id != name("Zed"))
            .map(|p| {
                let mut p = p.clone();
                if p.id == bee {
                    p.references = vec![
                        GraphReference::Project(name("Ay")),
                        GraphReference::Dll(fixture.output_dll(&name("Zed"))),
                    ];
                }
                p
            })
            .collect();
        GraphRequest::new(projects, bee.clone()).expect("a graph")
    };
    let mut oracle = ProjectGraphOracle::default();
    let mut answers = Vec::new();
    for (label, request) in [("source", &source), ("dll", &dll), ("mixed", &mixed)] {
        let answer = oracle.check(request).expect("the graph oracle answers");
        assert_eq!(
            errors(&answer),
            Vec::<&Value>::new(),
            "{label}: {answer:#?}"
        );
        assert!(
            binds(&answer, "Duplicate.Mod.x", "Zed"),
            "{label}: the later reference wins: {answer:#?}"
        );
        answers.push((label, answer));
    }
    for (label, answer) in &answers[1..] {
        assert_eq!(
            answer_diff(&answers[0].1, answer),
            Vec::<String>::new(),
            "source against {label}"
        );
    }
}

/// Fixtures are built together however their projects are named: two
/// fixtures each holding a project `Lib` build in one `build_fixtures` call.
#[test]
#[ignore = "builds fixtures; use --ignored for oracle smoke"]
fn same_named_projects_of_two_fixtures_build_together() {
    let fixture = || {
        ProjectGraphFixture::materialise(vec![FixtureProject {
            name: name("Lib"),
            files: files(vec![("Lib.fs".into(), "module Lib\n\nlet x = 1\n".into())]),
            project_refs: Vec::new(),
            defines: Vec::new(),
        }])
        .expect("a graph")
    };
    let (first, second) = (fixture(), fixture());
    build_fixtures(&[first.fsproj(&name("Lib")), second.fsproj(&name("Lib"))]);
    assert!(first.output_dll(&name("Lib")).is_file());
    assert!(second.output_dll(&name("Lib")).is_file());
}

/// A referenced type provider assembly is refused. FCS hands a dependant no
/// in-memory signature for a project whose assembly carries
/// `TypeProviderAssemblyAttribute` and reads its output DLL from disk instead,
/// so with the library unbuilt the source check would bind the consumer's
/// `id` to FSharp.Core's with no diagnostic, where the built DLL binds the
/// library's.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_referenced_type_provider_assembly_is_refused() {
    let fixture = ProjectGraphFixture::materialise(vec![
        FixtureProject {
            name: name("Provider"),
            files: files(vec![(
                "Lib.fs".into(),
                "namespace Provided\n\n\
                 [<AutoOpen>]\nmodule Exports =\n    let id (x: int) = x + 1\n\n\
                 module Attributes =\n    \
                 [<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\n    \
                 do ()\n"
                    .into(),
            )]),
            project_refs: Vec::new(),
            defines: Vec::new(),
        },
        FixtureProject {
            name: name("Bee"),
            files: files(vec![(
                "Use.fs".into(),
                "module Use\n\nopen Provided\n\nlet y = id 1\n".into(),
            )]),
            project_refs: vec![name("Provider")],
            defines: Vec::new(),
        },
    ])
    .expect("a graph");
    match ProjectGraphOracle::default().check(&fixture.source_request(&name("Bee"))) {
        Err(FcsInvokeError::Refused(message)) => assert!(
            message.contains("type provider"),
            "refused for another reason: {message}"
        ),
        other => panic!("a type provider reference must be refused: {other:#?}"),
    }
}
