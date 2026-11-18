//! The project-graph oracle (`fcs-dump uses-project-graph-batch`) against
//! itself: FCS with each F# project reference passed from source, as an IDE
//! passes it, must answer exactly what it answers with the reference built
//! fresh and passed as the DLL its build compiles against.
//!
//! Both requests hand FCS one argument list, each project's own (read off a
//! real build of it, which builds the reference DLLs too), and differ only in
//! whether a project reference's `-r:` is registered as a project, which each
//! case holds ([`only_substitution`]). A fresh DLL's signature is the same CCU
//! signature the source reference exports (`tcsCcuSig`, pickled), so the two
//! readings can differ only where FCS's IDE path and its compiler path read
//! a project differently: its assembly-level attributes (`AutoOpen`,
//! `InternalsVisibleTo`), what a `.fsi` hides, a reference FCS reads from
//! disk anyway. Later stages hold borzoi's source-derived surface to the
//! built DLL's, and that oracle rests on this equality.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use borzoi_corpus_diff::{FcsInvokeError, ProjectGraphOracle};
use borzoi_oracle_harness::BatchFailure;
use borzoi_oracle_harness::par_map::par_map;
use borzoi_oracle_harness::project_graph::{
    FixtureArgs, FixtureFile, FixtureProject, GraphProject, GraphRequest, GraphResponse, PlainName,
    ProjectGraphFixture, ProjectRef, only_substitution,
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

fn project(n: &str, sources: Vec<(String, String)>, refs: &[&str]) -> FixtureProject {
    FixtureProject {
        project_refs: refs.iter().map(|r| name(r)).collect(),
        ..FixtureProject::new(name(n), files(sources))
    }
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

fn binds(response: &GraphResponse, full_name: &str, assembly: &str) -> bool {
    uses(response).any(|u| u["FullName"] == full_name && u["Assembly"] == assembly)
}

/// `check()`, run with every file `request` registers as a project moved
/// aside, then put back: a reference the oracle should read from source but
/// reads from disk finds nothing there, so the answer cannot agree with the
/// DLL's by reading the same file.
fn with_registered_references_hidden<T>(request: &GraphRequest, check: impl FnOnce() -> T) -> T {
    let registered: BTreeSet<&str> = request
        .projects()
        .iter()
        .flat_map(|p| p.project_refs.iter().map(|r| r.reference.as_str()))
        .collect();
    let hidden = |r: &str| format!("{r}.hidden");
    for r in &registered {
        std::fs::rename(r, hidden(r)).unwrap_or_else(|e| panic!("hide {r}: {e}"));
    }
    let answer = check();
    for r in &registered {
        std::fs::rename(hidden(r), r).unwrap_or_else(|e| panic!("restore {r}: {e}"));
    }
    answer
}

/// Where each project of `request` (the source request `answer` answers)
/// has a signature FCS checked from source that is not, line for line, the
/// one it reads from the DLL that project's build wrote. Producers and the
/// checked project alike: a difference in meaning between FCS's check and
/// the build that reaches any project's exported surface shows here.
fn signature_disagreements(
    oracle: &mut ProjectGraphOracle,
    fixture: &ProjectGraphFixture,
    args: &FixtureArgs,
    request: &GraphRequest,
    answer: &GraphResponse,
) -> Vec<String> {
    let mut problems = Vec::new();
    for project in request.projects().iter().map(|p| p.id.clone()) {
        let source = if &project == request.check() {
            &answer.signature
        } else if let Some(r) = answer.referenced.iter().find(|r| r.id == project.as_str()) {
            &r.signature
        } else {
            problems.push(format!("{project} has no signature in the response"));
            continue;
        };
        if source.is_empty() {
            problems.push(format!("{project}'s signature is empty"));
        }
        // A failed build wrote no DLL; `errors_agree` holds that project.
        if !args.succeeded(&project) {
            continue;
        }
        let output = args
            .of(&project)
            .iter()
            .find_map(|a| a.strip_prefix("-o:"))
            .expect("a -o: argument");
        let dll = fixture.dir(&project).join(output);
        match oracle.dll_signature(request, &project, &dll) {
            Ok(built) if &built == source => {}
            Ok(built) => problems.push(format!(
                "{project}'s signature from source differs from its built DLL's:\n  source: {source:#?}\n  DLL: {built:#?}"
            )),
            Err(e) => problems.push(format!("{project}'s built signature is unread: {e}")),
        }
    }
    problems
}

/// `request` with each project's arguments mapped by `f`.
fn with_args(request: &GraphRequest, f: impl Fn(&GraphProject) -> Vec<String>) -> GraphRequest {
    let projects: Vec<GraphProject> = request
        .projects()
        .iter()
        .map(|p| GraphProject {
            args: f(p),
            ..p.clone()
        })
        .collect();
    GraphRequest::new(projects, request.check().clone()).expect("still a graph")
}

/// A library granting its internals to `Bee`, and a consumer using one.
fn friend_fixture() -> ProjectGraphFixture {
    ProjectGraphFixture::materialise(vec![
        project(
            "Ay",
            vec![(
                "Lib.fs".into(),
                "namespace Alpha\n\n\
                 module internal Hidden =\n    let secret = 42\n\n\
                 module Visible =\n    let shown = 1\n\n\
                 module Attributes =\n    \
                 [<assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"Bee\")>]\n    \
                 do ()\n"
                    .into(),
            )],
            &[],
        ),
        project(
            "Bee",
            vec![
                (
                    "Use.fs".into(),
                    "module Use\n\nlet s = Alpha.Hidden.secret\nlet v = Alpha.Visible.shown\n"
                        .into(),
                ),
                ("Program.fs".into(), "module Program\n\nlet z = 0\n".into()),
            ],
            &["Ay"],
        ),
    ])
    .expect("a graph")
}

/// The must-bind-internal cell. A friend's use of an internal binds only when
/// the consumer's assembly name, which its `-o:` argument sets, is the one
/// the library's `InternalsVisibleTo` names. It also pins that a reference
/// passed from source needs no file on disk: its DLL is deleted first.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_friend_binds_an_internal_only_under_its_assembly_name() {
    let fixture = friend_fixture();
    let args = fixture.fsc_args(&name("Bee"));
    let mut oracle = ProjectGraphOracle::default();
    let request = fixture.source_request(&args, &name("Bee"));
    let [ProjectRef { reference, .. }] = request.projects()[1].project_refs.as_slice() else {
        panic!("Bee references Ay: {request:#?}")
    };
    // Bee's build built the reference; FCS reads it from source, so the file
    // is not needed.
    std::fs::remove_file(reference).expect("remove the built reference");
    assert!(!Path::new(reference).exists());

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

    // The control: with its `-o:` renamed, the consumer is no friend, so the
    // internal's use (line 3) is an access error, and the public value's
    // (line 4) is not. FCS still records a use at an inaccessible name, so
    // the records alone do not tell the two apart.
    let stranger = oracle
        .check(&with_args(&request, |p| {
            p.args
                .iter()
                .map(|a| {
                    if p.id == name("Bee") && a.starts_with("-o:") {
                        a.replace("Bee.dll", "NotBee.dll")
                    } else {
                        a.clone()
                    }
                })
                .collect()
        }))
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

/// Indices of [`DEFAULT_SEED`] beyond [`DEFAULT_CASES`] the default run adds,
/// so that every kind of use, colliding or not, reaches a clean twin's
/// exports: the first [`DEFAULT_CASES`] use a colliding function with a
/// `CompiledName` only where the consumer cannot see it.
const PINNED_CASES: &[usize] = &[77, 92, 129];

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
    let mut cases: Vec<(u64, usize)> = (0..DEFAULT_CASES)
        .chain(PINNED_CASES.iter().copied())
        .map(|i| (DEFAULT_SEED, i))
        .collect();
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
    let library = case.library.as_str();
    let mut projects = vec![project(library, library_files(case), &[])];
    let consumer_refs: Vec<&str> = match &case.middle {
        Some(middle) => {
            let (_, sources) = middle_files(case).expect("a middle case has middle files");
            projects.push(project(middle, sources, &[library]));
            vec![middle.as_str()]
        }
        None => vec![library],
    };
    projects.push(project(
        &case.consumer,
        consumer_files(case),
        &consumer_refs,
    ));
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

/// D1 of the source-references review: on generated fixtures, FCS with the
/// library as an `FSharpReference` answers exactly what it answers with the
/// library built fresh and referenced as the DLL its build compiles against,
/// every consumer record and diagnostic compared, the two requests differing
/// only by that substitution.
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
    // One real build per project, fixtures side by side: each gives the
    // project's fsc arguments and builds the DLLs they reference.
    let args: Vec<FixtureArgs> = par_map(fixtures.len(), |i| {
        fixtures[i].fsc_args(&name(&cases[i].consumer))
    });

    let mut oracle = ProjectGraphOracle::default();
    let mut failures = Vec::new();
    let mut into_library: BTreeMap<String, usize> = BTreeMap::new();
    let mut consumer_errors = 0usize;
    let mut consumers_built = 0usize;
    let mut twins: Vec<Case> = Vec::new();
    let mut why_dropped: BTreeMap<String, String> = BTreeMap::new();
    for (((case, fixture), args), &(seed, i)) in cases.iter().zip(&fixtures).zip(&args).zip(&seeds)
    {
        let consumer = name(&case.consumer);
        let (source_request, dll_request) = (
            fixture.source_request(args, &consumer),
            fixture.dll_request(args, &consumer),
        );
        if let Err(why) = only_substitution(fixture, &source_request, &dll_request) {
            panic!("case {i}: the requests differ beyond the substitution: {why}");
        }
        let source = with_registered_references_hidden(&source_request, || {
            oracle
                .check(&source_request)
                .unwrap_or_else(|e| panic!("case {i}: the source check failed: {e}"))
        });
        let dll = oracle
            .check(&dll_request)
            .unwrap_or_else(|e| panic!("case {i}: the DLL check failed: {e}"));
        let mut problems = answer_diff(&source, &dll);
        // Each side must find errors exactly where fsc failed a build, or it
        // reads some project apart from the compiler.
        for (side, request, answer) in [
            ("source", &source_request, &source),
            ("DLL", &dll_request, &dll),
        ] {
            if let Err(why) = args.errors_agree(request, answer) {
                problems.push(format!(
                    "the {side} answer disagrees with the builds: {why}"
                ));
            }
        }
        problems.extend(signature_disagreements(
            &mut oracle,
            fixture,
            args,
            &source_request,
            &source,
        ));
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
        consumers_built += usize::from(args.succeeded(&consumer));
        for u in uses(&source).filter(|u| u["Assembly"] == case.library.as_str()) {
            let kind = u["SymbolKind"].as_str().unwrap_or("?").to_owned();
            *into_library.entry(kind).or_default() += 1;
        }
        // Every case must get its twin: a lost one leaves that consumer's
        // signature unchecked, which tag coverage over the run cannot see.
        match clean_twin(&mut oracle, fixture, args, case, &source, &mut why_dropped) {
            Ok(twin) => twins.push(twin),
            Err(why) => failures.push(format!("case {i} of seed {seed} has no clean twin: {why}")),
        }
    }

    // Each case's clean twin, built and held to its DLLs: most generated
    // consumers use what they cannot see and so build no DLL, which leaves
    // their own signature unchecked.
    let twin_cases: Vec<&Case> = twins.iter().collect();
    let twin_fixtures: Vec<ProjectGraphFixture> =
        twin_cases.iter().map(|c| case_fixture(c)).collect();
    let twin_args: Vec<FixtureArgs> = par_map(twin_fixtures.len(), |i| {
        twin_fixtures[i].fsc_args(&name(&twin_cases[i].consumer))
    });
    let (mut twins_built, mut twins_matched) = (0usize, 0usize);
    let mut covered: BTreeSet<&str> = BTreeSet::new();
    for ((twin, fixture), args) in twin_cases.iter().zip(&twin_fixtures).zip(&twin_args) {
        let consumer = name(&twin.consumer);
        let request = fixture.source_request(args, &consumer);
        // As in the original check, a reference read from disk instead of
        // from source finds nothing there.
        let answer = with_registered_references_hidden(&request, || {
            oracle.check(&request).unwrap_or_else(|e| {
                panic!("twin of {}: the source check failed: {e}", twin.library)
            })
        });
        let mut problems: Vec<String> = args
            .errors_agree(&request, &answer)
            .err()
            .into_iter()
            .collect();
        twins_built += usize::from(args.succeeded(&consumer));
        problems.extend(signature_disagreements(
            &mut oracle,
            fixture,
            args,
            &request,
            &answer,
        ));
        if !args.succeeded(&consumer) {
            problems.push("FCS checks the twin's consumer clean, but its build failed".to_owned());
        }
        if problems.is_empty() {
            twins_matched += 1;
            covered.extend(twin.use_tags.iter().map(String::as_str));
        } else {
            failures.push(format!(
                "the clean twin of {}:\n  {}\n{}",
                twin.library,
                problems.join("\n  "),
                consumer_files(twin)[0].1
            ));
        }
    }
    // Every kind of use the cases make, colliding and not, reaches a
    // consumer's exports in some twin that matched.
    let required: BTreeSet<&str> = cases
        .iter()
        .flat_map(|c| c.use_tags.iter().map(String::as_str))
        .collect();
    let uncovered: Vec<&&str> = required.difference(&covered).collect();
    println!(
        "source references vs fresh DLLs: {} cases, {consumers_built} consumers built (their signatures held to their DLLs), {} consumer errors, uses binding into the library by kind: {into_library:?}",
        cases.len(),
        consumer_errors
    );
    println!(
        "clean twins: {} of {} cleaned, {twins_built} built, {twins_matched} matched their DLLs; use kinds reaching a matched twin's exports: {covered:?}",
        twin_cases.len(),
        cases.len()
    );
    if !uncovered.is_empty() {
        let examples: Vec<String> = cases
            .iter()
            .flat_map(|c| {
                c.uses
                    .iter()
                    .zip(&c.use_tags)
                    .filter(|(_, t)| uncovered.contains(&&t.as_str()))
                    .map(|(u, t)| {
                        let key = format!("{}: {u}", c.library);
                        let why = why_dropped.get(&key).map_or("", String::as_str);
                        format!("{key} ({t}) dropped for: {why}")
                    })
            })
            .collect();
        failures.push(format!(
            "no matched twin exports a use of: {uncovered:?}; the cases' uses of them:\n  {}",
            examples.join("\n  ")
        ));
    }
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// The lines of the consumer's `Use.fs` on which `answer` reports an error.
fn use_error_lines(answer: &GraphResponse) -> BTreeMap<usize, String> {
    answer
        .files
        .iter()
        .filter(|f| f["Path"].as_str().is_some_and(|p| p.ends_with("/Use.fs")))
        .flat_map(|f| f["Diagnostics"].as_array().into_iter().flatten())
        .filter(|d| d["Severity"] == "Error")
        .filter_map(|d| {
            let line = usize::try_from(d["Range"]["Start"]["Line"].as_u64()?).ok()?;
            Some((line, d["Message"].as_str().unwrap_or("?").to_owned()))
        })
        .collect()
}

/// `case`'s clean twin: the same graph and inputs, with each consumer use
/// and `open` FCS reports an error on removed, round by round (removing an
/// `open` can break a later bare use). Each round rewrites `fixture`'s
/// `Use.fs` and checks it from source again. An error, saying why, when a
/// line other than a use or an `open` errs, an error lies outside `Use.fs`,
/// the oracle refuses a round, or four rounds do not reach a clean consumer.
fn clean_twin(
    oracle: &mut ProjectGraphOracle,
    fixture: &ProjectGraphFixture,
    args: &FixtureArgs,
    case: &Case,
    first: &GraphResponse,
    why_dropped: &mut BTreeMap<String, String>,
) -> Result<Case, String> {
    let consumer = name(&case.consumer);
    let request = fixture.source_request(args, &consumer);
    let use_fs = fixture.dir(&consumer).join("Use.fs");
    let mut twin = case.clone();
    let mut answer = first.clone();
    for _ in 0..4 {
        let bad = use_error_lines(&answer);
        if bad.is_empty() {
            return match answer.errors().next() {
                None => Ok(twin),
                Some(e) => Err(format!("an error outside Use.fs: {e}")),
            };
        }
        let text = consumer_files(&twin)[0].1.clone();
        let lines: Vec<&str> = text.lines().collect();
        let dropped: BTreeSet<&str> = bad
            .iter()
            .filter_map(|(l, message)| {
                let line = lines.get(l - 1)?;
                why_dropped.insert(format!("{}: {line}", case.library), message.clone());
                Some(line)
            })
            .copied()
            .collect();
        let removable = |l: &str| twin.uses.iter().any(|u| u == l) || l.starts_with("open ");
        if let Some(l) = dropped.iter().find(|l| !removable(l)) {
            return Err(format!("an error on a line that is no use or open: {l}"));
        }
        let kept: Vec<(String, String)> = twin
            .uses
            .iter()
            .zip(&twin.use_tags)
            .filter(|(u, _)| !dropped.contains(u.as_str()))
            .map(|(u, t)| (u.clone(), t.clone()))
            .collect();
        (twin.uses, twin.use_tags) = kept.into_iter().unzip();
        twin.opens
            .retain(|o| !dropped.contains(format!("open {o}").as_str()));
        std::fs::write(&use_fs, &consumer_files(&twin)[0].1).expect("rewrite Use.fs");
        answer = oracle
            .check(&request)
            .map_err(|e| format!("the oracle refused a round: {e}"))?;
    }
    Err("four rounds did not reach a clean consumer".to_owned())
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

/// A project is checked as the library its build makes, so a file a
/// library's build rejects (top-level code with no module or namespace,
/// FS0222) is an error to FCS too, rather than an executable's implicit
/// module a consumer could bind into: the `--target:` of its own arguments
/// reaches FCS.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_library_is_checked_as_a_library() {
    let fixture = ProjectGraphFixture::materialise(vec![project(
        "Lib",
        vec![("Lib.fs".into(), "let x = 42\n".into())],
        &[],
    )])
    .expect("a graph");
    let args = fixture.fsc_args(&name("Lib"));
    let request = fixture.source_request(&args, &name("Lib"));
    let answer = ProjectGraphOracle::default()
        .check(&request)
        .expect("the graph oracle answers");
    assert!(
        answer.errors().any(|e| e["ErrorNumber"] == 222),
        "a library's top-level code is FS0222 to FCS as to its build: {answer:#?}"
    );
    assert!(!args.succeeded(&name("Lib")), "fsc fails the build");
    assert_eq!(args.errors_agree(&request, &answer), Ok(()));
}

/// The checked project's own exported surface is held to the DLL its build
/// wrote, as every producer's is: here an export whose type the build's
/// defines decide, which FCS reads apart from fsc, without an error either
/// side, if any define fails to reach it.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_consumer_signature_is_its_built_dll_signature() {
    let fixture = ProjectGraphFixture::materialise(vec![
        project(
            "Lib",
            vec![("Lib.fs".into(), "module Lib\n\nlet x = 1\n".into())],
            &[],
        ),
        project(
            "App",
            vec![(
                "App.fs".into(),
                "module App\n\n#if RELEASE\nlet exported = Lib.x\n#else\nlet exported = string Lib.x\n#endif\n"
                    .into(),
            )],
            &["Lib"],
        ),
    ])
    .expect("a graph");
    let args = fixture.fsc_args(&name("App"));
    let request = fixture.source_request(&args, &name("App"));
    let mut oracle = ProjectGraphOracle::default();
    let answer = oracle.check(&request).expect("the graph oracle answers");
    assert_eq!(args.errors_agree(&request, &answer), Ok(()));
    let problems = signature_disagreements(&mut oracle, &fixture, &args, &request, &answer);
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    assert!(
        answer
            .signature
            .iter()
            .any(|l| l.contains("exported") && l.contains("System.Int32")),
        "the Release build's export is an int: {:#?}",
        answer.signature
    );
}

/// A project whose source names a signing key file is refused: FCS resolves
/// the file against its own directory, fsc against the project's, so the
/// two can give the assembly different identities.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_source_signing_attribute_is_refused() {
    let fixture = ProjectGraphFixture::materialise(vec![project(
        "Lib",
        vec![(
            "Lib.fs".into(),
            "module Lib\n\n[<assembly: System.Reflection.AssemblyKeyFileAttribute(\"key.snk\")>]\ndo ()\n\nlet x = 1\n"
                .into(),
        )],
        &[],
    )])
    .expect("a graph");
    let args = fixture.fsc_args(&name("Lib"));
    match ProjectGraphOracle::default().check(&fixture.source_request(&args, &name("Lib"))) {
        Err(FcsInvokeError::Refused(why)) if why.contains("AssemblyKeyFile") => {}
        other => panic!("a signing attribute must be refused: {other:?}"),
    }
}

/// Every record the oracle returns describes the code the build compiled.
/// FCS's per-file check defines `EDITING`, which fsc does not; here the
/// producer and the consumer each say one thing under `EDITING` and another
/// without, and the file records, like the build-agreement and signature
/// checks, must read the build's branch.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
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
    let args = fixture.fsc_args(&name("App"));
    assert!(
        args.succeeded(&name("App")),
        "the build compiles the non-EDITING branch"
    );
    let request = fixture.source_request(&args, &name("App"));
    let mut oracle = ProjectGraphOracle::default();
    let answer = oracle.check(&request).expect("the graph oracle answers");
    assert_eq!(args.errors_agree(&request, &answer), Ok(()));
    let problems = signature_disagreements(&mut oracle, &fixture, &args, &request, &answer);
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    assert!(
        errors(&answer).is_empty(),
        "no file record holds an error: {answer:#?}"
    );
    let named = |n: &str| uses(&answer).any(|u| u["FullName"] == format!("App.{n}"));
    assert!(
        named("onlyBuild"),
        "the build's branch is recorded: {answer:#?}"
    );
    assert!(
        !named("onlyEditing"),
        "the EDITING branch is not: {answer:#?}"
    );
}

/// The rendered signature tells apart what a consumer tells apart: one
/// module name under two namespaces, a literal from a value and one
/// literal's value from another, and a type by the assembly that defines it.
/// Its every line also equals the built DLL's.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn the_signature_tells_apart_paths_literals_and_defining_assemblies() {
    let fixture = ProjectGraphFixture::materialise(vec![project(
        "Lib",
        vec![(
            "Lib.fs".into(),
            "namespace First\n\nmodule Values =\n    [<Literal>]\n    let Export = 1\n    let plain = 1\n\n\
             namespace Second\n\nmodule Values =\n    [<Literal>]\n    let Export = 2\n    \
             type Token = Token of int\n    let make () = Token 0\n\n\
             namespace Third\n\n[<Measure>] type kg\n[<Measure>] type N = kg\n\nmodule Forces =\n    let force = 1.0<N>\n"
                .into(),
        )],
        &[],
    )])
    .expect("a graph");
    let args = fixture.fsc_args(&name("Lib"));
    let request = fixture.source_request(&args, &name("Lib"));
    let mut oracle = ProjectGraphOracle::default();
    let answer = oracle.check(&request).expect("the graph oracle answers");
    assert_eq!(args.errors_agree(&request, &answer), Ok(()));
    let problems = signature_disagreements(&mut oracle, &fixture, &args, &request, &answer);
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    let signature = answer.signature.join("\n");
    for expected in [
        "First.Values",
        "Second.Values",
        "System.Int32 = literal 1",
        "System.Int32 = literal 2",
        "plain : ",
        "Lib!Second.Values.Token",
    ] {
        assert!(
            signature.contains(expected),
            "the signature must hold {expected:?}:\n{signature}"
        );
    }
    assert!(
        answer
            .signature
            .iter()
            .any(|l| l.contains(" plain : ") && !l.contains("literal")),
        "a value is no literal:\n{signature}"
    );
}

/// Two references that declare one name: FCS takes the later one, so a
/// project passed from source must keep its DLL's place in the build's
/// order. With the first reference from source and the second its DLL, the
/// consumer binds exactly as with both DLLs, and as with both from source.
#[test]
#[ignore = "builds fixtures and runs FCS; use --ignored for oracle smoke"]
fn a_reference_from_source_keeps_its_place_in_the_order() {
    let library = |n: &str, ty: &str, value: &str| {
        project(
            n,
            vec![(
                "Lib.fs".into(),
                format!("namespace Duplicate\n\nmodule Mod =\n    let x : {ty} = {value}\n"),
            )],
            &[],
        )
    };
    let fixture = ProjectGraphFixture::materialise(vec![
        library("Ay", "int", "1"),
        library("Zed", "string", "\"z\""),
        project(
            "Bee",
            vec![(
                "Use.fs".into(),
                "module Use\n\nlet y = Duplicate.Mod.x\n".into(),
            )],
            &["Ay", "Zed"],
        ),
    ])
    .expect("a graph");
    let args = fixture.fsc_args(&name("Bee"));

    let bee = name("Bee");
    let source = fixture.source_request(&args, &bee);
    let dll = fixture.dll_request(&args, &bee);
    // Ay from source, Zed as its DLL, in the build's order.
    let mixed = {
        let projects: Vec<GraphProject> = source
            .projects()
            .iter()
            .filter(|p| p.id != name("Zed"))
            .map(|p| {
                let mut p = p.clone();
                p.project_refs.retain(|r| r.project != name("Zed"));
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
        let winner = uses(&answer)
            .find(|u| u["FullName"] == "Duplicate.Mod.x")
            .and_then(|u| u["Assembly"].as_str())
            .unwrap_or_else(|| panic!("{label}: no use of Duplicate.Mod.x: {answer:#?}"))
            .to_owned();
        answers.push((label, winner, answer));
    }
    for (label, winner, answer) in &answers[1..] {
        assert_eq!(winner, &answers[0].1, "source against {label}");
        assert_eq!(
            answer_diff(&answers[0].2, answer),
            Vec::<String>::new(),
            "source against {label}"
        );
    }
}

/// Whether `result` is the oracle refusing a reference it would read from
/// disk.
fn refused_as_read_from_disk(result: &Result<GraphResponse, FcsInvokeError>) -> bool {
    matches!(result, Err(FcsInvokeError::Refused(message)) if message.contains("rather than from source"))
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
        project(
            "Provider",
            vec![(
                "Lib.fs".into(),
                "namespace Provided\n\n\
                 [<AutoOpen>]\nmodule Exports =\n    let id (x: int) = x + 1\n\n\
                 module Attributes =\n    \
                 [<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\n    \
                 do ()\n"
                    .into(),
            )],
            &[],
        ),
        project(
            "Bee",
            vec![(
                "Use.fs".into(),
                "module Use\n\nopen Provided\n\nlet y = id 1\n".into(),
            )],
            &["Provider"],
        ),
    ])
    .expect("a graph");
    let args = fixture.fsc_args(&name("Bee"));
    let result = ProjectGraphOracle::default().check(&fixture.source_request(&args, &name("Bee")));
    assert!(
        refused_as_read_from_disk(&result),
        "a type provider reference must be refused: {result:#?}"
    );
}

/// A library that consumes a generative type provider is refused, though it
/// carries no `TypeProviderAssemblyAttribute`: FCS hands a dependant no
/// in-memory signature for a project that creates generated provided types,
/// either. Its schema is named relative to the project, so the provider
/// finds it only if the oracle checks the library from its project file's
/// directory. SwaggerProvider's runtime assembly comes from the packages
/// folder (`nix/deps.json` holds it), referenced unrestored.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_reference_that_creates_generated_provided_types_is_refused() {
    let packages = std::env::var_os("NUGET_PACKAGES")
        .expect("NUGET_PACKAGES names the packages folder (the devshell sets it)");
    let runtime = Path::new(&packages)
        .join("swaggerprovider/1.0.1/lib/netstandard2.0/SwaggerProvider.Runtime.dll");
    assert!(runtime.is_file(), "{} is missing", runtime.display());
    let fixture = ProjectGraphFixture::materialise(vec![
        FixtureProject {
            assembly_refs: vec![runtime],
            ..project(
                "Client",
                vec![(
                    "Lib.fs".into(),
                    "namespace Provided\n\nopen SwaggerProvider\n\n\
                     type Api = OpenApiClientProvider<\"schema.json\">\n\n\
                     [<AutoOpen>]\nmodule Exports =\n    let id (x: int) = x + 1\n"
                        .into(),
                )],
                &[],
            )
        },
        project(
            "Bee",
            vec![(
                "Use.fs".into(),
                "module Use\n\nopen Provided\n\nlet y = id 1\n".into(),
            )],
            &["Client"],
        ),
    ])
    .expect("a graph");
    std::fs::write(
        fixture.dir(&name("Client")).join("schema.json"),
        r#"{"openapi":"3.0.0","info":{"title":"T","version":"1"},"paths":{"/pets":{"get":{"operationId":"listPets","responses":{"200":{"description":"ok","content":{"application/json":{"schema":{"type":"string"}}}}}}}}}"#,
    )
    .expect("write the schema");
    let args = fixture.fsc_args(&name("Bee"));
    let result = ProjectGraphOracle::default().check(&fixture.source_request(&args, &name("Bee")));
    assert!(
        refused_as_read_from_disk(&result),
        "a generative provider's consumer must be refused: {result:#?}"
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
/// its timestamp put back, are read afresh. Later incremental differentials
/// put one graph to the oracle again after each edit.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn a_rewritten_reference_is_read_afresh_whatever_its_timestamp() {
    let fixture = ProjectGraphFixture::materialise(vec![
        project(
            "Lib",
            vec![("Lib.fs".into(), "module Lib\n\nlet x : int = 1\n".into())],
            &[],
        ),
        project(
            "App",
            vec![("Use.fs".into(), "module Use\n\nlet y = Lib.x\n".into())],
            &["Lib"],
        ),
    ])
    .expect("a graph");
    let type_of_x = |answer: &GraphResponse| -> String {
        uses(answer)
            .find(|u| u["FullName"] == "Lib.x" && u["IsFromDefinition"] == false)
            .and_then(|u| u["Value"]["TypeCanon"].as_str())
            .unwrap_or_else(|| panic!("no typed use of Lib.x: {answer:#?}"))
            .to_owned()
    };
    // The same library with `x` a string, built in a tree of its own, whose
    // reference DLL is copied over the first one's.
    let rewritten = ProjectGraphFixture::materialise(vec![project(
        "Lib",
        vec![(
            "Lib.fs".into(),
            "module Lib\n\nlet x : string = \"\"\n".into(),
        )],
        &[],
    )])
    .expect("a graph");
    let args = fixture.fsc_args(&name("App"));
    rewritten.fsc_args(&name("Lib"));
    let request = fixture.source_request(&args, &name("App"));
    let dll_request = fixture.dll_request(&args, &name("App"));
    let mut oracle = ProjectGraphOracle::default();
    let mut check = |request: &GraphRequest| {
        type_of_x(&oracle.check(request).expect("the graph oracle answers"))
    };
    let (before, before_dll) = (check(&request), check(&dll_request));
    assert!(before.contains("Int32"), "{before}");
    assert!(before_dll.contains("Int32"), "{before_dll}");

    let lib = fixture.paths(&name("Lib")).remove(0);
    let stamp = std::fs::metadata(&lib)
        .and_then(|m| m.modified())
        .expect("read the library's timestamp");
    std::fs::write(&lib, "module Lib\n\nlet x : string = \"\"\n").expect("rewrite the library");
    set_modified(&lib, stamp);
    let after = check(&request);
    assert!(
        after.contains("String"),
        "the source rewrite must be seen: {after}"
    );

    let [ProjectRef { reference, .. }] = request.projects()[1].project_refs.as_slice() else {
        panic!("App references Lib: {request:#?}")
    };
    let reference = Path::new(reference);
    let within = reference
        .strip_prefix(fixture.dir(&name("Lib")))
        .expect("the reference is Lib's");
    let rewritten_dll = rewritten.dir(&name("Lib")).join(within);
    assert!(
        rewritten_dll.exists(),
        "the rewritten build writes its reference at {}",
        rewritten_dll.display()
    );
    let stamp = std::fs::metadata(reference)
        .and_then(|m| m.modified())
        .expect("read the reference's timestamp");
    std::fs::copy(&rewritten_dll, reference).expect("rewrite the reference DLL");
    set_modified(reference, stamp);
    let after_dll = check(&dll_request);
    assert!(
        after_dll.contains("String"),
        "the DLL rewrite must be seen: {after_dll}"
    );
}

/// fcs-dump's request parser refuses, as one `BatchError` each, every
/// request outside the domain it reads as fsc does: the JSON shape (unknown,
/// repeated or mistyped fields), the paths (relative), the arguments
/// (padded, holding a line break, MSBuild spellings, response-file
/// directives, slash switches, switches outside its allow-list or with a
/// value outside their grammar, a target or language version outside its
/// allow-list, a missing, empty or repeated `-o:`/`--target:`/
/// `--langversion:`, the other spellings of the switches it reads) and the
/// graph (an unknown, cyclic or module reference, one registered by a file
/// the producer does not write, a duplicate id). Each variant is the friend
/// fixture's valid request with one thing changed, which the first case shows
/// the oracle accepts; other spellings inside each grammar are accepted; and
/// a request that is not one line is never sent.
#[test]
#[ignore = "builds/runs FCS; use --ignored for oracle smoke"]
fn the_graph_parser_refuses_everything_outside_its_domain() {
    let fixture = friend_fixture();
    let args = fixture.fsc_args(&name("Bee"));
    let valid: Value =
        serde_json::from_str(&fixture.source_request(&args, &name("Bee")).to_json_line())
            .expect("json");
    let edit = |f: &dyn Fn(&mut Value)| {
        let mut v = valid.clone();
        f(&mut v);
        v.to_string()
    };
    let map_bee_args = |f: &dyn Fn(Vec<Value>) -> Vec<Value>| {
        edit(&|v: &mut Value| {
            let bee = &mut v["projects"][1]["args"];
            *bee = Value::Array(f(bee.as_array().expect("args").clone()));
        })
    };
    let replace_line = |prefix: &'static str, line: &'static str| {
        map_bee_args(&move |a: Vec<Value>| {
            a.into_iter()
                .map(|l| {
                    if l.as_str().is_some_and(|s| s.starts_with(prefix)) {
                        Value::String(line.to_owned())
                    } else {
                        l
                    }
                })
                .collect()
        })
    };
    let drop_line = |prefix: &'static str| {
        map_bee_args(&move |a: Vec<Value>| {
            a.into_iter()
                .filter(|l| !l.as_str().is_some_and(|s| s.starts_with(prefix)))
                .collect()
        })
    };
    let add_line = |line: &'static str| {
        map_bee_args(&move |mut a: Vec<Value>| {
            a.insert(0, Value::String(line.to_owned()));
            a
        })
    };
    let refused: Vec<(&str, String)> = vec![
        (
            "unknown top-level field",
            edit(&|v| v["extra"] = Value::Bool(true)),
        ),
        (
            "unknown project field",
            edit(&|v| v["projects"][0]["refs"] = serde_json::json!([])),
        ),
        (
            "mistyped args",
            edit(&|v| v["projects"][0]["args"] = Value::String("-o:x.dll".into())),
        ),
        (
            "mistyped check",
            edit(&|v| v["check"] = serde_json::json!(1)),
        ),
        (
            "missing check",
            edit(&|v| {
                v.as_object_mut().expect("object").remove("check");
            }),
        ),
        (
            "relative project file",
            edit(&|v| v["projects"][0]["projectFile"] = Value::String("Ay/Ay.fsproj".into())),
        ),
        (
            "unknown reference field",
            edit(&|v| v["projects"][1]["projectRefs"][0]["path"] = Value::String("x".into())),
        ),
        ("padded line", add_line(" --nologo")),
        ("MSBuild escape", add_line("--define:A%3BB")),
        ("backslash", add_line("--define:A\\B")),
        ("response-file directive", add_line("@more.rsp")),
        ("comment line", add_line("# note")),
        ("switch outside the allow-list", add_line("--help")),
        ("no -o:", drop_line("-o:")),
        ("two -o:", add_line("-o:obj/Other.dll")),
        ("no --target:", drop_line("--target:")),
        (
            "target outside the allow-list",
            replace_line("--target:", "--target:appcontainerexe"),
        ),
        ("no --langversion:", drop_line("--langversion:")),
        (
            "langversion ?",
            replace_line("--langversion:", "--langversion:?"),
        ),
        (
            "langversion latest",
            replace_line("--langversion:", "--langversion:latest"),
        ),
        (
            "langversion below the floor",
            replace_line("--langversion:", "--langversion:7.0"),
        ),
        ("relative reference", add_line("-r:lib/Extra.dll")),
        (
            "--out: spelling",
            replace_line("-o:", "--out:obj/Release/net10.0/Bee.dll"),
        ),
        ("-o: with no path", replace_line("-o:", "-o:")),
        (
            "--refout: with no path",
            replace_line("--refout:", "--refout:"),
        ),
        ("two --refout:", add_line("--refout:obj/Other.dll")),
        ("--refonly", add_line("--refonly")),
        (
            "--reference: spelling",
            add_line("--reference:/abs/Extra.dll"),
        ),
        ("a path-valued switch", add_line("--keyfile:key.snk")),
        ("a slash switch", add_line("/nologo")),
        ("a quoted source", add_line("\"Extra.fs\"")),
        (
            "a line break inside an argument",
            add_line("--define:FIRST\r--define:SECOND"),
        ),
        ("a define that is no symbol", add_line("--define:A=B")),
        ("a warning level out of range", add_line("--warn:9")),
        ("warnings that are no numbers", add_line("--nowarn:abc")),
        ("a debug kind outside the list", add_line("--debug:weird")),
        ("a toggle with junk after it", add_line("--optimize*")),
        (
            "a registered reference that is not the producer's output file",
            edit(&|v| {
                let old = v["projects"][1]["projectRefs"][0]["reference"]
                    .as_str()
                    .expect("ref")
                    .to_owned();
                let new = format!("{}NotAy.dll", old.strip_suffix("Ay.dll").expect("Ay.dll"));
                for l in v["projects"][1]["args"].as_array_mut().expect("args") {
                    if l.as_str() == Some(&format!("-r:{old}")) {
                        *l = Value::String(format!("-r:{new}"));
                    }
                }
                v["projects"][1]["projectRefs"][0]["reference"] = Value::String(new);
            }),
        ),
        (
            "unknown project reference",
            edit(&|v| {
                v["projects"][1]["projectRefs"][0]["project"] = Value::String("Nobody".into())
            }),
        ),
        (
            "duplicate id",
            edit(&|v| v["projects"][1]["id"] = Value::String("Ay".into())),
        ),
        (
            "a netmodule target",
            edit(&|v| {
                let ay = v["projects"][0]["args"].as_array_mut().expect("args");
                for l in ay.iter_mut() {
                    if l.as_str().is_some_and(|s| s.starts_with("--target:")) {
                        *l = Value::String("--target:module".into());
                    }
                }
            }),
        ),
        (
            "cycle",
            edit(&|v| {
                // A reverse edge naming Bee's own output file, so only the
                // cycle is wrong with it.
                let bee_out = v["projects"][1]["args"]
                    .as_array()
                    .expect("args")
                    .iter()
                    .find_map(|l| l.as_str()?.strip_prefix("-o:"))
                    .expect("Bee's -o:")
                    .to_owned();
                let bee_file = v["projects"][1]["projectFile"].as_str().expect("file");
                let bee_ref = format!(
                    "{}/{bee_out}",
                    Path::new(bee_file).parent().expect("dir").display()
                );
                v["projects"][0]["args"]
                    .as_array_mut()
                    .expect("args")
                    .push(Value::String(format!("-r:{bee_ref}")));
                v["projects"][0]["projectRefs"] =
                    serde_json::json!([{ "project": "Bee", "reference": bee_ref }]);
            }),
        ),
        (
            "no FSharp.Core reference",
            map_bee_args(&|a: Vec<Value>| {
                a.into_iter()
                    .filter(|l| !l.as_str().is_some_and(|s| s.ends_with("/FSharp.Core.dll")))
                    .collect()
            }),
        ),
        ("one source twice", add_line("./Use.fs")),
        ("no --noframework", drop_line("--noframework")),
        (
            "a platform fsc refuses for a library",
            add_line("--platform:anycpu32bitpreferred"),
        ),
    ];
    // The cycle case is refused for its cycle, not for something else.
    let cycle = &refused
        .iter()
        .find(|(what, _)| *what == "cycle")
        .expect("a cycle case")
        .1;
    match ProjectGraphOracle::default().check_json(cycle) {
        Err(FcsInvokeError::Refused(why)) if why.contains("cycle") => {}
        other => panic!("the cycle must be refused as a cycle: {other:?}"),
    }
    // Inside the domain: other spellings each grammar admits.
    let admitted: Vec<String> = [
        "--nowarn:FS0025,3370;44",
        "--warnon:3390",
        "--warnaserror+",
        "--warnaserror-:3239",
        "--debug:full",
        "--debug-",
        "--checknulls+",
        "--crossoptimize-",
        "--platform:x64",
        "--define:DEBUG_1",
    ]
    .into_iter()
    .map(add_line)
    .collect();
    let mut oracle = ProjectGraphOracle::default();
    assert!(
        oracle.check_json(&valid.to_string()).is_ok(),
        "the unedited request is accepted"
    );
    let accepted: Vec<&str> = refused
        .iter()
        .filter(|(_, line)| !matches!(oracle.check_json(line), Err(FcsInvokeError::Refused(_))))
        .map(|(what, _)| *what)
        .collect();
    assert!(
        accepted.is_empty(),
        "accepted outside the domain: {accepted:?}"
    );
    let refused_inside: Vec<(&String, FcsInvokeError)> = admitted
        .iter()
        .filter_map(|line| oracle.check_json(line).err().map(|e| (line, e)))
        .collect();
    assert!(
        refused_inside.is_empty(),
        "refused inside the domain: {refused_inside:?}"
    );
    // The transport pairs answers with requests by line, so what is not one
    // line is never sent.
    for not_one_line in [
        String::new(),
        serde_json::to_string_pretty(&valid).expect("json"),
    ] {
        assert!(
            matches!(
                oracle.check_json(&not_one_line),
                Err(FcsInvokeError::Oracle(BatchFailure::NotOneLine))
            ),
            "{not_one_line:?} must not be sent"
        );
    }
}
