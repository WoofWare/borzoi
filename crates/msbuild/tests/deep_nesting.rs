//! Deep input at every recursive entry point: never a crash, and certain
//! implies exact at the boundary.
//!
//! A stack overflow is not a panic. It aborts the whole process, so a
//! `global.json`, a `Condition` or a property body nested deeply enough on
//! disk takes the LSP down, and no `catch_unwind` can save it. Each recursive
//! descent the crate runs over user text is therefore bounded, and this file
//! holds each bound to two obligations:
//!
//! - **No abort.** Every deep input runs on a thread with an explicit 2 MiB
//!   stack (the Rust test harness's own default, and the debug build's frames
//!   are the large ones), at a depth far past the bound. Before the bounds,
//!   each of these inputs aborted the test binary outright.
//! - **Certain implies exact at the boundary.** At the bound itself the
//!   evaluator must still *commit*, and MSBuild (`tools/msbuild-condition-oracle`)
//!   must agree with what it commits; one level past it, it must decline.
//!   MSBuild evaluates far deeper than our bounds before it overflows its own
//!   stack, so a decline there is a coverage loss and never a wrong answer.
//!
//! `And`/`Or` chains are not nesting: they are held flat, so a chain of any
//! length evaluates exactly, and the oracle grades a long one.
//!
//! The parse-everything entry point (`parse_fsproj`) is driven with each deep
//! shape too, since it reaches the condition evaluator, property expansion and
//! the reference scans the trust layer runs over every body.

mod common;

use std::collections::HashMap;
use std::path::Path;
use std::sync::mpsc;
use std::time::Duration;

use borzoi_msbuild::test_support::{
    GLOBAL_JSON_MAX_DEPTH, Issue, MAX_CONDITION_NESTING, MAX_EXPRESSION_NESTING, Outcome,
    PropertyMap, evaluate, property_references, substitute,
};
use borzoi_msbuild::{GlobalJsonError, parse_fsproj, parse_global_json};
use common::{
    ExpandVerdict, Oracle, Verdict, check_certain_implies_exact, check_expand_certain_implies_exact,
};

/// Far past every bound, and past the depth at which MSBuild itself overflows
/// its stack on the oracle (10,000 nested property functions; 100,000 nested
/// parentheses, `!`s or chained `And`s).
const DEEP: usize = 100_000;

/// Run `f` on a thread with a 2 MiB stack and wait for it. A stack overflow
/// aborts the process (the failure this file exists to catch); a scan that is
/// super-linear in the depth instead blows the deadline, which is generous
/// enough for a loaded machine and still far short of a quadratic scan of
/// [`DEEP`] levels, which runs for hours.
fn on_small_stack<T: Send + 'static>(what: &str, f: impl FnOnce() -> T + Send + 'static) -> T {
    let (tx, rx) = mpsc::channel();
    let handle = std::thread::Builder::new()
        .name(what.to_string())
        .stack_size(2 << 20)
        .spawn(move || {
            let _ = tx.send(f());
        })
        .expect("spawn a 2 MiB thread");
    match rx.recv_timeout(Duration::from_secs(120)) {
        Ok(value) => {
            handle.join().expect("thread finished");
            value
        }
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("{what}: still running after 120 s on deep input")
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            // The closure panicked; surface its message.
            match handle.join() {
                Err(payload) => std::panic::resume_unwind(payload),
                Ok(()) => unreachable!("sender dropped without sending or panicking"),
            }
        }
    }
}

fn nest(open: &str, leaf: &str, close: &str, depth: usize) -> String {
    let mut out = String::with_capacity((open.len() + close.len()) * depth + leaf.len());
    for _ in 0..depth {
        out.push_str(open);
    }
    out.push_str(leaf);
    for _ in 0..depth {
        out.push_str(close);
    }
    out
}

// ============================================================================
// global.json
// ============================================================================

/// `{"x": [[…]]}` with `depth` containers in all, the top-level object included.
fn global_json_arrays(depth: usize) -> String {
    format!(
        "{{\"sdk\": {{\"version\": \"9.0.100\"}}, \"x\": {}}}",
        nest("[", "", "]", depth - 1)
    )
}

/// `{"a": {"a": … 1 …}}` with `depth` objects.
fn global_json_objects(depth: usize) -> String {
    nest("{\"a\": ", "1", "}", depth)
}

fn is_depth_refusal(result: Result<borzoi_msbuild::GlobalJson, GlobalJsonError>) -> bool {
    matches!(result, Err(GlobalJsonError::Syntax { message, .. }) if message.contains("maximum configured depth"))
}

/// The `dotnet` CLI reads `global.json` with `System.Text.Json` at its default
/// `MaxDepth` of 64 before anything else: nested 64 deep, `dotnet msbuild`
/// evaluates the project; 65 deep, every `dotnet` command fails with "The
/// maximum configured depth of 64 has been exceeded" (probed against SDK
/// 10.0.401 with exactly [`global_json_arrays`]'s shape). So the boundary is
/// the reference's, and both sides of it are pinned here.
#[test]
fn global_json_depth_is_the_dotnet_clis() {
    assert_eq!(
        GLOBAL_JSON_MAX_DEPTH, 64,
        "the CLI's System.Text.Json MaxDepth"
    );
    on_small_stack("global.json boundary", || {
        let at = parse_global_json(&global_json_arrays(GLOBAL_JSON_MAX_DEPTH))
            .expect("64 containers deep is a document the CLI reads");
        assert_eq!(
            at.sdk.and_then(|s| s.version).map(|v| v.to_string()),
            Some("9.0.100".to_string()),
            "the sdk block still reads at the boundary"
        );
        parse_global_json(&global_json_objects(GLOBAL_JSON_MAX_DEPTH))
            .expect("64 objects deep is a document the CLI reads");

        assert!(is_depth_refusal(parse_global_json(&global_json_arrays(
            GLOBAL_JSON_MAX_DEPTH + 1
        ))));
        assert!(is_depth_refusal(parse_global_json(&global_json_objects(
            GLOBAL_JSON_MAX_DEPTH + 1
        ))));
    });
}

#[test]
fn deep_global_json_is_refused_without_aborting() {
    on_small_stack("deep global.json", || {
        assert!(is_depth_refusal(parse_global_json(&global_json_arrays(
            DEEP
        ))));
        assert!(is_depth_refusal(parse_global_json(&global_json_objects(
            DEEP
        ))));
        // Unterminated, so the parser never gets to see a closing bracket.
        assert!(is_depth_refusal(parse_global_json(&"[".repeat(DEEP))));
    });
}

// ============================================================================
// Conditions
// ============================================================================

fn parens(depth: usize) -> String {
    nest("(", "'a' == 'a'", ")", depth)
}

fn bangs(depth: usize) -> String {
    // An even count, so the value is the leaf's.
    format!("{}true", "!".repeat(depth))
}

/// `(!(!(… false …)))`: both nesting constructs, alternating, `depth`
/// levels in all.
fn mixed(depth: usize) -> String {
    let mut open = String::new();
    let mut close = String::new();
    for level in 0..depth {
        if level % 2 == 0 {
            open.push('(');
            close.push(')');
        } else {
            open.push('!');
        }
    }
    format!("{open}false{close}")
}

fn and_chain(len: usize) -> String {
    vec!["'$(P)' == 'x'"; len].join(" and ")
}

fn or_chain(len: usize) -> String {
    // Every arm false but the last, so evaluation walks the whole chain.
    let mut arms = vec!["'$(P)' == 'y'"; len - 1];
    arms.push("'$(P)' == 'x'");
    arms.join(" or ")
}

fn ours(condition: String, props: &'static [(&'static str, &'static str)]) -> Outcome {
    on_small_stack("condition", move || {
        let mut map = PropertyMap::new();
        for (k, v) in props {
            map.insert(*k, *v);
        }
        evaluate(&condition, &map).outcome
    })
}

const P_IS_X: &[(&str, &str)] = &[("P", "x")];

fn p_is_x() -> Vec<(String, String)> {
    vec![("P".to_string(), "x".to_string())]
}

/// At the bound we commit, MSBuild agrees, and one level more declines.
#[test]
fn condition_nesting_boundary_is_exact() {
    let mut oracle = Oracle::spawn();
    for (name, shape) in [
        ("parens", parens as fn(usize) -> String),
        ("bangs", bangs),
        ("mixed", mixed),
    ] {
        let at = shape(MAX_CONDITION_NESTING);
        // Our verdict on a 2 MiB stack first, then the graded one.
        assert!(
            matches!(ours(at.clone(), &[]), Outcome::True | Outcome::False),
            "{name} at the bound"
        );
        let verdict = check_certain_implies_exact(&mut oracle, &at, &[]);
        assert!(
            matches!(verdict, Verdict::True | Verdict::False),
            "{name} at the bound commits"
        );

        let past = shape(MAX_CONDITION_NESTING + 1);
        assert_eq!(
            ours(past.clone(), &[]),
            Outcome::Unsupported,
            "{name} one level past the bound declines"
        );
        assert!(
            oracle.eval(&past, &[]).is_some(),
            "MSBuild evaluates {name} one level past our bound, so the decline is a coverage loss, not agreement with a refusal"
        );
    }
}

#[test]
fn deep_conditions_decline_without_aborting() {
    for shape in [parens as fn(usize) -> String, bangs, mixed] {
        assert_eq!(ours(shape(DEEP), &[]), Outcome::Unsupported);
    }
    // Unbalanced: the parser descends before it can know the input is bad.
    assert_eq!(ours("(".repeat(DEEP), &[]), Outcome::Unsupported);
    assert_eq!(ours("!".repeat(DEEP), &[]), Outcome::Unsupported);
}

/// Chains are flat, so their length costs no stack and they evaluate exactly
/// at any length. 10,000 is as long as MSBuild gets before it overflows its
/// own stack, so that is the length the oracle grades.
#[test]
fn long_chains_evaluate_exactly() {
    let mut oracle = Oracle::spawn();
    for chain in [and_chain(10_000), or_chain(10_000)] {
        assert_eq!(ours(chain.clone(), P_IS_X), Outcome::True);
        assert_eq!(
            check_certain_implies_exact(&mut oracle, &chain, &p_is_x()),
            Verdict::True
        );
    }
    // Precedence survives flattening: `And` binds tighter than `Or`.
    for (condition, expected) in [
        ("'a' == 'b' or 'a' == 'a' and 'a' == 'b'", Verdict::False),
        ("'a' == 'a' or 'a' == 'b' and 'a' == 'b'", Verdict::True),
        ("'a' == 'b' and 'a' == 'a' or 'a' == 'a'", Verdict::True),
        (
            "('a' == 'b' or 'a' == 'a') and !('a' == 'b' and 'a' == 'a')",
            Verdict::True,
        ),
    ] {
        assert_eq!(
            check_certain_implies_exact(&mut oracle, condition, &[]),
            expected,
            "{condition}"
        );
    }
}

#[test]
fn deep_chains_evaluate_without_aborting() {
    assert_eq!(ours(and_chain(DEEP), P_IS_X), Outcome::True);
    assert_eq!(ours(or_chain(DEEP), P_IS_X), Outcome::True);
}

// ============================================================================
// Property functions
// ============================================================================

/// `$([MSBuild]::EnsureTrailingSlash($([MSBuild]::EnsureTrailingSlash('a'))))`
/// with `depth` calls: every level is one the evaluator commits on, so the
/// nesting itself is the only thing that can make it decline.
fn ensure_trailing_slash(depth: usize) -> String {
    nest("$([MSBuild]::EnsureTrailingSlash(", "'a'", "))", depth)
}

/// The same nesting with an instance method innermost, whose argument is a
/// property read: `ETS(…ETS($(P.TrimStart($(Q))))…)`, `depth` `$(…)`s in all.
/// (A uniform `TrimStart` nest cannot be used: a receiver trimmed by its own
/// trimmed value runs out of characters within three levels, and an empty
/// character set declines.)
fn trim_start(depth: usize) -> String {
    nest(
        "$([MSBuild]::EnsureTrailingSlash(",
        "$(P.TrimStart($(Q)))",
        "))",
        depth - 2,
    )
}

/// The same through a quoted argument, `'$(…)'`, alternating the three string
/// delimiters so no literal closes its neighbour.
fn quoted_ensure_trailing_slash(depth: usize) -> String {
    const DELIMS: [char; 3] = ['\'', '`', '"'];
    let mut open = String::new();
    let mut close = String::new();
    for level in 0..depth {
        let d = DELIMS[level % 3];
        open.push_str(&format!("$([MSBuild]::EnsureTrailingSlash({d}"));
        close.insert_str(0, &format!("{d}))"));
    }
    format!("{open}a{close}")
}

fn expand(value: String) -> (String, Vec<Issue>) {
    on_small_stack("expand", move || {
        let mut map = PropertyMap::new();
        map.insert("P", "abc");
        map.insert("Q", "z");
        substitute(&value, &map)
    })
}

fn p_is_abc() -> Vec<(String, String)> {
    vec![
        ("P".to_string(), "abc".to_string()),
        ("Q".to_string(), "z".to_string()),
    ]
}

#[test]
fn expression_nesting_boundary_is_exact() {
    let mut oracle = Oracle::spawn();
    for (name, shape) in [
        (
            "EnsureTrailingSlash",
            ensure_trailing_slash as fn(usize) -> String,
        ),
        ("TrimStart", trim_start),
        ("quoted EnsureTrailingSlash", quoted_ensure_trailing_slash),
    ] {
        let at = shape(MAX_EXPRESSION_NESTING);
        let (_, issues) = expand(at.clone());
        assert!(issues.is_empty(), "{name} at the bound commits: {issues:?}");
        assert_eq!(
            check_expand_certain_implies_exact(&mut oracle, &at, &p_is_abc()),
            ExpandVerdict::Exact,
            "{name} at the bound"
        );

        let past = shape(MAX_EXPRESSION_NESTING + 1);
        let (_, issues) = expand(past.clone());
        assert!(
            matches!(issues.as_slice(), [Issue::Unsupported { .. }]),
            "{name} one level past the bound declines: {issues:?}"
        );
        assert!(
            oracle.expand(&past, &p_is_abc()).is_some(),
            "MSBuild evaluates {name} one level past our bound, so the decline is a coverage loss, not agreement with a refusal"
        );
    }
}

#[test]
fn deep_expressions_decline_without_aborting() {
    for shape in [
        ensure_trailing_slash as fn(usize) -> String,
        trim_start,
        quoted_ensure_trailing_slash,
    ] {
        let (_, issues) = expand(shape(DEEP));
        assert!(
            matches!(issues.as_slice(), [Issue::Unsupported { .. }]),
            "{issues:?}"
        );
    }
    // Unbalanced: no closing paren anywhere.
    let (_, issues) = expand("$([MSBuild]::EnsureTrailingSlash(".repeat(DEEP));
    assert!(!issues.is_empty());
}

/// The trust layer scans every body for the properties it reads. The scan
/// reports a receiver per opener, so it must stay linear in the text, not in
/// the text times the nesting.
#[test]
fn deep_reference_scans_finish() {
    let names = on_small_stack("property_references", || {
        let body = nest("$(P.TrimStart(", "$(Q)", "))", DEEP);
        property_references(&body).len()
    });
    assert_eq!(names, DEEP + 1);
}

// ============================================================================
// The whole evaluation
// ============================================================================

fn evaluate_project(body: String) {
    on_small_stack("parse_fsproj", move || {
        let source = format!("<Project>{body}</Project>");
        parse_fsproj(
            &borzoi_msbuild::ProjectFile::buffer(Path::new("/deep/p.fsproj"), &source)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &HashMap::new(),
        )
        .expect("well-formed XML evaluates");
    });
}

fn xml_attr(text: &str) -> String {
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('"', "&quot;")
        .replace('\'', "&apos;")
}

#[test]
fn deep_project_text_evaluates_without_aborting() {
    for condition in [parens(DEEP), bangs(DEEP), mixed(DEEP), and_chain(DEEP)] {
        let condition = xml_attr(&condition);
        evaluate_project(format!(
            "<PropertyGroup><P Condition=\"{condition}\">1</P></PropertyGroup>\
             <ItemGroup><Compile Include=\"a.fs\" Condition=\"{condition}\" /></ItemGroup>"
        ));
    }
    for value in [
        ensure_trailing_slash(DEEP),
        trim_start(DEEP),
        quoted_ensure_trailing_slash(DEEP),
        nest("$(P.TrimStart(", "$(Q)", "))", DEEP),
    ] {
        let text = xml_attr(&value);
        evaluate_project(format!(
            "<PropertyGroup><P>{text}</P><Q>$(P)</Q></PropertyGroup>\
             <ItemGroup><Compile Include=\"{text}.fs\" /></ItemGroup>"
        ));
    }
    // A condition that fails around a name the walk holds no value of (`X`, a
    // write it refuses), nested deep: the rejection judgement searches it for
    // the expressions on that name, and descends no deeper than the
    // evaluator does, so the search is linear in the text.
    let deep = xml_attr(&nest("$(P.TrimStart(", "$(X)", "))", DEEP));
    evaluate_project(format!(
        "<PropertyGroup><P>abc</P><X>$([System.String]::Copy('d'))</X>\
         <R Condition=\"'{deep}' == 'y'\">1</R></PropertyGroup>"
    ));
}

/// An inline task's body nested deep: the rejection judgement serializes it
/// as MSBuild reads it, descending no deeper than a bound, so it never takes
/// the stack.
#[test]
fn a_deep_inline_task_body_evaluates_without_aborting() {
    let body = nest("<a>", "$(P[9])", "</a>", DEEP);
    evaluate_project(format!(
        "<PropertyGroup><P>abc</P></PropertyGroup>\
         <UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
         <Task>{body}</Task></UsingTask>"
    ));
}

/// A name the walk holds no value of (`X`, a write it refuses), read `width`
/// times over in the argument of a function that throws whatever it returns
/// (no repetition of a value is a version): half as itself, half in
/// distinct calls, so that neither one spelling nor many repeat cheaply.
fn wide_unheld_reads(width: usize) -> String {
    let wide: String = (0..width)
        .map(|i| {
            if i % 2 == 0 {
                "$(X)".to_owned()
            } else {
                format!("$(X.Contains(`{i}`))")
            }
        })
        .collect();
    format!(
        "<PropertyGroup><X>$([System.String]::Copy('d'))</X>\
         <R>$([MSBuild]::VersionLessThan('{wide}', '1.0'))</R></PropertyGroup>"
    )
}

/// A `<When>` the walk cannot decide, with `width` property writes and
/// `width` item groups after them, each group judged in the item pass
/// knowing the writes that reach it.
fn many_groups_on_one_path(width: usize) -> String {
    let writes: String = (0..width)
        .map(|i| format!("<PropertyGroup><P{i}>x</P{i}></PropertyGroup>"))
        .collect();
    let groups: String = (0..width).map(|_| "<ItemGroup />").collect();
    format!("<Choose><When Condition=\"'É' == 'é'\">{writes}{groups}</When></Choose>")
}

/// A `<When>` the walk cannot decide holding `width` sibling `<Choose>`s,
/// each with a write and an item group reading a name, so that every group
/// stands in arms of its own and every sibling's write may reach it.
fn many_groups_on_sibling_paths(width: usize) -> String {
    let chooses: String = (0..width)
        .map(|i| {
            format!(
                "<Choose><When Condition=\"'É' == 'Ê'\"><PropertyGroup><P{i}>x</P{i}></PropertyGroup>\
                 <ItemGroup><I Include=\"$(P0)\" /></ItemGroup></When></Choose>"
            )
        })
        .collect();
    format!("<Choose><When Condition=\"'É' == 'é'\">{chooses}</When></Choose>")
}

/// The groups of [`many_groups_on_one_path`] and of
/// [`many_groups_on_sibling_paths`] ask only of the names they read whether a
/// write reaches them: four times the width costs about four times the time,
/// where gathering every write that reaches each group costs sixteen. Timed
/// as a ratio, as [`wide_unheld_reads_are_struck_in_one_pass`] is.
#[test]
fn groups_ask_only_of_the_writes_they_read() {
    for shape in [many_groups_on_one_path, many_groups_on_sibling_paths] {
        let time = |width: usize| {
            let body = shape(width);
            let start = std::time::Instant::now();
            evaluate_project(body);
            start.elapsed()
        };
        time(100);
        let narrow = time(400);
        let wide = time(1_600);
        let ratio = wide.as_secs_f64() / narrow.as_secs_f64().max(1e-6);
        assert!(
            ratio < 10.0,
            "4× the groups took {ratio:.1}× the time ({narrow:?} → {wide:?})"
        );
    }
}

/// A `<Choose>` of `width` `<When>`s the walk cannot decide, each holding a
/// write and a `<ProjectReference>`, which `rejection::arm_is_dead` asks of
/// every arm.
fn wide_undecided_choose(width: usize) -> String {
    let whens: String = (0..width)
        .map(|i| {
            format!(
                "<When Condition=\"'É' == 'é' And '$(P{i})' == ''\">\
                 <PropertyGroup><P{i}>x</P{i}></PropertyGroup>\
                 <ItemGroup><ProjectReference Include=\"R{i}.fsproj\" /></ItemGroup></When>"
            )
        })
        .collect();
    format!("<Choose>{whens}</Choose>")
}

/// The work the walk does over `body` ([`borzoi_msbuild::test_support::WalkCosts`]),
/// on a 2 MiB stack.
fn walk_costs(body: String) -> borzoi_msbuild::test_support::WalkCosts {
    on_small_stack("parse_fsproj", move || {
        let source = format!("<Project>{body}</Project>");
        let (_, costs) = borzoi_msbuild::test_support::count_walk_costs(|| {
            parse_fsproj(
                &borzoi_msbuild::ProjectFile::buffer(Path::new("/deep/p.fsproj"), &source)
                    .expect("a project path spelt as its full path"),
                &HashMap::new(),
                &HashMap::new(),
            )
            .expect("well-formed XML evaluates")
        });
        costs
    })
}

/// Whether each arm of [`wide_undecided_choose`] is one MSBuild cannot take
/// is decided once per `<When>` for the whole chain
/// (`rejection::arm_is_dead`): `n` arms cost `n` decisions, where deciding
/// every earlier `<When>` again for each arm costs `n(n + 1) / 2`. Counted,
/// so no load on the machine moves it.
#[test]
fn a_wide_undecided_choose_decides_each_when_once() {
    for width in [1, 2, 500, 2_000] {
        let decisions = walk_costs(wide_undecided_choose(width)).arm_gate_decisions;
        assert_eq!(
            decisions, width as u64,
            "{width} arms took {decisions} decisions"
        );
    }
}

/// The rejection judgement strikes each read of [`wide_unheld_reads`] with a
/// value in one pass over the text, so four times the width costs about four
/// times the time; striking one read at a time over the whole text costs
/// sixteen. Timed as a ratio of two runs on one machine, which a loaded
/// machine slows alike.
#[test]
fn wide_unheld_reads_are_struck_in_one_pass() {
    let time = |width: usize| {
        let body = wide_unheld_reads(width);
        let start = std::time::Instant::now();
        evaluate_project(body);
        start.elapsed()
    };
    // Warm the allocator and the code once before timing.
    time(DEEP / 16);
    let narrow = time(DEEP / 4);
    let wide = time(DEEP);
    let ratio = wide.as_secs_f64() / narrow.as_secs_f64().max(1e-6);
    assert!(
        ratio < 10.0,
        "4× the width took {ratio:.1}× the time ({narrow:?} → {wide:?})"
    );
}

/// An inline task of `width` parameters, no two named alike.
fn wide_parameter_group(width: usize) -> String {
    let parameters: String = (0..width)
        .map(|i| format!("<P{i} ParameterType=\"System.String\" Required=\"false\" />"))
        .collect();
    format!(
        "<UsingTask TaskName=\"X\" TaskFactory=\"RoslynCodeTaskFactory\" AssemblyFile=\"y.dll\">\
         <ParameterGroup>{parameters}</ParameterGroup><Task>x</Task></UsingTask>"
    )
}

/// A `<UsingTask>`'s parameter names are checked for a repeat, as the loader
/// keys them and as the registration folds them, by sorting them
/// (`loader::first_repeat`): `n` parameters cost `O(n log n)` comparisons,
/// where checking each against every earlier one costs `n(n - 1) / 2`.
/// Counted, so no load on the machine moves it.
#[test]
fn a_wide_parameter_group_is_registered_in_one_pass() {
    for width in [500_u64, 2_000] {
        let comparisons = walk_costs(wide_parameter_group(width as usize)).name_comparisons;
        let log = u64::from(width.ilog2()) + 1;
        assert!(comparisons > 0, "{width} parameters made no comparison");
        assert!(
            comparisons <= 4 * width * log,
            "{width} parameters took {comparisons} comparisons"
        );
    }
}
