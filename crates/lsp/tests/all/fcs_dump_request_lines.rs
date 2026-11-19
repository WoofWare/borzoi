//! The resident JSON ops of `fcs-dump` ([`JSON_OPS`]) answer each line they
//! read with one line, and read a line as exactly one request or refuse it.
//!
//! The answers are matched to the requests by position, so a line read as no
//! request (a blank one, skipped) moves every later answer onto the request
//! before it. And a line read leniently is a request the oracle answers
//! otherwise than its caller asked: whitespace a trimming reader removes, a
//! field of the wrong type taken as absent, an unknown field ignored, a key
//! given twice. Each such line is refused on its own line, and the good
//! request after them gets the answer the first one got.

use std::path::Path;

use borzoi_spawn::BoundedCommand;
use serde_json::{Value, json};

use crate::common::fcs_dump_command;

/// The answer lines `op` writes for `lines`, each ended by a line feed, sent
/// in one batch.
fn answers(op: &str, lines: &[Vec<u8>]) -> Vec<String> {
    let input: Vec<u8> = lines
        .iter()
        .flat_map(|l| [l.as_slice(), b"\n"].concat())
        .collect();
    let out = BoundedCommand::new(fcs_dump_command(op))
        .stdin_bytes(input)
        .run_ok(format_args!("fcs-dump {op}"));
    String::from_utf8(out.stdout)
        .expect("UTF-8")
        .lines()
        .map(str::to_owned)
        .collect()
}

/// Whether `answer` is a refusal (`{"BatchError": <text>}`) rather than an
/// answer (an object holding `Uses` or `Files`).
///
/// # Panics
///
/// If it is neither: the oracle wrote something that is no answer at all.
fn is_refusal(answer: &str) -> bool {
    let value: Value = serde_json::from_str(answer)
        .unwrap_or_else(|e| panic!("an answer is JSON ({e}): {answer}"));
    match value.get("BatchError") {
        Some(Value::String(_)) => true,
        Some(other) => panic!("a refusal's message is text: {other}"),
        None => {
            assert!(
                value.get("Uses").is_some() || value.get("Files").is_some(),
                "an answer holds Uses or Files: {answer}"
            );
            false
        }
    }
}

/// `good` as written, with `field` set to `value`, given twice, or added.
fn with_field(good: &Value, field: &str, value: Value) -> String {
    let mut v = good.clone();
    v[field] = value;
    v.to_string()
}

fn duplicated(good: &Value, field: &str) -> String {
    let text = good.to_string();
    let extra = format!("{}:{},", json!(field), good[field]);
    text.replacen('{', &format!("{{{extra}"), 1)
}

/// The ops that read one JSON request per line, each held to its framing
/// here.
const JSON_OPS: &[&str] = &[
    "file-batch",
    "uses-project-batch",
    "xmldoc-batch",
    "uses-project-graph-batch",
];

/// The batch ops that read one path per line. Their driver
/// (`BatchChild::try_request`) refuses to send a blank or multi-line request,
/// so their framing is not held here.
const PATH_OPS: &[&str] = &[
    "ast-batch",
    "tokens-filtered-batch",
    "tokens-raw-batch",
    "tokens-lexfilter-internal-batch",
    "attrs-batch",
    "script-options-batch",
    "uses-census-batch",
    "types-census-batch",
];

/// Every batch op `fcs-dump` dispatches is one of [`JSON_OPS`] or
/// [`PATH_OPS`], so a new op is held to one rule or the other.
#[test]
fn every_batch_op_is_classified() {
    let program = crate::common::host_fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tools/fcs-dump/Program.fs"),
    )
    .expect("read fcs-dump's source");
    let mut dispatched: Vec<&str> = program
        .split("| [| \"")
        .skip(1)
        .filter_map(|rest| rest.split('"').next())
        .filter(|mode| mode.ends_with("-batch"))
        .collect();
    dispatched.sort_unstable();
    dispatched.dedup();
    let mut classified: Vec<&str> = JSON_OPS.iter().chain(PATH_OPS).copied().collect();
    classified.sort_unstable();
    assert_eq!(
        dispatched, classified,
        "each batch op is a JSON op or a path op"
    );
}

/// Lines that are not one line of one request, whatever the op.
fn framing_lines(good: &Value) -> Vec<(&'static str, String)> {
    let line = good.to_string();
    vec![
        ("a blank line", String::new()),
        ("a line of blanks", "  \t".into()),
        ("a trailing no-break space", format!("{line}\u{a0}")),
        ("a trailing line separator", format!("{line}\u{2028}")),
        ("a leading byte order mark", format!("\u{feff}{line}")),
    ]
}

fn hostile_lines(good: &Value, path_field: &str) -> Vec<(&'static str, String)> {
    let line = good.to_string();
    let mut lines = framing_lines(good);
    lines.extend([
        (
            "an unknown field",
            with_field(good, "borzoiUnknown", json!(true)),
        ),
        ("a known field in another case", {
            let mut v = good.as_object().unwrap().clone();
            let value = v.remove(path_field).unwrap();
            v.insert(path_field.to_uppercase(), value);
            Value::Object(v).to_string()
        }),
        ("a key twice", duplicated(good, path_field)),
        (
            "refs of the wrong type",
            with_field(good, "refs", json!("x")),
        ),
        (
            "langversion of the wrong type",
            with_field(good, "langversion", json!(false)),
        ),
        ("an array", json!([good]).to_string()),
        ("a trailing comma", line.replacen('}', ",}", 1)),
    ]);
    lines.push((
        "a language version FCS would read as a switch",
        with_field(good, "langversion", json!("?")),
    ));
    lines.push((
        "a language version FCS does not know",
        with_field(good, "langversion", json!("99.0")),
    ));
    lines.push((
        "a misspelt language version",
        with_field(good, "langversion", json!("latestt")),
    ));
    if good.get("defines").is_some() {
        lines.push((
            "a padded symbol",
            with_field(good, "defines", json!([" A "])),
        ));
        lines.push(("a blank symbol", with_field(good, "defines", json!([""]))));
    }
    lines
}

fn assert_each_line_answered(op: &str, good: Value, path_field: &str) {
    assert_each_hostile_line_answered(op, &good, hostile_lines(&good, path_field));
}

fn assert_each_hostile_line_answered(op: &str, good: &Value, hostile: Vec<(&'static str, String)>) {
    let mut hostile: Vec<(&str, Vec<u8>)> = hostile
        .into_iter()
        .map(|(what, line)| (what, line.into_bytes()))
        .collect();
    // A byte that is not UTF-8 inside the path's string: decoded leniently it
    // would name another file.
    let text = good.to_string();
    let quote = text.find(".fs\"").expect("a source path");
    hostile.push((
        "a path holding a byte that is not UTF-8",
        [
            &text.as_bytes()[..quote],
            b"\xff",
            &text.as_bytes()[quote..],
        ]
        .concat(),
    ));
    let mut lines = vec![good.to_string().into_bytes()];
    lines.extend(hostile.iter().map(|(_, l)| l.clone()));
    // A carriage return between tokens is JSON whitespace, and a line ended by
    // a carriage return and a line feed is one line: both are the good
    // request.
    lines.push(text.replacen(',', ",\r", 1).into_bytes());
    lines.push(format!("{text}\r").into_bytes());
    lines.push(good.to_string().into_bytes());
    let got = answers(op, &lines);
    assert_eq!(
        got.len(),
        lines.len(),
        "{op}: one answer per line, and got {} for {}: {got:#?}",
        got.len(),
        lines.len()
    );
    assert!(
        !is_refusal(&got[0]),
        "{op}: the good request is answered: {}",
        got[0]
    );
    for (i, (what, line)) in hostile.iter().enumerate() {
        assert!(
            is_refusal(&got[i + 1]),
            "{op}: {what} ({:?}) must be refused, and got {}",
            String::from_utf8_lossy(line),
            got[i + 1]
        );
    }
    for answer in &got[hostile.len() + 1..] {
        assert_eq!(
            Some(answer),
            got.first(),
            "{op}: the good request, and in step"
        );
    }
}

fn fixture() -> (tempfile::TempDir, String) {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    std::fs::write(&a, "module A\nlet a = 1\n").expect("write");
    // What a request holding a byte that is not UTF-8 in this path names once
    // decoded leniently: so that only a strict decoder refuses it.
    std::fs::write(dir.path().join("A\u{fffd}.fs"), "module A\nlet a = 1\n").expect("write");
    let a = Path::new(&a).display().to_string();
    (dir, a)
}

#[test]
fn file_batch_refuses_each_line_that_is_not_one_request() {
    let (_dir, a) = fixture();
    assert_each_line_answered(
        "file-batch",
        json!({"kind": "uses", "path": a, "refs": [], "langversion": null}),
        "path",
    );
}

#[test]
fn uses_project_batch_refuses_each_line_that_is_not_one_request() {
    let (_dir, a) = fixture();
    assert_each_line_answered(
        "uses-project-batch",
        json!({"paths": [a], "refs": [], "defines": [], "langversion": null, "exclusiveRefs": false}),
        "paths",
    );
}

#[test]
fn uses_project_graph_batch_refuses_each_line_that_is_not_one_request() {
    let (_dir, a) = fixture();
    let good = json!({
        "op": "check",
        "projects": [{
            "id": "a", "assemblyName": "A", "target": "library",
            "sources": [a], "defines": [],
            "references": borzoi_oracle_harness::project_graph::framework_references()
                .iter()
                .map(|dll| json!({"dll": dll}))
                .collect::<Vec<_>>()
        }],
        "check": "a"
    });
    assert_each_hostile_line_answered("uses-project-graph-batch", &good, framing_lines(&good));
}

#[test]
fn xmldoc_batch_refuses_each_line_that_is_not_one_request() {
    let (_dir, a) = fixture();
    assert_each_line_answered(
        "xmldoc-batch",
        json!({"paths": [a], "refs": [], "defines": [], "langversion": null, "exclusiveRefs": false}),
        "paths",
    );
}

/// A `types-project` request checks at FCS's default language version, so it
/// refuses a pin it would not honour.
#[test]
fn types_project_refuses_a_language_version_pin() {
    let (_dir, a) = fixture();
    let lines = vec![
        json!({"kind": "types-project", "paths": [a], "refs": [], "langversion": "7.0"})
            .to_string()
            .into_bytes(),
        json!({"kind": "types-project", "paths": [a], "refs": [], "langversion": null})
            .to_string()
            .into_bytes(),
    ];
    let got = answers("file-batch", &lines);
    assert!(is_refusal(&got[0]), "{}", got[0]);
    assert!(!is_refusal(&got[1]), "{}", got[1]);
}

/// A `file-batch` reference is held to what the project checks hold theirs
/// to: one that names no file (a trailing blank, say) or a file that is no
/// assembly is refused, since FCS drops a reference it cannot read and checks
/// without it (the padded spelling of an assembly is not that assembly). A
/// recognised older language version, and `preview` in any case, are taken.
#[test]
fn file_batch_refuses_a_reference_that_is_not_an_assembly() {
    let (dir, a) = fixture();
    let real = dir.path().join("Real.dll");
    std::fs::copy(crate::common::ensure_system_runtime_dll(), &real).expect("copy an assembly");
    let text = dir.path().join("Text.dll");
    std::fs::write(&text, "not an assembly").expect("write");
    let request = |refs: Vec<String>| {
        json!({"kind": "uses", "path": a, "refs": refs})
            .to_string()
            .into_bytes()
    };
    let lines = vec![
        request(vec![format!("{} ", real.display())]),
        request(vec![dir.path().join("Missing.dll").display().to_string()]),
        request(vec![text.display().to_string()]),
        json!({"kind": "uses", "path": a, "refs": [], "langversion": "7.0"})
            .to_string()
            .into_bytes(),
        json!({"kind": "uses", "path": a, "refs": [], "langversion": "preview"})
            .to_string()
            .into_bytes(),
        json!({"kind": "uses", "path": a, "refs": [], "langversion": "Preview"})
            .to_string()
            .into_bytes(),
        request(vec![real.display().to_string()]),
    ];
    let got = answers("file-batch", &lines);
    for (i, what) in ["padded", "missing", "not an assembly"].iter().enumerate() {
        assert!(is_refusal(&got[i]), "{what}: {}", got[i]);
    }
    assert!(
        !is_refusal(&got[3]),
        "a recognised older version: {}",
        got[3]
    );
    for (i, what) in [(4, "preview"), (5, "Preview, in another case")] {
        assert!(!is_refusal(&got[i]), "{what}: {}", got[i]);
    }
    assert!(
        !is_refusal(&got[6]),
        "the assembly the padded spelling is not: {}",
        got[6]
    );
}
