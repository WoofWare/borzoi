//! The resident JSON ops of `fcs-dump` (`file-batch`, `uses-project-batch`,
//! `xmldoc-batch`) answer each line they read with one line, and read a line
//! as exactly one request or refuse it.
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

/// The answer lines `op` writes for `lines`, sent in one batch.
fn answers(op: &str, lines: &[String]) -> Vec<String> {
    let mut input = lines.join("\n").into_bytes();
    input.push(b'\n');
    let out = BoundedCommand::new(fcs_dump_command(op))
        .stdin_bytes(input)
        .run_ok(format_args!("fcs-dump {op}"));
    String::from_utf8(out.stdout)
        .expect("UTF-8")
        .lines()
        .map(str::to_owned)
        .collect()
}

fn is_refusal(answer: &str) -> bool {
    serde_json::from_str::<Value>(answer)
        .ok()
        .and_then(|v| v.get("BatchError").cloned())
        .is_some()
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

fn hostile_lines(good: &Value, path_field: &str) -> Vec<(&'static str, String)> {
    let line = good.to_string();
    let relative = match &good[path_field] {
        Value::Array(_) => json!(["A.fs"]),
        _ => json!("A.fs"),
    };
    vec![
        ("a blank line", String::new()),
        ("a line of blanks", "  \t".into()),
        ("a trailing no-break space", format!("{line}\u{a0}")),
        ("a trailing line separator", format!("{line}\u{2028}")),
        ("a leading byte order mark", format!("\u{feff}{line}")),
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
        ("a relative path", with_field(good, path_field, relative)),
        ("an array", json!([good]).to_string()),
        ("a trailing comma", line.replacen('}', ",}", 1)),
    ]
}

fn assert_each_line_answered(op: &str, good: Value, path_field: &str) {
    let hostile = hostile_lines(&good, path_field);
    let mut lines = vec![good.to_string()];
    lines.extend(hostile.iter().map(|(_, l)| l.clone()));
    lines.push(good.to_string());
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
            "{op}: {what} ({line:?}) must be refused, and got {}",
            got[i + 1]
        );
    }
    assert_eq!(got.last(), got.first(), "{op}: the oracle stays in step");
}

fn fixture() -> (tempfile::TempDir, String) {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    std::fs::write(&a, "module A\nlet a = 1\n").expect("write");
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
fn xmldoc_batch_refuses_each_line_that_is_not_one_request() {
    let (_dir, a) = fixture();
    assert_each_line_answered(
        "xmldoc-batch",
        json!({"paths": [a], "refs": [], "defines": [], "langversion": null, "exclusiveRefs": false}),
        "paths",
    );
}
