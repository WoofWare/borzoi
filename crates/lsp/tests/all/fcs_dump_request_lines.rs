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

fn hostile_lines(good: &Value, path_field: &str) -> Vec<(&'static str, String)> {
    let line = good.to_string();
    let mut lines = vec![
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
        ("an array", json!([good]).to_string()),
        ("a trailing comma", line.replacen('}', ",}", 1)),
    ];
    lines.push((
        "a language version FCS would read as a switch",
        with_field(good, "langversion", json!("?")),
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
    let mut hostile: Vec<(&str, Vec<u8>)> = hostile_lines(&good, path_field)
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
