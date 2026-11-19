//! The resident ops of `fcs-dump` refuse a source or a reference that is not
//! a regular file, before anything opens it, and FCS opens no such file for
//! them, whatever names it (a script's `#load`, a reference spelt with
//! blanks around it).
//!
//! An open of a FIFO for reading waits for a writer, for ever, so a request
//! naming one wedged the resident child until its driver's deadline killed
//! it; a character device may be read without end, or read as an empty file
//! fsc would not be handed. The refusal names the file and what it is.

#![cfg(unix)]

use std::os::unix::fs::symlink;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use borzoi_oracle_harness::BatchChild;
use borzoi_spawn::BoundedCommand;
use serde_json::{Value, json};

use crate::common::fcs_dump_command;

/// A resident `op` child whose answers are bounded well below a hang.
fn child(op: &'static str) -> BatchChild {
    BatchChild::with_factory(
        Box::new(move || fcs_dump_command(op)),
        format!("fcs-dump {op}"),
        Duration::from_secs(120),
        1,
    )
}

fn mkfifo(path: &Path) {
    let mut cmd = Command::new("mkfifo");
    cmd.arg(path);
    BoundedCommand::new(cmd).run_ok("mkfifo");
}

/// The refusal `answer` holds, failing if it is an answer.
fn refusal(op: &str, answer: &str) -> String {
    let value: Value = serde_json::from_str(answer).expect("JSON");
    value["BatchError"]
        .as_str()
        .unwrap_or_else(|| panic!("{op} must refuse, and answered {answer}"))
        .to_owned()
}

/// Each special file in turn at a source's path and at a reference's, put
/// to each resident op, is refused as not a regular file; and the child then
/// answers a good request.
#[test]
fn a_source_or_reference_that_is_not_a_regular_file_is_refused_unopened() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    std::fs::write(&a, "module A\nlet a = 1\n").expect("write");
    let fifo = dir.path().join("Fifo.fs");
    mkfifo(&fifo);
    let fifo_dll = dir.path().join("Fifo.dll");
    mkfifo(&fifo_dll);
    let device = dir.path().join("Device.fs");
    symlink("/dev/null", &device).expect("link to a device");
    let device_dll = dir.path().join("Device.dll");
    symlink("/dev/null", &device_dll).expect("link to a device");
    let fifo_script = dir.path().join("Fifo.fsx");
    mkfifo(&fifo_script);
    let loads_fifo = dir.path().join("Loads.fsx");
    std::fs::write(&loads_fifo, "#load \"Fifo.fsx\"\nlet z = 1\n").expect("write");
    let references_device = dir.path().join("References.fsx");
    std::fs::write(&references_device, "#r \"Device.dll\"\nlet z = 1\n").expect("write");
    let text = |p: &Path| p.display().to_string();
    let project =
        |paths: Vec<String>, refs: Vec<String>| json!({"paths": paths, "refs": refs}).to_string();
    let file = |path: String, refs: Vec<String>| {
        json!({"kind": "uses", "path": path, "refs": refs}).to_string()
    };
    for op in ["uses-project-batch", "xmldoc-batch", "file-batch"] {
        let mut oracle = child(op);
        let ask = |source: &Path, reference: Option<&Path>| {
            let refs: Vec<String> = reference.map(text).into_iter().collect();
            if op == "file-batch" {
                file(text(source), refs)
            } else if source == a {
                project(vec![text(&a)], refs)
            } else {
                project(vec![text(&a), text(source)], refs)
            }
        };
        // Each case, and what its refusal must name.
        const SPECIAL: &str = "not a regular file";
        let mut cases = vec![
            ("a FIFO source", ask(&fifo, None), SPECIAL),
            ("a device source", ask(&device, None), SPECIAL),
            ("a FIFO reference", ask(&a, Some(&fifo_dll)), SPECIAL),
            ("a device reference", ask(&a, Some(&device_dll)), SPECIAL),
        ];
        if op == "file-batch" {
            // FCS resolves a script's directives itself. A reference with
            // blanks around it may be refused for those, or as the FIFO it
            // names once trimmed, but never opened.
            cases.push((
                "a script that loads a FIFO",
                file(text(&loads_fifo), vec![]),
                SPECIAL,
            ));
            // FCS reports a reference it could not open as a diagnostic and
            // goes on: the answer would describe a check without it.
            cases.push((
                "a script that references a device",
                file(text(&references_device), vec![]),
                SPECIAL,
            ));
            cases.push((
                "a FIFO reference spelt through a missing directory, read for its metadata",
                json!({
                    "kind": "assembly-entities",
                    "path": text(&a),
                    "refs": [format!("{}/missing/../Fifo.dll", dir.path().display())],
                })
                .to_string(),
                SPECIAL,
            ));
            cases.push((
                "a FIFO reference with blanks around it",
                file(text(&a), vec![format!(" {} ", text(&fifo_dll))]),
                "Fifo.dll",
            ));
        }
        for (what, request, reason) in cases {
            let answer = oracle
                .try_request(&request)
                .unwrap_or_else(|e| panic!("{op}, {what}: {e}"));
            let why = refusal(op, &answer);
            assert!(
                why.contains(reason),
                "{op}, {what}: the refusal names {reason:?}: {why}"
            );
        }
        let good = if op == "file-batch" {
            file(text(&a), vec![])
        } else {
            project(vec![text(&a)], vec![])
        };
        let answer = oracle.try_request(&good).expect("the good request");
        assert!(
            serde_json::from_str::<Value>(&answer).expect("JSON")["BatchError"].is_null(),
            "{op}: {answer}"
        );
    }
}

/// A source whose name does not end in an F# source suffix is refused: FCS
/// reports it in no record (only a project-wide FS0226), and fsc reads such
/// an argument otherwise (a `.dll` as a reference, a name with a trailing
/// space or dot, or none, as an error), so no record could describe it.
#[test]
fn a_source_not_named_as_fsharp_source_is_refused() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    std::fs::write(&a, "module A\nlet a = 1\n").expect("write");
    let text = |p: &Path| p.display().to_string();
    let names = ["Lib.dll", "Lib.fs ", "Lib.fs.", "Lib", "--"];
    for name in names {
        std::fs::write(dir.path().join(name), "module Lib\nlet b = A.a\n").expect("write");
    }
    for op in ["uses-project-batch", "xmldoc-batch", "file-batch"] {
        let mut oracle = child(op);
        for name in names {
            let lib = dir.path().join(name);
            let request = if op == "file-batch" {
                json!({"kind": "uses", "path": text(&lib), "refs": []}).to_string()
            } else {
                json!({"paths": [text(&a), text(&lib)], "refs": []}).to_string()
            };
            let answer = oracle
                .try_request(&request)
                .unwrap_or_else(|e| panic!("{op}, {name:?}: {e}"));
            let why = refusal(op, &answer);
            assert!(
                why.contains("F# source"),
                "{op}, {name:?}: the refusal says why: {why}"
            );
        }
    }
    // The suffix is compared as FCS compares it, ignoring case.
    let upper = dir.path().join("UPPER.FS");
    std::fs::write(&upper, "module UPPER\nlet c = 1\n").expect("write");
    let answer = child("uses-project-batch")
        .try_request(&json!({"paths": [text(&upper)], "refs": []}).to_string())
        .expect("answered");
    assert!(
        serde_json::from_str::<Value>(&answer).expect("JSON")["BatchError"].is_null(),
        "{answer}"
    );
}

/// The resident path-reading ops (`ast-batch`, the token batches) refuse a
/// FIFO on its own line, and answer the next path.
#[test]
fn a_path_batch_answers_a_fifo_with_an_error_and_goes_on() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    std::fs::write(&a, "module A\nlet a = 1\n").expect("write");
    let fifo = dir.path().join("Fifo.fs");
    mkfifo(&fifo);
    for op in [
        "ast-batch",
        "tokens-filtered-batch",
        "tokens-raw-batch",
        "tokens-lexfilter-internal-batch",
    ] {
        let input = format!("{}\n{}\n", fifo.display(), a.display());
        let out = BoundedCommand::new(fcs_dump_command(op))
            .stdin_bytes(input.into_bytes())
            .timeout(Duration::from_secs(120))
            .run_ok(format_args!("fcs-dump {op}"));
        let lines: Vec<Value> = String::from_utf8(out.stdout)
            .expect("UTF-8")
            .lines()
            .map(|l| serde_json::from_str(l).expect("JSON"))
            .collect();
        assert_eq!(lines.len(), 2, "{op}: one line per path: {lines:?}");
        let error = lines[0]["Error"].as_str().unwrap_or_default();
        assert!(error.contains("not a regular file"), "{op}: {:?}", lines[0]);
        assert!(lines[1].get("Error").is_none(), "{op}: {:?}", lines[1]);
    }
}
