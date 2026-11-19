//! The resident ops of `fcs-dump` refuse a source or a reference that is not
//! a regular file, before anything opens it.
//!
//! An open of a FIFO for reading waits for a writer, for ever, so a request
//! naming one wedged the resident child until its driver's deadline killed
//! it; a character device may be read without end, or read as an empty file
//! fsc would not be handed. The refusal names the file and what it is.

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
        for (what, request) in [
            ("a FIFO source", ask(&fifo, None)),
            ("a device source", ask(&device, None)),
            ("a FIFO reference", ask(&a, Some(&fifo_dll))),
            ("a device reference", ask(&a, Some(&device_dll))),
        ] {
            let answer = oracle
                .try_request(&request)
                .unwrap_or_else(|e| panic!("{op}, {what}: {e}"));
            let why = refusal(op, &answer);
            assert!(
                why.contains("not a regular file"),
                "{op}, {what}: the refusal says why: {why}"
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
    for name in ["Lib.dll", "Lib.fs ", "Lib.fs.", "Lib", "--"] {
        let lib = dir.path().join(name);
        std::fs::write(&lib, "module Lib\nlet b = A.a\n").expect("write");
        for op in ["uses-project-batch", "xmldoc-batch", "file-batch"] {
            let request = if op == "file-batch" {
                json!({"kind": "uses", "path": text(&lib), "refs": []}).to_string()
            } else {
                json!({"paths": [text(&a), text(&lib)], "refs": []}).to_string()
            };
            let answer = child(op)
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
