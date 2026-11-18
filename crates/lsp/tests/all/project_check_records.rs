//! The project-check oracles (`uses-project-batch`, `xmldoc-batch`) describe
//! the code fsc compiles, as it is when they are asked.
//!
//! Each takes its records from FCS's whole-project check. Three things could
//! still put something other than the build's code in a record, and each case
//! here puts one to both oracles:
//!
//! - a `#line` directive, which moves where FCS reports a range, so a record
//!   keyed by the reported file would hold another file's diagnostics;
//! - a resident oracle asked about a file rewritten without its modification
//!   time moving, which FCS would answer from the text it checked before;
//! - a script directive under `#if EDITING` in the first source, which the
//!   script resolution that supplies the SDK's references reads with
//!   `EDITING` defined, as fsc does not.

use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::common::{ensure_fsharp_compiler_service_dll, fcs_dump_batch_child, host_fs};

const ORACLES: [&str; 2] = ["uses-project-batch", "xmldoc-batch"];

fn write(path: &Path, text: &str) {
    std::fs::write(path, text).expect("write fixture");
}

/// `oracle`'s answer for the project of `paths`, a `BatchError` panicking.
fn check(child: &mut borzoi_oracle_harness::BatchChild, oracle: &str, paths: &[&Path]) -> Value {
    let request = serde_json::json!({
        "paths": paths.iter().map(|p| p.display().to_string()).collect::<Vec<_>>(),
        "refs": [],
    })
    .to_string();
    let line = child.request(&request);
    let v: Value = serde_json::from_str(&line)
        .unwrap_or_else(|e| panic!("{oracle}: unparseable response ({e}): {line}"));
    if let Some(err) = v.get("BatchError") {
        panic!("{oracle} refused the request: {err}");
    }
    v
}

/// The record of the file named `name`.
fn record<'a>(answer: &'a Value, name: &str) -> &'a Value {
    answer["Files"]
        .as_array()
        .expect("Files")
        .iter()
        .find(|f| {
            Path::new(f["Path"].as_str().expect("Path"))
                .file_name()
                .is_some_and(|n| n == name)
        })
        .unwrap_or_else(|| panic!("no record for {name}: {answer}"))
}

fn error_numbers(file: &Value) -> Vec<i64> {
    file["Diagnostics"]
        .as_array()
        .expect("Diagnostics")
        .iter()
        .filter(|d| d["Severity"] == "Error")
        .map(|d| d["ErrorNumber"].as_i64().expect("ErrorNumber"))
        .collect()
}

/// The names of the uses in a record, under either oracle's spelling.
fn use_names(file: &Value) -> Vec<String> {
    file["Uses"]
        .as_array()
        .expect("Uses")
        .iter()
        .map(|u| {
            u.get("SymbolName")
                .or_else(|| u.get("Name"))
                .and_then(Value::as_str)
                .expect("a use's name")
                .to_string()
        })
        .collect()
}

/// A `#line` naming another source moves only where FCS would report a
/// range: the error and the binding after it stay in `A.fs`'s record.
#[test]
fn a_line_directive_moves_no_record_to_another_file() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    let b = dir.path().join("B.fs");
    write(
        &a,
        &format!(
            "module A\n#line 1 \"{}\"\nlet movedBinding : int = \"\"\n",
            b.display()
        ),
    );
    write(&b, "module B\nlet y = 1\n");
    for oracle in ORACLES {
        let mut child = fcs_dump_batch_child(oracle);
        let answer = check(&mut child, oracle, &[&a, &b]);
        assert_eq!(
            error_numbers(record(&answer, "A.fs")),
            [1],
            "{oracle}: the error is in A.fs's record: {answer}"
        );
        assert_eq!(
            error_numbers(record(&answer, "B.fs")),
            Vec::<i64>::new(),
            "{oracle}: B.fs's record is clean: {answer}"
        );
        assert!(
            use_names(record(&answer, "A.fs")).contains(&"movedBinding".to_string()),
            "{oracle}: the binding is in A.fs's record: {answer}"
        );
    }
}

/// A resident oracle reads the sources as they are now: a file rewritten
/// with its modification time put back is answered from its new text.
#[test]
fn a_rewrite_that_keeps_the_modification_time_is_read() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    for oracle in ORACLES {
        let mut child = fcs_dump_batch_child(oracle);
        write(&a, "module A\nlet before = 1\n");
        let stamp = host_fs::metadata(&a)
            .and_then(|m| m.modified())
            .expect("modification time");
        let first = check(&mut child, oracle, &[&a]);
        assert!(
            use_names(record(&first, "A.fs")).contains(&"before".to_string()),
            "{oracle}: {first}"
        );
        write(&a, "module A\nlet afterw = 1\n");
        host_fs::set_modified(&a, stamp).expect("restore the modification time");
        let second = check(&mut child, oracle, &[&a]);
        let names = use_names(record(&second, "A.fs"));
        assert!(
            names.contains(&"afterw".to_string()) && !names.contains(&"before".to_string()),
            "{oracle}: the second answer reads the new text: {second}"
        );
    }
}

/// A `#r` under `#if EDITING` is not a reference of the build's: the type it
/// would supply is unbound, as fsc reports (FS0039).
#[test]
fn a_reference_under_editing_is_not_read() {
    let dir = tempfile::tempdir().expect("temp dir");
    let dll = ensure_fsharp_compiler_service_dll();
    let script: PathBuf = dir.path().join("A.fsx");
    write(
        &script,
        &format!(
            "#if EDITING\n#r \"{}\"\n#endif\nlet z = FSharp.Compiler.Text.Range.Zero\n",
            dll.display()
        ),
    );
    for oracle in ORACLES {
        let mut child = fcs_dump_batch_child(oracle);
        let answer = check(&mut child, oracle, &[&script]);
        assert!(
            error_numbers(record(&answer, "A.fsx")).contains(&39),
            "{oracle}: the build does not reference the assembly, so the type is unbound: {answer}"
        );
    }
}
