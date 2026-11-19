//! The project-check oracles (`uses-project-batch`, `xmldoc-batch`) describe
//! the code fsc compiles, as it is when they are asked, or refuse.
//!
//! Each takes its records from FCS's whole-project check. These could still
//! put something other than the build's code in a record, and each case here
//! puts one to both oracles:
//!
//! - a `#line` directive, which moves where FCS reports a range (so a record
//!   keyed by the reported file would hold another file's diagnostics) and
//!   what `__SOURCE_FILE__` is. The oracles refuse a source that may hold one.
//! - a resident oracle asked about a file rewritten without its modification
//!   time moving, which FCS would answer from the text it checked before;
//! - a `#r` in a source. Under `#if EDITING` it is no reference of the build's,
//!   and an active one is a reference FCS's project check does not read, so
//!   the oracles refuse a source whose build branches hold one;
//! - a reference that is not a file or not an assembly, which fsc rejects and
//!   FCS's project check does not report, so the oracles refuse it.

use std::path::{Path, PathBuf};
use std::sync::{Mutex, MutexGuard, OnceLock};

use serde_json::Value;

use crate::common::{ensure_fsharp_compiler_service_dll, fcs_dump_batch_child, host_fs};

const ORACLES: [&str; 2] = ["uses-project-batch", "xmldoc-batch"];

/// The resident child of `oracle`, one per oracle for the whole group, held
/// for a test's whole sequence of requests.
fn resident(oracle: &'static str) -> MutexGuard<'static, borzoi_oracle_harness::BatchChild> {
    static CHILDREN: [OnceLock<Mutex<borzoi_oracle_harness::BatchChild>>; 2] =
        [OnceLock::new(), OnceLock::new()];
    let i = ORACLES
        .iter()
        .position(|o| *o == oracle)
        .expect("a project-check oracle");
    CHILDREN[i]
        .get_or_init(|| Mutex::new(fcs_dump_batch_child(oracle)))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

fn write(path: &Path, text: &str) {
    std::fs::write(path, text).expect("write fixture");
}

/// `oracle`'s answer for the project of `paths`: the payload, or the
/// refusal's message.
fn ask(
    child: &mut borzoi_oracle_harness::BatchChild,
    oracle: &str,
    paths: &[&Path],
) -> Result<Value, String> {
    ask_with_refs(child, oracle, paths, &[])
}

/// [`ask`], with `refs` referenced beside the SDK's own: a fixture request.
fn ask_with_refs(
    child: &mut borzoi_oracle_harness::BatchChild,
    oracle: &str,
    paths: &[&Path],
    refs: &[&Path],
) -> Result<Value, String> {
    ask_with(child, oracle, paths, refs, false)
}

/// [`ask_with_refs`] for a real project's inputs, which may change during a
/// run (`inputsMayChange`, the oracle's module doc): a request only a fresh
/// child serves.
fn ask_real(
    child: &mut borzoi_oracle_harness::BatchChild,
    oracle: &str,
    paths: &[&Path],
    refs: &[&Path],
) -> Result<Value, String> {
    ask_with(child, oracle, paths, refs, true)
}

fn ask_with(
    child: &mut borzoi_oracle_harness::BatchChild,
    oracle: &str,
    paths: &[&Path],
    refs: &[&Path],
    inputs_may_change: bool,
) -> Result<Value, String> {
    let request = serde_json::json!({
        "paths": paths.iter().map(|p| p.display().to_string()).collect::<Vec<_>>(),
        "refs": refs.iter().map(|p| p.display().to_string()).collect::<Vec<_>>(),
        "inputsMayChange": inputs_may_change,
    })
    .to_string();
    let line = child.request(&request);
    let v: Value = serde_json::from_str(&line)
        .unwrap_or_else(|e| panic!("{oracle}: unparseable response ({e}): {line}"));
    match v.get("BatchError") {
        Some(err) => Err(err.as_str().unwrap_or_default().to_string()),
        None => Ok(v),
    }
}

/// `oracle`'s answer for the project of `paths`, a refusal panicking.
fn check(child: &mut borzoi_oracle_harness::BatchChild, oracle: &str, paths: &[&Path]) -> Value {
    ask(child, oracle, paths).unwrap_or_else(|err| panic!("{oracle} refused the request: {err}"))
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

/// A source that may hold a line directive is refused: one naming another
/// source would put this file's error in that file's record, and one naming
/// a file of a name `__SOURCE_FILE__` reads changes what the code means.
#[test]
fn a_line_directive_is_refused() {
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
        let mut child = resident(oracle);
        match ask(&mut child, oracle, &[&a, &b]) {
            Err(why) if why.contains("line directive") => {}
            other => panic!("{oracle}: a line directive must be refused: {other:?}"),
        }
    }
}

/// FCS honours a line directive after other text on its line, so that is
/// refused too.
#[test]
fn a_line_directive_after_other_text_is_refused() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    let b = dir.path().join("B.fs");
    write(
        &a,
        &format!(
            "module A\n(* comment *) #line 1 \"{}\"\nlet moved : int = \"\"\n",
            b.display()
        ),
    );
    write(&b, "module B\nlet y = 1\n");
    for oracle in ORACLES {
        let mut child = resident(oracle);
        match ask(&mut child, oracle, &[&a, &b]) {
            Err(why) if why.contains("line directive") => {}
            other => panic!("{oracle}: a line directive must be refused: {other:?}"),
        }
    }
}

/// A reference fsc would reject (FS0084: not a file, or not an assembly) is
/// refused. FCS's project check resolves its references without reporting
/// these, so without the refusal a project with one would look clean.
#[test]
fn an_unreadable_reference_is_refused() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    write(&a, "module A\nlet x = 1\n");
    let missing = dir.path().join("Missing.dll");
    let not_an_assembly = dir.path().join("NotAnAssembly.dll");
    write(&not_an_assembly, "not an assembly");
    for oracle in ORACLES {
        let mut child = resident(oracle);
        for reference in [&missing, &not_an_assembly] {
            match ask_with_refs(&mut child, oracle, &[&a], &[reference]) {
                Err(why) if why.contains("reference") => {}
                other => panic!("{oracle}: {reference:?} must be refused: {other:?}"),
            }
        }
    }
}

/// A child serves a request whose inputs may change only as its first, and
/// nothing after one: a later request of either kind is refused, and so is
/// such a request after a fixture request. So an answer to such a request is
/// the one a fresh process gives, whatever FCS and the CLR keep across
/// requests (the oracle's module doc); the harnesses put each one to a fresh
/// child.
#[test]
fn a_request_whose_inputs_may_change_is_a_fresh_childs_only_one() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    write(&a, "module A\nlet y = 1\n");
    for oracle in ORACLES {
        let mut child = fcs_dump_batch_child(oracle);
        ask_real(&mut child, oracle, &[&a], &[])
            .unwrap_or_else(|err| panic!("{oracle}: a fresh child's first request: {err}"));
        match ask_real(&mut child, oracle, &[&a], &[]) {
            Err(why) if why.contains("start a fresh child") => {}
            other => panic!("{oracle}: a second request must be refused: {other:?}"),
        }
        match ask(&mut child, oracle, &[&a]) {
            Err(why) if why.contains("start a fresh child") => {}
            other => panic!("{oracle}: a fixture request after one must be refused: {other:?}"),
        }

        let mut child = fcs_dump_batch_child(oracle);
        check(&mut child, oracle, &[&a]);
        match ask_real(&mut child, oracle, &[&a], &[]) {
            Err(why) if why.contains("start a fresh child") => {}
            other => panic!("{oracle}: one after a fixture request must be refused: {other:?}"),
        }
        check(&mut child, oracle, &[&a]);
    }
}

/// A fixture reference rewritten in place breaks the precondition the
/// fixture requests rest on (the oracle's module doc), so the next request
/// naming it is refused, naming the path, rather than answered from what FCS
/// kept of the old bytes. However the request spells the path.
#[test]
fn a_fixture_reference_rewritten_in_place_is_refused() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    write(&a, "module A\nlet z = FSharp.Compiler.Text.Range.Zero\n");
    let fcs = ensure_fsharp_compiler_service_dll();
    let other = fcs
        .parent()
        .expect("the oracle's directory")
        .join("FSharp.Core.dll");
    let lib = dir.path().join("Lib.dll");
    let lib_respelled = dir.path().join(".").join("Lib.dll");
    for oracle in ORACLES {
        let mut child = resident(oracle);
        std::fs::copy(&fcs, &lib).expect("copy the referenced assembly");
        let first = ask_with_refs(&mut child, oracle, &[&a], &[&lib])
            .unwrap_or_else(|err| panic!("{oracle} refused: {err}"));
        assert_eq!(
            error_numbers(record(&first, "A.fs")),
            Vec::<i64>::new(),
            "{oracle}: the type resolves in the reference: {first}"
        );
        std::fs::copy(&other, &lib).expect("rewrite the referenced assembly");
        match ask_with_refs(&mut child, oracle, &[&a], &[&lib_respelled]) {
            Err(why)
                if why.contains("reused a path") && why.contains(&lib.display().to_string()) => {}
            other => panic!("{oracle}: a fixture reused a path, which must be refused: {other:?}"),
        }
    }
}

/// Two sources FCS takes for one file (names equal under its culture-aware,
/// case-blind comparison) are refused: one file's record would hold the
/// other's uses, and the other's none.
#[test]
fn sources_fcs_takes_for_one_file_are_refused() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("Slot.fs");
    let b = dir.path().join("Sl\u{ad}ot.fs");
    let c = dir.path().join("Use.fs");
    write(&a, "module Slot\nlet a = 1\n");
    write(&b, "module Slot2\nlet b = 2\n");
    write(&c, "module Use\nlet c = Slot.a + Slot2.b\n");
    for oracle in ORACLES {
        let mut child = resident(oracle);
        match ask(&mut child, oracle, &[&a, &b, &c]) {
            Err(why) if why.contains("one file") => {}
            other => panic!("{oracle}: conflated sources must be refused: {other:?}"),
        }
    }
}

/// A line directive after an operator spelled with `//` is a directive, not
/// a comment, and is refused: no reading of the line short of FCS's lexer
/// tells the two apart, so any directive-shaped text refuses.
#[test]
fn a_line_directive_after_a_slash_operator_is_refused() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    let b = dir.path().join("B.fs");
    write(
        &a,
        &format!(
            "module A\nlet (+//) x y = x + y\nlet t = 1 +// 2 #line 100 \"{}\"\nlet moved : int = \"\"\n",
            b.display()
        ),
    );
    write(&b, "module B\nlet y = 1\n");
    for oracle in ORACLES {
        let mut child = resident(oracle);
        match ask(&mut child, oracle, &[&a, &b]) {
            Err(why) if why.contains("line directive") => {}
            other => panic!("{oracle}: a line directive must be refused: {other:?}"),
        }
    }
}

/// A resident oracle reads the sources as they are now: a file rewritten
/// with its modification time put back is answered from its new text.
#[test]
fn a_rewrite_that_keeps_the_modification_time_is_read() {
    let dir = tempfile::tempdir().expect("temp dir");
    let a = dir.path().join("A.fs");
    for oracle in ORACLES {
        let mut child = resident(oracle);
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

/// An active `#r` in a source names an assembly the build references and the
/// project check does not read, so the request is refused.
#[test]
fn an_active_source_reference_is_refused() {
    let dir = tempfile::tempdir().expect("temp dir");
    let dll = ensure_fsharp_compiler_service_dll();
    let script: PathBuf = dir.path().join("A.fsx");
    write(
        &script,
        &format!(
            "#r \"{}\"\nlet z = FSharp.Compiler.Text.Range.Zero\n",
            dll.display()
        ),
    );
    for oracle in ORACLES {
        let mut child = resident(oracle);
        match ask(&mut child, oracle, &[&script]) {
            Err(why) if why.contains("#r") => {}
            other => panic!("{oracle}: an active #r must be refused: {other:?}"),
        }
    }
}

/// fsc ignores a `#r` in a nested module (FS0236, a warning), so it names
/// nothing the build reads and the project is checked.
#[test]
fn a_reference_in_a_nested_module_is_checked() {
    let dir = tempfile::tempdir().expect("temp dir");
    let script: PathBuf = dir.path().join("A.fsx");
    write(
        &script,
        "module Inner =\n    #r \"Missing.dll\"\n    let x = 1\n",
    );
    for oracle in ORACLES {
        let mut child = resident(oracle);
        let answer = check(&mut child, oracle, &[&script]);
        assert_eq!(
            error_numbers(record(&answer, "A.fsx")),
            Vec::<i64>::new(),
            "{oracle}: {answer}"
        );
        assert_eq!(
            error_numbers(&answer),
            Vec::<i64>::new(),
            "{oracle}: no error in no file either: {answer}"
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
        let mut child = resident(oracle);
        let answer = check(&mut child, oracle, &[&script]);
        assert!(
            error_numbers(record(&answer, "A.fsx")).contains(&39),
            "{oracle}: the build does not reference the assembly, so the type is unbound: {answer}"
        );
    }
}
