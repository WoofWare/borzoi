//! The xml-doc oracle's answer to a request depends on that request alone.
//!
//! The resident `xmldoc-batch` child serves the whole suite in sequence, so
//! any state one request leaves behind moves the answers to later ones,
//! whichever test sent them. The property: a probe project answered after
//! each of a set of earlier requests gets byte for byte the answer a fresh
//! child gives it.
//!
//! The earlier requests are a project that references a DLL (and is checked
//! against it: a type from it resolves), and the ways a project's location
//! can move script resolution: a project under a `global.json`, and a plain
//! project. The probe names a type in that DLL, so it resolves only where the
//! reference leaked: a fresh child reports it unbound. The referencing
//! project is the row that discriminates on every host. The pin names an SDK
//! no machine has, and FCS then falls back to the newest one, so the
//! `global.json` row moves the answer only where that differs from the SDK
//! the probe's own directory selects.

use std::path::{Path, PathBuf};

use super::harness::{OracleFile, fcs_check_or_refusal};
use crate::common::{ensure_fsharp_compiler_service_dll, fcs_dump_batch_child, host_fs};

fn write(path: &Path, text: &str) {
    std::fs::create_dir_all(path.parent().expect("a parent")).expect("create dir");
    std::fs::write(path, text).expect("write file");
}

fn request(paths: &[&Path], refs: &[&Path]) -> String {
    serde_json::json!({
        "paths": paths.iter().map(|p| p.display().to_string()).collect::<Vec<_>>(),
        "refs": refs.iter().map(|p| p.display().to_string()).collect::<Vec<_>>(),
    })
    .to_string()
}

#[test]
fn an_answer_does_not_depend_on_earlier_requests() {
    let root = tempfile::TempDir::new().expect("temp dir");
    let root = root.path();
    let dll = ensure_fsharp_compiler_service_dll();

    let referencing = root.join("referencing/A.fs");
    write(
        &referencing,
        "module A\nlet a = FSharp.Compiler.Text.Range.Zero\n",
    );
    let pinned = root.join("pinned");
    write(
        &pinned.join("global.json"),
        r#"{ "sdk": { "version": "1.0.0", "rollForward": "disable" } }"#,
    );
    write(&pinned.join("A.fs"), "module A\nlet a = 1\n");
    let plain = root.join("plain/A.fs");
    write(&plain, "module A\nlet a = 1\n");

    let probe = root.join("probe/B.fs");
    write(
        &probe,
        "module B\n/// Doc.\nlet z = FSharp.Compiler.Text.Range.Zero\n",
    );
    let probe_request = request(&[&probe], &[]);

    let fresh = fcs_dump_batch_child("xmldoc-batch").request(&probe_request);
    assert!(
        fresh.contains("\"ErrorNumber\":39"),
        "a fresh child must report the probe's type unbound, or the leak is unobservable: {fresh}"
    );

    let earlier: [(&str, PathBuf, Vec<&Path>); 3] = [
        (
            "a project referencing the DLL",
            referencing,
            vec![dll.as_path()],
        ),
        ("a project under a global.json", pinned.join("A.fs"), vec![]),
        ("a plain project", plain, vec![]),
    ];
    let mut child = fcs_dump_batch_child("xmldoc-batch");
    let mut failures = Vec::new();
    for (label, path, refs) in &earlier {
        let answer = child.request(&request(&[path], refs));
        assert!(
            !answer.contains("\"BatchError\"") && !answer.contains("\"ErrorNumber\":39"),
            "{label} must check, its references resolving: {answer}"
        );
        let after = child.request(&probe_request);
        if after != fresh {
            failures.push(format!("after {label}:\n  got   {after}\n  fresh {fresh}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// A real project's reference rewritten in place, its modification time put
/// back, between two of the harness's requests whose inputs may change is
/// read as it is now: the harness puts each such request to a fresh child,
/// which reads the reference as a fresh process would, however the request
/// spells its path. Run in an ordinary directory, and in one shaped like a
/// framework reference pack, whose assemblies FCS keeps by path alone.
#[test]
fn a_real_projects_reference_rewritten_in_place_is_read() {
    let root = tempfile::TempDir::new().expect("temp dir");
    let a = root.path().join("A.fs");
    write(&a, "module A\nlet z = FSharp.Compiler.Text.Range.Zero\n");
    let fcs = ensure_fsharp_compiler_service_dll();
    let other = fcs
        .parent()
        .expect("the oracle's directory")
        .join("FSharp.Core.dll");
    let check = |lib: &Path| -> Vec<i32> {
        fcs_check_or_refusal(std::slice::from_ref(&a), &[], &[lib], false, None, true)
            .unwrap_or_else(|err| panic!("refused: {err}"))
            .iter()
            .flat_map(OracleFile::errors)
            .map(|d| d.error_number)
            .collect()
    };
    for home in [
        root.path().join("lib"),
        root.path()
            .join("packs/Microsoft.NETCore.App.Ref/10.0.0/ref/net10.0"),
    ] {
        std::fs::create_dir_all(&home).expect("create the reference's directory");
        let lib = home.join("Lib.dll");
        std::fs::copy(&fcs, &lib).expect("copy the referenced assembly");
        let stamp = host_fs::metadata(&lib)
            .and_then(|m| m.modified())
            .expect("modification time");
        assert_eq!(
            check(&lib),
            Vec::<i32>::new(),
            "{home:?}: the type resolves in the reference"
        );
        std::fs::copy(&other, &lib).expect("rewrite the referenced assembly");
        host_fs::set_modified(&lib, stamp).expect("restore the modification time");
        let second = check(&home.join(".").join("Lib.dll"));
        assert!(
            second.contains(&39),
            "{home:?}: the rewritten reference does not hold the type: {second:?}"
        );
    }
}
