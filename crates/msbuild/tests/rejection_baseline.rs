//! A revision's walk over the projects `rejection_generative_diff`'s fixed
//! seed generates, recorded so that the sweep can hold the walk under test to
//! it: a project the baseline answered rightly, or withdrew, must not be one
//! the walk under test answers wrongly.
//!
//! `tools/rejection-baseline.sh <revision>` runs this file in a checkout of
//! the baseline revision, over the projects the sweep dumped
//! (`BORZOI_REJECTION_DUMP`), and writes
//! `tests/manifests/rejection_projects_baseline.txt`. It reads the walk only
//! through the crate's public surface, so that it builds at a revision older
//! than the sweep.

mod common;

use std::collections::HashMap;

use borzoi_msbuild::PropertyRead;

/// The names the sweep grades, as it reads them.
const NAMES: &[&str] = &["A", "B", "U", "X", "R", "After", "Delta"];

#[test]
#[ignore = "run by tools/rejection-baseline.sh in a checkout of the baseline revision"]
fn record_baseline() {
    let dump = std::path::PathBuf::from(
        std::env::var("BORZOI_REJECTION_DUMP").expect("BORZOI_REJECTION_DUMP names the dump"),
    );
    let tmp = tempfile::TempDir::new().unwrap();
    let dir = borzoi_msbuild::observed::host_fs::canonicalize(tmp.path()).unwrap();
    std::fs::write(
        dir.join("there.props"),
        "<Project><PropertyGroup><Delta>d</Delta></PropertyGroup></Project>",
    )
    .unwrap();
    let project_path = dir.join("Demo.fsproj");
    let mut cases: Vec<(String, std::path::PathBuf)> =
        borzoi_msbuild::observed::host_fs::read_dir(&dump)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|e| e == "xml"))
            .map(|path| {
                let key = path.file_stem().unwrap().to_string_lossy().into_owned();
                (key, path)
            })
            .collect();
    cases.sort();
    assert!(!cases.is_empty(), "no project dumped in {}", dump.display());
    let mut out = String::new();
    for (key, path) in cases {
        let xml = borzoi_msbuild::observed::host_fs::read_to_string(&path).unwrap();
        std::fs::write(&project_path, &xml).unwrap();
        let parsed = common::parse_fsproj_with_imports(
            &borzoi_msbuild::ProjectFile::buffer(&project_path, &xml)
                .expect("a project path spelt as its full path"),
            &HashMap::new(),
            &common::oracle_environment(),
            None,
            None,
        )
        .expect("well-formed");
        let rejection = match parsed.rejection.as_ref().map(|r| r.certainty) {
            None => "none",
            Some(borzoi_msbuild::RejectionCertainty::Possible) => "possible",
            Some(borzoi_msbuild::RejectionCertainty::Certain) => "certain",
        };
        let committed: Vec<String> = NAMES
            .iter()
            .filter_map(|name| match parsed.property(name) {
                PropertyRead::Unset => Some(format!("{name}=")),
                read => read.value().map(|v| format!("{name}={}", encode(v))),
            })
            .collect();
        // A row that commits nothing ends at its rejection: a manifest line
        // holds no trailing tab.
        out.push_str(&format!("{key}\t{}\t{rejection}", fnv1a(&xml)));
        if !committed.is_empty() {
            out.push_str(&format!("\t{}", committed.join(" ")));
        }
        out.push('\n');
    }
    std::fs::write(dump.join("baseline.txt"), out).unwrap();
}

/// `value` as one space-free field: Rust's default escape, a space as `\x20`.
/// `rejection_generative_diff` encodes MSBuild's values alike to compare.
fn encode(value: &str) -> String {
    value.escape_default().to_string().replace(' ', "\\x20")
}

/// FNV-1a over `text`'s bytes, as hex: the sweep's key for a project's text.
fn fnv1a(text: &str) -> String {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in text.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x0100_0000_01b3);
    }
    format!("{hash:016x}")
}
