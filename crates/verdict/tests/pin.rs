//! The exact text of every file under `src`, pinned.
//!
//! The crate exists to have no reading of an incomplete answer as a complete
//! one, and such a reading can be added under any name, on any platform, in a
//! signature, a nested item or a macro's arguments. No listing of the surface
//! read off the source can be shown to see every one of those. So nothing is
//! read off it: each file under `src` is pinned whole, by its SHA-1 and length,
//! in `tests/src.pin`, together with the set of file names. Any edit, and any
//! new or removed file, fails here until the pin is regenerated, and the
//! regenerated pin is in the diff the reviewer reads.
//!
//! Regenerate with
//! `BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-verdict --test pin`.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use sha1::{Digest, Sha1};

const PIN: &str = include_str!("src.pin");

/// Every file under `dir`, recursively, by its path relative to `root`,
/// `/`-separated and sorted.
fn files(root: &Path, dir: &Path, out: &mut Vec<(String, PathBuf)>) {
    for entry in std::fs::read_dir(dir).expect("a readable source directory") {
        let path = entry.expect("a readable directory entry").path();
        if path.is_dir() {
            files(root, &path, out);
        } else {
            let relative = path
                .strip_prefix(root)
                .expect("under the crate")
                .components()
                .map(|c| c.as_os_str().to_str().expect("a UTF-8 file name"))
                .collect::<Vec<_>>()
                .join("/");
            out.push((relative, path));
        }
    }
}

/// The pin of the crate's sources as they are on disk.
fn current_pin(crate_dir: &Path) -> String {
    let mut found = Vec::new();
    files(crate_dir, &crate_dir.join("src"), &mut found);
    found.sort();
    let mut pin = String::from(
        "# Every file under crates/verdict/src: path, SHA-1 of its bytes, length.\n\
         # Regenerate with BORZOI_UPDATE_MANIFESTS=1 (see tests/pin.rs).\n",
    );
    for (relative, path) in found {
        let bytes = std::fs::read(&path).expect("a readable source file");
        let digest = Sha1::digest(&bytes);
        let mut hex = String::new();
        for byte in digest {
            write!(hex, "{byte:02x}").expect("writing to a String");
        }
        writeln!(pin, "{relative}\t{hex}\t{}", bytes.len()).expect("writing to a String");
    }
    pin
}

#[test]
fn every_source_file_is_exactly_as_pinned() {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let current = current_pin(crate_dir);
    if std::env::var_os("BORZOI_UPDATE_MANIFESTS").is_some_and(|v| v == "1") {
        std::fs::write(crate_dir.join("tests/src.pin"), &current).expect("writing the pin");
        return;
    }
    let moved: Vec<String> = current
        .lines()
        .filter(|line| !PIN.lines().any(|pinned| pinned == *line))
        .map(|line| format!("+ {line}"))
        .chain(
            PIN.lines()
                .filter(|pinned| !current.lines().any(|line| line == *pinned))
                .map(|line| format!("- {line}")),
        )
        .collect();
    assert!(
        current == PIN,
        "crates/verdict/src no longer matches tests/src.pin:\n{}\n\
         Every change to this primitive is reviewed: check that it adds no reading of an \
         incomplete answer as a complete one (crate docs), give any new operation its laws \
         in tests/laws.rs, then regenerate with\n  \
         BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-verdict --test pin",
        moved.join("\n")
    );
}

#[test]
fn the_pin_covers_at_least_the_crate_root() {
    // Anti-vacuity: the pin names the file that holds the crate, so an empty
    // or misdirected walk cannot agree with it.
    assert!(
        PIN.lines().any(|line| line.starts_with("src/lib.rs\t")),
        "{PIN}"
    );
}
