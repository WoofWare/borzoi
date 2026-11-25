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
//! The bytes hashed are the ones rustc compiles: it reads a CRLF line end as
//! LF, so a checkout under `core.autocrlf` compiles the same crate, and pins
//! the same. A lone CR is kept.
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
        pin.push_str(&pin_line(&relative, &bytes));
    }
    pin
}

/// The bytes as rustc reads them: each CRLF as LF, a lone CR kept.
fn as_compiled(bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\r' && bytes.get(i + 1) == Some(&b'\n') {
            i += 1;
            continue;
        }
        out.push(bytes[i]);
        i += 1;
    }
    out
}

/// One file's line of the pin: its path, and the SHA-1 and length of its
/// bytes as compiled.
fn pin_line(relative: &str, bytes: &[u8]) -> String {
    let compiled = as_compiled(bytes);
    let mut hex = String::new();
    for byte in Sha1::digest(&compiled) {
        write!(hex, "{byte:02x}").expect("writing to a String");
    }
    format!("{relative}\t{hex}\t{}\n", compiled.len())
}

#[test]
fn every_source_file_is_exactly_as_pinned() {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let current = current_pin(crate_dir);
    if std::env::var_os("BORZOI_UPDATE_MANIFESTS").is_some_and(|v| v == "1") {
        std::fs::write(crate_dir.join("tests/src.pin"), &current).expect("writing the pin");
        return;
    }
    // By line, so a pin checked out with CRLF line ends reads the same.
    let pinned: Vec<&str> = PIN.lines().collect();
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
        current.lines().collect::<Vec<_>>() == pinned,
        "crates/verdict/src no longer matches tests/src.pin:\n{}\n\
         Every change to this primitive is reviewed: check that it adds no reading of an \
         incomplete answer as a complete one (crate docs), give any new operation its laws \
         in tests/laws.rs, then regenerate with\n  \
         BORZOI_UPDATE_MANIFESTS=1 nix develop -c cargo test -p borzoi-verdict --test pin",
        moved.join("\n")
    );
}

#[test]
fn line_ends_pin_as_rustc_compiles_them() {
    let lf = b"//! a\nfn f() {}\n";
    let crlf = b"//! a\r\nfn f() {}\r\n";
    assert_eq!(pin_line("src/x.rs", lf), pin_line("src/x.rs", crlf));
    // A lone CR is part of what rustc reads, and so is pinned.
    let lone = b"//! a\rfn f() {}\n";
    assert_ne!(pin_line("src/x.rs", lf), pin_line("src/x.rs", lone));
    assert_eq!(as_compiled(b"\r\r\n\n\r"), b"\r\n\n\r");
    // Any other edit moves the pin.
    assert_ne!(
        pin_line("src/x.rs", lf),
        pin_line("src/x.rs", b"//! b\nfn f() {}\n")
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
