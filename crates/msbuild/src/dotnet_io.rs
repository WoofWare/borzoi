//! The existence predicates of .NET's `System.IO` that MSBuild's evaluation
//! asks, answered as .NET answers them on Unix and queried through
//! [`observed`] so the evaluation's read set records them.
//!
//! Two rules part them from the operating system's own answer, which is what
//! [`observed::exists`] and [`observed::is_file`] give:
//!
//! - **`..` is lexical.** `File.Exists` and `Directory.Exists` take
//!   `Path.GetFullPath` of their argument first, which collapses `.`, `..` and
//!   repeated separators as text. The OS resolves `..` physically, so the two
//!   part when a `..` follows a symlinked directory: `link/..` is the
//!   directory holding `link` to .NET, and the link target's parent to the OS.
//! - **A dangling symlink exists.** `File.Exists` asks `stat` and, when that
//!   fails, `lstat`: a link whose target is missing is a file that exists.
//!   `Directory.Exists` asks the same pair, and a link is no directory, so it
//!   follows the link in effect.
//!
//! A path whose full form ends in a separator is no file to `File.Exists`,
//! and `Directory.Exists` asks `stat`, which follows a final link before
//! looking for a directory. All of this is oracle-pinned through `Exists()`
//! (`tests/condition_diff.rs`, `exists_matches_msbuild_over_a_generated_tree`).

use std::path::{Path, PathBuf};

use crate::imports::normalise;
use crate::observed::{self, EntryKind, Observer};

/// `File.Exists(path) || Directory.Exists(path)`, the question MSBuild's
/// `Exists()` condition function asks (`FileOrDirectoryExistsNoThrow`), for a
/// rooted `path`.
pub(crate) fn file_or_directory_exists(observer: &Observer, path: &Path) -> bool {
    let Some((full, trailing)) = full_path(path) else {
        return false;
    };
    if trailing {
        observed::kind(observer, &full) == Ok(EntryKind::Dir)
    } else {
        // `stat` succeeds only where `lstat` does, and `lstat` succeeding on
        // anything but a dangling link means `stat` does too.
        observed::link_kind(observer, &full).is_ok()
    }
}

/// Whether the full form of `path` is the root, a directory on every Unix
/// host, so that both predicates hold for it without asking the file system.
pub(crate) fn names_the_root(path: &Path) -> bool {
    full_path(path).is_some_and(|(full, _)| full.parent().is_none())
}

/// `File.Exists(path)` for a rooted `path`: something is there that is no
/// directory, a dangling symlink included.
pub(crate) fn file_exists(observer: &Observer, path: &Path) -> bool {
    let Some((full, trailing)) = full_path(path) else {
        return false;
    };
    if trailing {
        return false;
    }
    match observed::kind(observer, &full) {
        Ok(kind) => kind != EntryKind::Dir,
        // `stat` failed: only a symlink (whose target is missing, loops, or
        // cannot be reached) lets `lstat` succeed.
        Err(_) => observed::link_kind(observer, &full).is_ok(),
    }
}

/// `Directory.Exists(path)` for a rooted `path`: `stat`, which follows a
/// link, finds a directory there.
pub(crate) fn directory_exists(observer: &Observer, path: &Path) -> bool {
    let Some((full, _)) = full_path(path) else {
        return false;
    };
    observed::kind(observer, &full) == Ok(EntryKind::Dir)
}

/// `Path.GetFullPath(path)` for a rooted `path`, as the path to ask the file
/// system about, and whether the full form ends in a separator. `None` for an
/// unrooted `path` (it would resolve against the process's working directory)
/// or an empty one, and for one holding a NUL, which `Path.GetFullPath` rejects
/// before it collapses anything: both predicates are false for it, even where a
/// `..` would erase the segment that holds the NUL.
fn full_path(path: &Path) -> Option<(PathBuf, bool)> {
    if !path.has_root() || path.as_os_str().as_encoded_bytes().contains(&0) {
        return None;
    }
    let trailing = path.as_os_str().as_encoded_bytes().ends_with(b"/");
    let full = normalise(path);
    // The root itself names a directory with or without its separator.
    let trailing = trailing || full.parent().is_none();
    Some((full, trailing))
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;

    fn ask(f: fn(&Observer, &Path) -> bool, path: &Path) -> bool {
        f(&Observer::new(), path)
    }

    #[test]
    fn a_dangling_link_is_a_file_that_exists() {
        let dir = tempfile::tempdir().unwrap();
        let link = dir.path().join("link");
        symlink("missing", &link).unwrap();
        assert!(ask(file_or_directory_exists, &link));
        assert!(ask(file_exists, &link));
        let mut slashed = link.into_os_string();
        slashed.push("/");
        assert!(!ask(file_or_directory_exists, Path::new(&slashed)));
    }

    #[test]
    fn dot_dot_collapses_before_the_file_system_sees_it() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir_all(dir.path().join("a/b")).unwrap();
        std::fs::create_dir_all(dir.path().join("elsewhere")).unwrap();
        std::fs::write(dir.path().join("a/f"), "").unwrap();
        symlink(dir.path().join("elsewhere"), dir.path().join("a/link")).unwrap();
        // Physically `a/link/..` is `dir`, which holds no `f`.
        assert!(ask(
            file_or_directory_exists,
            &dir.path().join("a/link/../f")
        ));
        assert!(ask(file_exists, &dir.path().join("a/link/../f")));
        assert!(!ask(file_exists, &dir.path().join("a/b/../../f")));
    }

    #[test]
    fn a_trailing_separator_asks_for_a_directory() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::create_dir(dir.path().join("d")).unwrap();
        std::fs::write(dir.path().join("f"), "").unwrap();
        symlink("d", dir.path().join("dlink")).unwrap();
        for (name, exists) in [
            ("d/", true),
            ("dlink/", true),
            ("f/", false),
            ("d/./", true),
        ] {
            assert_eq!(
                ask(file_or_directory_exists, &dir.path().join(name)),
                exists,
                "{name}"
            );
            assert!(!ask(file_exists, &dir.path().join(name)), "{name}");
        }
        assert!(ask(file_or_directory_exists, Path::new("/")));
        assert!(!ask(file_exists, Path::new("/")));
    }

    #[test]
    fn a_relative_path_names_nothing() {
        assert!(!ask(file_or_directory_exists, Path::new("Cargo.toml")));
        assert!(!ask(file_exists, Path::new("")));
    }
}
