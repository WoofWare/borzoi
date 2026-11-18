//! The project-path spelling axis shared by the differentials that evaluate a
//! project at a real path.
//!
//! MSBuild takes the project's path as `Path.GetFullPath` gives it: `.`
//! segments dropped, runs of `/` collapsed, and each `..` taking the segment
//! before it, lexically (no symlink is resolved). Every `MSBuildProject*` and
//! `MSBuildThisFile*` value, every item's `FullPath`, `Directory` and
//! `DefiningProject*`, every relative import and the duplicate-import key
//! derive from that full path. A differential that only ever hands both
//! sides a canonical path cannot tell an evaluator that normalises from one
//! that carries the caller's spelling through: both agree with MSBuild on
//! every input it builds.
//!
//! [`respell`] spells the same project file another way. A sweep evaluates
//! both sides at the respelt path, so MSBuild's answer is the oracle for that
//! spelling, and nothing about what normalisation does is assumed here.

use std::path::{Path, PathBuf};

/// How [`respell`] spells a project path.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjectSpelling {
    /// The path as given.
    AsIs,
    /// A doubled separator before the file name: `dir//p.proj`.
    DoubledSeparator,
    /// A `.` segment before the file name: `dir/./p.proj`.
    CurDir,
    /// The directory left and entered again: `dir/../<dir's name>/p.proj`,
    /// which needs no directory beyond the ones the path already names.
    ParentDir,
    /// All three at once, the `..` first: `parent//<name>/../<name>/./p.proj`.
    Mixed,
}

/// Every spelling, [`ProjectSpelling::AsIs`] first.
///
/// Only [`ProjectSpelling::AsIs`] off Unix: the harnesses hand over
/// canonicalised fixture paths, which Windows spells verbatim (`\\?\`), and a
/// verbatim path takes `//`, `.` and `..` as written rather than normalising
/// them.
#[cfg(unix)]
pub const SPELLINGS: &[ProjectSpelling] = &[
    ProjectSpelling::AsIs,
    ProjectSpelling::DoubledSeparator,
    ProjectSpelling::CurDir,
    ProjectSpelling::ParentDir,
    ProjectSpelling::Mixed,
];
#[cfg(not(unix))]
pub const SPELLINGS: &[ProjectSpelling] = &[ProjectSpelling::AsIs];

/// `path` (an absolute path to a file whose directory has a parent) spelt as
/// `spelling` says. Every spelling names the same file as `path` through the
/// file system as well as lexically, so a harness can write a project at
/// `path` and hand either side the respelling.
pub fn respell(path: &Path, spelling: ProjectSpelling) -> PathBuf {
    let dir = path.parent().expect("a project file has a directory");
    let file = path
        .file_name()
        .expect("a project path names a file")
        .to_string_lossy();
    let dir_text = dir.to_string_lossy();
    let name = dir
        .file_name()
        .expect("the project's directory has a name")
        .to_string_lossy();
    let parent = dir
        .parent()
        .expect("the project's directory has a parent")
        .to_string_lossy();
    let parent = parent.trim_end_matches('/');
    PathBuf::from(match spelling {
        ProjectSpelling::AsIs => return path.to_path_buf(),
        ProjectSpelling::DoubledSeparator => format!("{dir_text}//{file}"),
        ProjectSpelling::CurDir => format!("{dir_text}/./{file}"),
        ProjectSpelling::ParentDir => format!("{dir_text}/../{name}/{file}"),
        ProjectSpelling::Mixed => format!("{parent}//{name}/../{name}/./{file}"),
    })
}
