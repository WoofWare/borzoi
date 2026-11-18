//! The project an evaluation evaluates: its path, as MSBuild takes it, paired
//! with the text the evaluation reads as its body.
//!
//! MSBuild loads a project from the full path of the path it is handed
//! (`Path.GetFullPath`: `.` segments dropped, runs of separators collapsed,
//! each `..` taking the segment before it, lexically, whatever that segment
//! links to). Every value the walk derives from the project's path starts from
//! that full path, so the text must be the text *at* that full path. A caller
//! that read the text through some other spelling (`dir/link/../p.fsproj`,
//! which the file system resolves through the link) would pair one file's
//! body with another file's directory.
//!
//! [`ProjectFile`] makes that pairing unrepresentable. Its only constructors
//! are [`ProjectFile::read`], which normalises the path and reads the text at
//! the full path, and [`ProjectFile::buffer`], which takes a caller's text (an
//! editor's buffer, a test's document) only for a path already spelt as its
//! own full path, so there is no other spelling it can have been read
//! through.
//!
//! The lexical rule is `GetFullPath`'s on a Unix host. Windows' (drive-relative
//! paths, verbatim `\\?\` prefixes, a `:` inside a segment) is not modelled,
//! so there a path is taken as spelt.

use std::fmt;
use std::path::{Path, PathBuf};

use crate::observed;

/// A project file's full path and its text, paired so that the text is the
/// file's at that path: [`ProjectFile::read`] reads it there, and
/// [`ProjectFile::buffer`] takes a caller's text only for a path spelt as its
/// own full path.
#[derive(Debug, Clone)]
pub struct ProjectFile {
    path: PathBuf,
    text: String,
}

/// Why a [`ProjectFile`] could not be made.
#[derive(Debug, Clone)]
pub enum ProjectFileError {
    /// The path has no filesystem root (`/foo` on Unix, `C:\foo` or
    /// `\\server\share\foo` on Windows). Every relative Include and import
    /// is resolved against the project's directory, which a relative path
    /// does not name. [`Path::has_root`] rather than [`Path::is_absolute`],
    /// so that rooted-but-not-drive-qualified paths (`/foo` on Windows) are
    /// accepted.
    Relative(PathBuf),
    /// On a Unix host, the path holds a `\`. MSBuild loads a project from
    /// its path with every backslash read as a separator, so it evaluates the
    /// file the rewritten path names, or refuses the project (MSB4025) where
    /// that path names no file. Where a `..` follows the backslash, which file
    /// even depends on the host: `dotnet msbuild` rewrites the backslash
    /// before it resolves the `..` (`a\b/../p.proj` is `a/p.proj`), the
    /// in-process API after (`p.proj`).
    Backslash(PathBuf),
    /// The path names no file: it holds a NUL, which .NET refuses before it
    /// resolves any `..`, or (on a Unix host) its full path is the
    /// file-system root (`/work/..`) or it ends in a separator. MSBuild loads
    /// no project from any of them.
    NamesNoFile(PathBuf),
    /// [`ProjectFile::buffer`] was handed a path not spelt as its own full
    /// path, which text may have been read through to name another file.
    NotFullPath { spelt: PathBuf, full: PathBuf },
    /// [`ProjectFile::read`] could not read the file at the full path.
    Unreadable {
        path: PathBuf,
        failure: observed::Failure,
    },
}

impl fmt::Display for ProjectFileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProjectFileError::Relative(p) => write!(
                f,
                "project path must be rooted (have a filesystem root), got {}",
                p.display()
            ),
            ProjectFileError::Backslash(p) => write!(
                f,
                "project path {} holds a backslash, which MSBuild reads as a separator on \
                 this host, so it would load another file, or none (MSB4025)",
                p.display()
            ),
            ProjectFileError::NamesNoFile(p) => write!(
                f,
                "project path {} names no file: its full path is the root, it ends in a \
                 separator, or it holds a NUL",
                p.display()
            ),
            ProjectFileError::NotFullPath { spelt, full } => write!(
                f,
                "project path {} is not spelt as its full path {}, so text read through it \
                 may be another file's",
                spelt.display(),
                full.display()
            ),
            ProjectFileError::Unreadable { path, failure } => {
                write!(f, "cannot read project {}: {failure}", path.display())
            }
        }
    }
}

impl std::error::Error for ProjectFileError {}

impl ProjectFile {
    /// The project file at `path`: its full path, and the text read there
    /// through `observer` (so a caller whose read set includes `observer`'s
    /// holds the read), a leading byte-order mark dropped.
    pub fn read(path: &Path, observer: &observed::Observer) -> Result<Self, ProjectFileError> {
        let full = full_path(path)?;
        let text = observed::read_to_string(observer, &full).map_err(|failure| {
            ProjectFileError::Unreadable {
                path: full.clone(),
                failure,
            }
        })?;
        let text = match text.strip_prefix('\u{feff}') {
            Some(rest) => rest.to_string(),
            None => text,
        };
        Ok(Self { path: full, text })
    }

    /// The project file at `path` with the caller's `text` as its body: an
    /// editor's buffer, or a document a test wrote. `path` must be spelt as
    /// its own full path ([`ProjectFileError::NotFullPath`]).
    pub fn buffer(path: &Path, text: impl Into<String>) -> Result<Self, ProjectFileError> {
        let full = full_path(path)?;
        if full.as_os_str() != path.as_os_str() {
            return Err(ProjectFileError::NotFullPath {
                spelt: path.to_path_buf(),
                full,
            });
        }
        Ok(Self {
            path: full,
            text: text.into(),
        })
    }

    /// The project's full path.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// The project's text.
    pub fn text(&self) -> &str {
        &self.text
    }
}

/// `path` as MSBuild takes it, or why MSBuild would load no project, or one
/// whose file the walk cannot name, from it.
pub fn full_path(path: &Path) -> Result<PathBuf, ProjectFileError> {
    if !path.has_root() {
        return Err(ProjectFileError::Relative(path.to_path_buf()));
    }
    let spelt = path.as_os_str().as_encoded_bytes();
    if spelt.contains(&0) {
        return Err(ProjectFileError::NamesNoFile(path.to_path_buf()));
    }
    // Checked on the path as spelt: `dotnet msbuild` rewrites each `\` before
    // it resolves a `..`, the in-process API after, so a `..` that takes a
    // backslash-bearing segment away still leaves the file host-dependent.
    if cfg!(unix) && spelt.contains(&b'\\') {
        return Err(ProjectFileError::Backslash(path.to_path_buf()));
    }
    if !cfg!(unix) {
        return Ok(path.to_path_buf());
    }
    // After the backslash, which may make a spelling that collapses to the
    // root name a file to `dotnet msbuild`.
    let full = crate::imports::normalise(path);
    if full.file_name().is_none() || spelt.last() == Some(&b'/') {
        return Err(ProjectFileError::NamesNoFile(path.to_path_buf()));
    }
    Ok(full)
}
