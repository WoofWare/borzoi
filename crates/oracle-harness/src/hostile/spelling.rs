//! Hostile spellings of a path ([`Kind::PathSpelling`]).
//!
//! The scenario is one file, `<base>/<dir>/<name>`, and the ways to write a
//! path that some reader takes for it. A spelling is a template over the
//! base, the directory and the name; [`Means`] says what the file system
//! makes of it, which this module's tests check against a real tree, so a
//! harness can state what its subject owes each spelling.
//!
//! Some spellings go through fixtures beside the file: [`prepare`] makes
//! them.

use std::ffi::OsString;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::symlink;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use super::fs::HostileFs;
use super::{Alphabet, Dimension, Entry, Kind};

/// One part of a spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Part {
    /// The directory the file is in, relative to the base.
    Dir,
    /// The directory, in ASCII upper case.
    DirUpper,
    /// The file's name.
    Name,
    /// The name, in ASCII upper case.
    NameUpper,
    /// These bytes.
    Lit(&'static [u8]),
    /// These bytes, this many times.
    Repeat(&'static [u8], usize),
}

/// What the file system makes of a spelling, read against the base.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Means {
    /// The file.
    TheFile,
    /// The file on a file system that ignores case, and nothing on one that
    /// does not.
    TheFileIfCaseIsIgnored,
    /// Nothing the file system can open: no such file, or a path it refuses.
    /// A reader that normalises the text first may still take it for the
    /// file.
    Nothing,
    /// Something that exists and is not the file: a directory, or the root.
    SomethingElse,
}

/// A hostile spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Spelling {
    /// The spelling.
    pub parts: &'static [Part],
    /// Whether the spelling is rooted as written. One that is not is read
    /// against the base: [`Self::relative`] leaves that to the reader, and
    /// [`Self::absolute`] writes the base in front.
    pub rooted: bool,
    /// What the file system makes of it.
    pub means: Means,
}

/// A real directory inside the file's directory, for `<dir>/x/../<name>`.
pub const INNER_DIR: &str = "x";
/// A link beside the file's directory, to it.
pub const LINK: &str = "ln";
/// A link inside the file's directory to a directory two levels down a tree
/// outside the base, so that `far/..` is one thing lexically and another
/// physically.
pub const FAR_LINK: &str = "far";

/// Make the fixtures the spellings go through, for a file in `dir` under
/// `fs`'s tree: [`INNER_DIR`], [`LINK`] and [`FAR_LINK`]. `dir` is one path
/// component.
pub fn prepare(fs: &HostileFs, dir: &str) {
    let base = fs.tree();
    let inner = base.join(dir).join(INNER_DIR);
    std::fs::create_dir_all(&inner).unwrap_or_else(|e| panic!("create {}: {e}", inner.display()));
    symlink(dir, base.join(LINK)).expect("link to the file's directory");
    let far = fs.aside().join("far-target").join("a").join("b");
    std::fs::create_dir_all(&far).unwrap_or_else(|e| panic!("create {}: {e}", far.display()));
    symlink(&far, base.join(dir).join(FAR_LINK)).expect("link out of the tree");
}

impl Spelling {
    fn tail(&self, dir: &str, name: &str) -> Vec<u8> {
        let mut out = Vec::new();
        for part in self.parts {
            match part {
                Part::Dir => out.extend(dir.as_bytes()),
                Part::DirUpper => out.extend(dir.to_ascii_uppercase().as_bytes()),
                Part::Name => out.extend(name.as_bytes()),
                Part::NameUpper => out.extend(name.to_ascii_uppercase().as_bytes()),
                Part::Lit(bytes) => out.extend(*bytes),
                Part::Repeat(bytes, n) => {
                    for _ in 0..*n {
                        out.extend(*bytes);
                    }
                }
            }
        }
        out
    }

    /// The spelling as written, for a reader that resolves it against the
    /// base itself (as its working directory, or its project directory).
    pub fn relative(&self, dir: &str, name: &str) -> OsString {
        OsString::from_vec(self.tail(dir, name))
    }

    /// The spelling with `base` written in front, unless it is rooted
    /// already.
    pub fn absolute(&self, base: &Path, dir: &str, name: &str) -> OsString {
        let tail = self.tail(dir, name);
        if self.rooted {
            return OsString::from_vec(tail);
        }
        let mut out = base.as_os_str().to_owned().into_encoded_bytes();
        out.push(b'/');
        out.extend(tail);
        OsString::from_vec(out)
    }
}

use Part::{Dir, DirUpper, Lit, Name, NameUpper, Repeat};

const fn relative(parts: &'static [Part], means: Means) -> Spelling {
    Spelling {
        parts,
        rooted: false,
        means,
    }
}

const fn rooted(parts: &'static [Part], means: Means) -> Spelling {
    Spelling {
        parts,
        rooted: true,
        means,
    }
}

/// The plain spelling: the directory, a separator, the name.
pub const PLAIN: Spelling = relative(&[Dir, Lit(b"/"), Name], Means::TheFile);

const TABLE: &[(Dimension, Spelling, &str)] = &[
    (
        Dimension::Relative,
        PLAIN,
        "the plain relative spelling, where a reader expects an absolute path: it means the file only from one working directory",
    ),
    (
        Dimension::CurDir,
        relative(&[Lit(b"./"), Dir, Lit(b"/"), Name], Means::TheFile),
        "a leading `./`",
    ),
    (
        Dimension::CurDir,
        relative(&[Dir, Lit(b"/./"), Name], Means::TheFile),
        "a `.` segment inside the path: one file under two spellings to a cache keyed by text",
    ),
    (
        Dimension::DotDot,
        relative(&[Dir, Lit(b"/x/../"), Name], Means::TheFile),
        "a `..` through a real directory",
    ),
    (
        Dimension::DotDot,
        relative(&[Dir, Lit(b"/../"), Dir, Lit(b"/"), Name], Means::TheFile),
        "out of the directory and back in",
    ),
    (
        Dimension::DotDotThroughLink,
        relative(&[Dir, Lit(b"/far/../"), Name], Means::Nothing),
        "a `..` through a link: the file lexically, the link target's parent physically",
    ),
    (
        Dimension::DotDotThroughMissing,
        relative(&[Dir, Lit(b"/missing/../"), Name], Means::Nothing),
        "a `..` through a directory that does not exist",
    ),
    (
        Dimension::Doubled,
        relative(&[Dir, Lit(b"//"), Name], Means::TheFile),
        "a doubled separator",
    ),
    (
        Dimension::Doubled,
        relative(&[Lit(b".//"), Dir, Lit(b"/"), Name], Means::TheFile),
        "a doubled separator after a `.`",
    ),
    (
        Dimension::TrailingSeparator,
        relative(&[Dir, Lit(b"/"), Name, Lit(b"/")], Means::Nothing),
        "a trailing separator on a file: not a directory",
    ),
    (
        Dimension::TrailingSeparator,
        relative(&[Dir, Lit(b"/"), Name, Lit(b"/.")], Means::Nothing),
        "a trailing `/.` on a file",
    ),
    (
        Dimension::BackslashSeparator,
        relative(&[Dir, Lit(b"\\"), Name], Means::Nothing),
        "a backslash for the separator: one odd name on Unix, the file to MSBuild where it rewrites",
    ),
    (
        Dimension::BackslashSeparator,
        relative(&[Lit(b".\\"), Dir, Lit(b"\\"), Name], Means::Nothing),
        "backslashes throughout",
    ),
    (
        Dimension::BackslashSeparator,
        relative(&[Dir, Lit(b"/x\\..\\"), Name], Means::Nothing),
        "a `..` between backslashes, which a rewrite must collapse after it rewrites",
    ),
    (
        Dimension::EscapedSeparator,
        relative(&[Dir, Lit(b"%2F"), Name], Means::Nothing),
        "an escaped slash",
    ),
    (
        Dimension::EscapedSeparator,
        relative(&[Dir, Lit(b"%5C"), Name], Means::Nothing),
        "an escaped backslash, which MSBuild rewrites only if it decodes first",
    ),
    (
        Dimension::ParentEscape,
        relative(&[Lit(b"../"), Name], Means::Nothing),
        "a file of the same name beside the base: a write there leaves the directory the caller owns",
    ),
    (
        Dimension::ParentEscape,
        relative(&[Dir, Lit(b"/../../"), Name], Means::Nothing),
        "an escape from inside the directory",
    ),
    (
        Dimension::Rooted,
        rooted(&[Lit(b"/"), Name], Means::Nothing),
        "the name with a leading slash: a file in the root directory",
    ),
    (
        Dimension::Rooted,
        rooted(&[Lit(b"/"), Dir, Lit(b"/"), Name], Means::Nothing),
        "the relative path with a leading slash",
    ),
    (
        Dimension::Root,
        rooted(&[Lit(b"/")], Means::SomethingElse),
        "the root: no parent, no file name",
    ),
    (
        Dimension::WindowsRoot,
        rooted(&[Lit(b"C:\\"), Dir, Lit(b"\\"), Name], Means::Nothing),
        "a drive-rooted Windows path: a relative name on Unix",
    ),
    (
        Dimension::WindowsRoot,
        rooted(&[Lit(b"C:/"), Dir, Lit(b"/"), Name], Means::Nothing),
        "a drive letter before forward slashes: a directory named `C:` on Unix",
    ),
    (
        Dimension::WindowsRoot,
        rooted(&[Lit(b"\\\\server\\share\\"), Name], Means::Nothing),
        "a UNC path",
    ),
    (
        Dimension::WindowsRoot,
        rooted(&[Lit(b"\\\\?\\C:\\"), Name], Means::Nothing),
        "a verbatim path, which Windows does not normalise",
    ),
    (
        Dimension::CaseVariant,
        relative(&[DirUpper, Lit(b"/"), Name], Means::TheFileIfCaseIsIgnored),
        "the directory in another case",
    ),
    (
        Dimension::CaseVariant,
        relative(&[Dir, Lit(b"/"), NameUpper], Means::TheFileIfCaseIsIgnored),
        "the name in another case",
    ),
    (
        Dimension::ThroughLink,
        relative(&[Lit(b"ln/"), Name], Means::TheFile),
        "through a link to the directory: one file with two physical-looking paths",
    ),
    (
        Dimension::LongPath,
        relative(&[Dir, Lit(b"/"), Repeat(b"./", 2100), Name], Means::Nothing),
        "a path longer than one call takes, which names the file once normalised",
    ),
];

/// The alphabet of hostile spellings.
pub fn alphabet() -> &'static Alphabet<Spelling> {
    static ALPHABET: OnceLock<Alphabet<Spelling>> = OnceLock::new();
    ALPHABET.get_or_init(|| {
        Alphabet::new(
            Kind::PathSpelling,
            TABLE
                .iter()
                .map(|(dimension, value, why)| Entry {
                    dimension: *dimension,
                    value: *value,
                    why,
                })
                .collect(),
        )
    })
}

/// Whether the file system at `dir` ignores case: whether a file made there
/// under one name is found under the name in another case.
pub fn ignores_case(dir: &Path) -> bool {
    let probe = tempfile::Builder::new()
        .prefix("case-probe-x")
        .tempfile_in(dir)
        .expect("create a probe file");
    let name = probe
        .path()
        .file_name()
        .and_then(|n| n.to_str())
        .expect("the probe's name is text")
        .to_ascii_uppercase();
    dir.join(name).exists()
}

/// What `path` is, for checking a spelling's [`Means`] against a tree: the
/// file `file`, something else, or nothing.
pub fn resolve(path: &Path, file: &Path) -> Resolved {
    let (Ok(found), Ok(file)) = (path.canonicalize(), file.canonicalize()) else {
        return Resolved::Nothing;
    };
    // A trailing separator on a file is `ENOTDIR` to `open` and yet resolves
    // on some platforms' `realpath`; ask the question a reader asks.
    if std::fs::metadata(path).is_err() {
        return Resolved::Nothing;
    }
    if found == file {
        Resolved::TheFile
    } else {
        Resolved::SomethingElse(found)
    }
}

/// What a spelling resolved to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Resolved {
    /// The file.
    TheFile,
    /// Another path that exists.
    SomethingElse(PathBuf),
    /// Nothing.
    Nothing,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hostile::fs::State;
    use crate::hostile::name;

    #[test]
    fn the_alphabet_covers_every_spelling_dimension() {
        assert_eq!(alphabet().kind(), Kind::PathSpelling);
    }

    /// Each spelling's `means` is what the file system does with it.
    #[test]
    fn every_spelling_means_what_it_says() {
        let fs = HostileFs::new();
        let plain = name::Name {
            parts: name::PLAIN,
            twin: None,
        }
        .render("Lib", ".fs");
        let file = fs.place("sub", &plain, State::Regular, b"x").unwrap().path;
        prepare(&fs, "sub");
        let folds = ignores_case(fs.tree());
        for entry in alphabet().entries() {
            let spelling = entry.value;
            let absolute = PathBuf::from(spelling.absolute(fs.tree(), "sub", "Lib.fs"));
            let got = resolve(&absolute, &file);
            let expected_file = match spelling.means {
                Means::TheFile => true,
                Means::TheFileIfCaseIsIgnored => folds,
                Means::Nothing | Means::SomethingElse => false,
            };
            match spelling.means {
                _ if expected_file => assert_eq!(got, Resolved::TheFile, "{}", entry.why),
                Means::SomethingElse => {
                    assert!(matches!(got, Resolved::SomethingElse(_)), "{}", entry.why)
                }
                _ => assert_eq!(got, Resolved::Nothing, "{}", entry.why),
            }
            if !spelling.rooted {
                assert!(
                    absolute.starts_with(fs.tree())
                        || entry.dimension == Dimension::ParentEscape
                        || entry.dimension == Dimension::DotDotThroughLink,
                    "{absolute:?}"
                );
                assert!(
                    Path::new(&spelling.relative("sub", "Lib.fs")).is_relative(),
                    "{}",
                    entry.why
                );
            }
        }
    }

    #[test]
    fn the_plain_spelling_is_the_file() {
        assert_eq!(PLAIN.relative("sub", "Lib.fs"), "sub/Lib.fs");
        assert_eq!(
            PLAIN.absolute(Path::new("/b"), "sub", "Lib.fs"),
            "/b/sub/Lib.fs"
        );
    }
}
