//! Hostile file-system states, and the fixture builder that makes them
//! ([`Kind::FsState`](super::Kind::FsState),
//! [`Kind::FsChange`](super::Kind::FsChange),
//! [`Kind::FsRace`](super::Kind::FsRace)).
//!
//! [`HostileFs`] puts any [`State`] at any name under a tree, and applies any
//! [`Change`] to a file between two requests. A state or a name the platform
//! cannot make comes back as [`Unmakeable`] with the reason, which the caller
//! hands to its census ([`super::census::Census::unmakeable`]): a state is
//! never skipped silently, and an error the builder does not expect is a
//! panic, not a skip.
//!
//! The states of [`Race`] happen *during* a request, so no builder outside
//! the subject can make them: each boundary makes them with a hook in its own
//! file-system layer.

use std::ffi::OsStr;
use std::fs::{self, File, Permissions};
use std::io::{self, Read, Seek, Write};
use std::os::unix::fs::{FileTypeExt, PermissionsExt, symlink};
use std::os::unix::net::UnixListener;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::SystemTime;

use super::Dimension;
use super::name::{NotAComponent, Rendered};

/// What sits at a path.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum State {
    /// A regular file holding the content.
    Regular,
    /// A regular file of no bytes.
    Empty,
    /// A FIFO.
    Fifo,
    /// A socket.
    Socket,
    /// A link to `/dev/null`: a character device to whatever follows links.
    CharDevice,
    /// A link to a regular file in the tree, which holds the content.
    Symlink,
    /// A link to a path where nothing is.
    DanglingSymlink,
    /// A link to itself.
    SymlinkLoop,
    /// A link to a regular file outside the tree, which holds the content.
    SymlinkOutOfTree,
    /// An empty directory.
    Directory,
    /// A regular file holding the content, which its owner may not read.
    Unreadable,
    /// A regular file holding the content, which its owner may not write.
    ReadOnly,
    /// Nothing, in a directory that exists.
    Missing,
}

impl State {
    /// Every state.
    pub const ALL: &'static [State] = &[
        State::Regular,
        State::Empty,
        State::Fifo,
        State::Socket,
        State::CharDevice,
        State::Symlink,
        State::DanglingSymlink,
        State::SymlinkLoop,
        State::SymlinkOutOfTree,
        State::Directory,
        State::Unreadable,
        State::ReadOnly,
        State::Missing,
    ];

    /// The state's dimension.
    pub fn dimension(self) -> Dimension {
        match self {
            State::Regular => Dimension::Regular,
            State::Empty => Dimension::Empty,
            State::Fifo => Dimension::Fifo,
            State::Socket => Dimension::Socket,
            State::CharDevice => Dimension::CharDevice,
            State::Symlink => Dimension::Symlink,
            State::DanglingSymlink => Dimension::DanglingSymlink,
            State::SymlinkLoop => Dimension::SymlinkLoop,
            State::SymlinkOutOfTree => Dimension::SymlinkOutOfTree,
            State::Directory => Dimension::Directory,
            State::Unreadable => Dimension::Unreadable,
            State::ReadOnly => Dimension::ReadOnly,
            State::Missing => Dimension::Missing,
        }
    }
}

/// The alphabet of file-system states: every [`State`], under its dimension,
/// for a harness that enumerates them ([`super::Alphabet::entries`]) or mixes
/// them into its own at [`super::RATE`] ([`super::Alphabet::sample`]). A
/// state is made with [`HostileFs::place`].
pub fn alphabet() -> &'static super::Alphabet<State> {
    static ALPHABET: std::sync::OnceLock<super::Alphabet<State>> = std::sync::OnceLock::new();
    ALPHABET.get_or_init(|| {
        super::Alphabet::new(
            super::Kind::FsState,
            State::ALL
                .iter()
                .map(|state| super::Entry {
                    dimension: state.dimension(),
                    value: *state,
                    why: state.dimension().why(),
                })
                .collect(),
        )
    })
}

/// A file changing between two requests.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Change {
    /// Rewritten in place with other bytes of the same length, the
    /// modification time put back.
    SameStampRewrite,
    /// Rewritten in place with bytes of another length, the modification
    /// time put back.
    SameStampResize,
    /// Replaced by renaming another file over it, which is given the old
    /// modification time.
    SameStampReplace,
    /// Created where nothing was.
    Appears,
    /// Removed.
    Disappears,
}

impl Change {
    /// Every change.
    pub const ALL: &'static [Change] = &[
        Change::SameStampRewrite,
        Change::SameStampResize,
        Change::SameStampReplace,
        Change::Appears,
        Change::Disappears,
    ];

    /// The change's dimension.
    pub fn dimension(self) -> Dimension {
        match self {
            Change::SameStampRewrite => Dimension::SameStampRewrite,
            Change::SameStampResize => Dimension::SameStampResize,
            Change::SameStampReplace => Dimension::SameStampReplace,
            Change::Appears => Dimension::Appears,
            Change::Disappears => Dimension::Disappears,
        }
    }
}

/// A file changing while one request reads it. Made by a hook in the
/// boundary's own file-system layer, not by [`HostileFs`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Race {
    /// Deleted between the listing that named it and the open.
    DeletedAfterListing,
    /// Rewritten between two reads of one request.
    RewrittenDuringRequest,
    /// Replaced between the read that identified it and the read that used
    /// it.
    ReplacedAfterHash,
    /// Recorded absent, and present before the request ends.
    AppearsDuringRequest,
}

impl Race {
    /// Every race.
    pub const ALL: &'static [Race] = &[
        Race::DeletedAfterListing,
        Race::RewrittenDuringRequest,
        Race::ReplacedAfterHash,
        Race::AppearsDuringRequest,
    ];

    /// The race's dimension.
    pub fn dimension(self) -> Dimension {
        match self {
            Race::DeletedAfterListing => Dimension::DeletedAfterListing,
            Race::RewrittenDuringRequest => Dimension::RewrittenDuringRequest,
            Race::ReplacedAfterHash => Dimension::ReplacedAfterHash,
            Race::AppearsDuringRequest => Dimension::AppearsDuringRequest,
        }
    }
}

/// Why no file can have a name here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NameRefusal {
    /// It is not one path component.
    NotAComponent(NotAComponent),
    /// The file system takes no name this long.
    TooLong,
    /// The file system takes no name that is not UTF-8 (APFS).
    NotUtf8,
    /// The file system takes the name and its twin for one file.
    Folded,
}

impl std::fmt::Display for NameRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameRefusal::NotAComponent(why) => why.fmt(f),
            NameRefusal::TooLong => f.write_str("the file system takes no name this long"),
            NameRefusal::NotUtf8 => f.write_str("the file system takes no name that is not UTF-8"),
            NameRefusal::Folded => {
                f.write_str("the file system takes the name and its twin for one file")
            }
        }
    }
}

/// What the platform could not make, and why. Printed by the census that is
/// handed it; never dropped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Unmakeable {
    /// No file can have the name here.
    Name {
        /// Why.
        why: NameRefusal,
    },
    /// The name is fine and the state cannot be made here.
    State {
        /// The state.
        state: State,
        /// Why.
        reason: String,
        /// Whether the platform can make the state under no name at all
        /// (as opposed to not under this one).
        whole: bool,
    },
    /// The change cannot be made here.
    Change {
        /// The change.
        change: Change,
        /// Why.
        reason: String,
    },
}

impl Unmakeable {
    /// The dimension of which the platform can make *no* value, if this
    /// refusal shows that: what a census may excuse on its strength. A
    /// refusal of one value (a name with a NUL, a name too long) shows
    /// nothing about the other values of its dimension, and excuses none.
    pub fn excuses(&self) -> Option<Dimension> {
        match self {
            Unmakeable::Name {
                why: NameRefusal::NotUtf8,
            } => Some(Dimension::NonUtf8),
            Unmakeable::Name { .. } => None,
            Unmakeable::State { state, whole, .. } => whole.then(|| state.dimension()),
            // One stamp the file system did not keep says nothing of the
            // stamps it does keep.
            Unmakeable::Change { .. } => None,
        }
    }
}

impl std::fmt::Display for Unmakeable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Unmakeable::Name { why } => write!(f, "the name cannot be made: {why}"),
            Unmakeable::State { state, reason, .. } => {
                write!(f, "{} cannot be made: {reason}", state.dimension())
            }
            Unmakeable::Change { change, reason } => {
                write!(f, "{} cannot be made: {reason}", change.dimension())
            }
        }
    }
}

/// What [`HostileFs::place`] made.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Placed {
    /// The path the state sits at.
    pub path: PathBuf,
    /// The file a link points at, where the state is a link to a file that
    /// exists.
    pub target: Option<PathBuf>,
}

/// A fixture tree that can hold every [`State`].
///
/// It has two directories: the *tree*, which is what the subject is shown,
/// and a directory *aside* from it, where the targets of links out of the
/// tree live. A link to a file in the tree points into `linked/` under the
/// tree's root, so a subject that walks the whole tree meets those targets as
/// files in their own right.
#[derive(Debug)]
pub struct HostileFs {
    tree: PathBuf,
    aside: PathBuf,
    /// Numbers the link targets, so two links never share one.
    next: AtomicUsize,
    /// Owns the directories when the fixture made them.
    _owned: Option<tempfile::TempDir>,
}

/// The directory under the tree's root holding the targets of
/// [`State::Symlink`].
pub const LINKED: &str = "linked";

impl Default for HostileFs {
    fn default() -> Self {
        Self::new()
    }
}

impl HostileFs {
    /// A fresh fixture in a temporary directory of its own.
    pub fn new() -> Self {
        let owned = tempfile::tempdir().expect("create a temporary directory");
        // The canonical path: a harness compares paths with a subject that
        // may canonicalise, and macOS's temporary directory is behind a link.
        let root = owned
            .path()
            .canonicalize()
            .expect("canonicalise the temporary directory");
        let (tree, aside) = (root.join("tree"), root.join("aside"));
        fs::create_dir(&tree).expect("create the tree");
        fs::create_dir(&aside).expect("create the directory aside");
        HostileFs {
            tree,
            aside,
            next: AtomicUsize::new(0),
            _owned: Some(owned),
        }
    }

    /// A fixture over a tree the harness made, with `aside` a directory
    /// outside it on the same file system.
    ///
    /// # Panics
    ///
    /// If either directory does not exist, or if `aside` is inside `tree`: a
    /// link "out of the tree" would then point into it.
    pub fn over(tree: &Path, aside: &Path) -> Self {
        // Canonical and absolute: a link's target is read against the link's
        // own directory, and containment is checked against real paths.
        let canonical = |dir: &Path| {
            dir.canonicalize()
                .unwrap_or_else(|e| panic!("{} is no directory to build in: {e}", dir.display()))
        };
        let (tree, aside) = (canonical(tree), canonical(aside));
        assert!(
            !aside.starts_with(&tree),
            "{} is inside the tree {}",
            aside.display(),
            tree.display()
        );
        HostileFs {
            tree,
            aside,
            next: AtomicUsize::new(0),
            _owned: None,
        }
    }

    /// The tree's root.
    pub fn tree(&self) -> &Path {
        &self.tree
    }

    /// The directory aside from the tree, where the targets of links out of
    /// it live.
    pub fn aside(&self) -> &Path {
        &self.aside
    }

    /// Whether the tree's file system holds `a` and `b` apart as two names.
    /// A name and its twin ([`super::name::Name::twin`]) are one file to a
    /// file system that folds case or normal forms, and a fixture cannot
    /// hold both there.
    ///
    /// # Errors
    ///
    /// [`Unmakeable::Name`] if either name cannot be made, or if the file
    /// system takes the two for one.
    pub fn holds_apart(&self, first: &Rendered, second: &Rendered) -> Result<(), Unmakeable> {
        let name = |r: &Rendered| {
            r.component()
                .map(ToOwned::to_owned)
                .map_err(|why| Unmakeable::Name {
                    why: NameRefusal::NotAComponent(why),
                })
        };
        let (a, b) = (name(first)?, name(second)?);
        let dir = self.target_dir(&self.aside);
        write_new(&dir.join(&a), b"").map_err(|e| match name_refusal_in(&e, first, &dir) {
            Some(why) => Unmakeable::Name { why },
            None => panic!("probe {a:?}: {e}"),
        })?;
        // Made, not looked up: a name that cannot be found may still be one
        // that cannot be made.
        match write_new(&dir.join(&b), b"") {
            Ok(()) => Ok(()),
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => Err(Unmakeable::Name {
                why: NameRefusal::Folded,
            }),
            Err(e) => match name_refusal_in(&e, second, &dir) {
                Some(why) => Err(Unmakeable::Name { why }),
                None => panic!("probe {b:?}: {e}"),
            },
        }
    }

    /// The directory `dir` names under the tree, created if need be.
    ///
    /// # Panics
    ///
    /// If `dir` could name a directory outside the tree: if it is rooted,
    /// holds a `..`, or goes through anything that is not a real directory
    /// of the tree (a link, which may point out of it). A fixture must not
    /// write outside its own directory, whatever its caller generated, so
    /// each component is checked before anything is made below it.
    pub(super) fn directory(&self, dir: &Path) -> PathBuf {
        assert!(
            dir.components().all(|c| matches!(c, Component::Normal(_))),
            "{dir:?} is not a plain relative path, so it may name a directory outside the tree"
        );
        let mut path = self.tree.clone();
        for component in dir.components() {
            path.push(component);
            match fs::symlink_metadata(&path) {
                Ok(found) if found.is_dir() => {}
                Ok(_) => panic!(
                    "{} is on the way to {dir:?} and is no directory of the tree (a link or a \
                     file), so it may name a directory outside the tree",
                    path.display()
                ),
                Err(e) if e.kind() == io::ErrorKind::NotFound => match fs::create_dir(&path) {
                    Ok(()) => {}
                    // Another thread of the harness made it first: fine, if
                    // what it made is a directory of the tree.
                    Err(e)
                        if e.kind() == io::ErrorKind::AlreadyExists
                            && fs::symlink_metadata(&path).is_ok_and(|m| m.is_dir()) => {}
                    Err(e) => panic!("create {}: {e}", path.display()),
                },
                Err(e) => panic!("stat {}: {e}", path.display()),
            }
        }
        path
    }

    /// A directory nothing else holds, for one link's target, under `base`
    /// (which exists).
    pub(super) fn target_dir(&self, base: &Path) -> PathBuf {
        loop {
            let n = self.next.fetch_add(1, Ordering::Relaxed);
            let dir = base.join(n.to_string());
            // Created, never reused: a tree the caller made may hold a
            // directory of the same name.
            match fs::create_dir(&dir) {
                Ok(()) => return dir,
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
                Err(e) => panic!("create {}: {e}", dir.display()),
            }
        }
    }

    /// Put `state` at `name` in the directory `dir` under the tree. `content`
    /// is what a regular file there holds, or the file a link there points
    /// at; the states with no content ignore it.
    ///
    /// # Errors
    ///
    /// [`Unmakeable`] if the platform cannot hold the name or make the state.
    /// Nothing is left at the path then.
    ///
    /// # Panics
    ///
    /// If something is at the path already, if `dir` is not a plain relative
    /// path, or on any error other than the platform refusing the name or
    /// the state.
    pub fn place(
        &self,
        dir: impl AsRef<Path>,
        name: &Rendered,
        state: State,
        content: &[u8],
    ) -> Result<Placed, Unmakeable> {
        let component = name
            .component()
            .map_err(|why: NotAComponent| Unmakeable::Name {
                why: NameRefusal::NotAComponent(why),
            })?;
        let parent = self.directory(dir.as_ref());
        let path = parent.join(component);
        assert!(
            fs::symlink_metadata(&path)
                .is_err_and(|e| e.kind() == io::ErrorKind::NotFound || name_refusal(&e).is_some()),
            "{} exists already",
            path.display()
        );
        // A refusal is the platform's only if it is shown to be: an error
        // that could as well be a broken fixture is a panic.
        let made = |result: io::Result<()>| -> Result<(), Unmakeable> {
            result.map_err(|e| match name_refusal_in(&e, name, &parent) {
                Some(why) => Unmakeable::Name { why },
                None => panic!("make {state:?} at {}: {e}", path.display()),
            })
        };
        // The operations that make something other than a file or a
        // directory. One the platform does not permit or support is the
        // state's refusal if a regular file of the same name can be made.
        let special = |result: io::Result<()>| -> Result<(), Unmakeable> {
            let Err(e) = result else { return Ok(()) };
            let unpermitted = matches!(
                e.kind(),
                io::ErrorKind::PermissionDenied | io::ErrorKind::Unsupported
            );
            if unpermitted && name_refusal(&e).is_none() {
                made(write_new(&path, b""))?;
                fs::remove_file(&path).expect("remove the probe file");
                return Err(Unmakeable::State {
                    state,
                    reason: format!("the platform does not make one here: {e}"),
                    whole: true,
                });
            }
            made(Err(e))
        };
        let mut target = None;
        match state {
            State::Regular => made(write_new(&path, content))?,
            State::Empty => made(write_new(&path, b""))?,
            State::Missing => {
                // Whether the name could exist is still the platform's to
                // say: a name it refuses is not "missing" but unmakeable.
                made(write_new(&path, b""))?;
                fs::remove_file(&path).expect("remove the probe file");
            }
            State::Directory => made(fs::create_dir(&path))?,
            State::Fifo => special(mkfifo(&path))?,
            State::Socket => match bind_socket(&parent, component) {
                Ok(()) => {}
                Err(SocketFailure::Path(reason)) => {
                    // A shorter name may fit: this is no verdict on sockets.
                    return Err(Unmakeable::State {
                        state,
                        reason,
                        whole: false,
                    });
                }
                Err(SocketFailure::Io(e)) => special(Err(e))?,
            },
            State::CharDevice => {
                let null = Path::new("/dev/null");
                if !fs::metadata(null).is_ok_and(|m| m.file_type().is_char_device()) {
                    return Err(Unmakeable::State {
                        state,
                        reason: "/dev/null is not a character device here".into(),
                        whole: true,
                    });
                }
                special(symlink(null, &path))?;
            }
            State::Symlink | State::SymlinkOutOfTree => {
                let base = if state == State::Symlink {
                    self.directory(Path::new(LINKED))
                } else {
                    self.aside.clone()
                };
                let to = self.target_dir(&base).join(component);
                made(fs::write(&to, content))?;
                special(symlink(&to, &path))?;
                target = Some(to);
            }
            State::DanglingSymlink => {
                let nowhere = self.target_dir(&self.aside).join("nowhere");
                special(symlink(&nowhere, &path))?;
            }
            State::SymlinkLoop => special(symlink(component, &path))?,
            State::Unreadable => {
                made(write_new(&path, content))?;
                fs::set_permissions(&path, Permissions::from_mode(0o000))
                    .expect("clear the file's mode");
                if File::open(&path).is_ok() {
                    fs::remove_file(&path).expect("remove the readable file");
                    return Err(Unmakeable::State {
                        state,
                        reason: "this user reads a file whatever its mode (root?)".into(),
                        whole: true,
                    });
                }
            }
            State::ReadOnly => {
                made(write_new(&path, content))?;
                fs::set_permissions(&path, Permissions::from_mode(0o444))
                    .expect("make the file read-only");
                if File::options().write(true).open(&path).is_ok() {
                    fs::remove_file(&path).expect("remove the writable file");
                    return Err(Unmakeable::State {
                        state,
                        reason: "this user writes a file whatever its mode (root?)".into(),
                        whole: true,
                    });
                }
            }
        }
        Ok(Placed { path, target })
    }

    /// Apply `change` to the file at `path`, which must be under the tree.
    /// `new` is what the file holds afterwards (ignored by
    /// [`Change::Disappears`]).
    ///
    /// # Errors
    ///
    /// [`Unmakeable`] if the file system does not give back the stamp it was
    /// asked to keep.
    ///
    /// # Panics
    ///
    /// If the file is not in the state the change starts from (a rewrite
    /// needs a regular file and new bytes that differ, of the same length or
    /// not as the change says; an appearance needs nothing at the path), or
    /// on an I/O error.
    pub fn change(&self, path: &Path, change: Change, new: &[u8]) -> Result<(), Unmakeable> {
        // Where the change lands, not how the path is spelt: a `..` or a
        // link to a directory would take it out of the tree.
        let parent = path
            .parent()
            .filter(|_| path.file_name().is_some())
            .and_then(|parent| parent.canonicalize().ok());
        assert!(
            parent.is_some_and(|parent| parent.starts_with(&self.tree)),
            "{} is outside the tree",
            path.display()
        );
        let unkept = |reason: String| Unmakeable::Change { change, reason };
        match change {
            Change::Appears => {
                assert!(
                    fs::symlink_metadata(path).is_err(),
                    "{} is there already",
                    path.display()
                );
                write_new(path, new).expect("write the file that appears");
            }
            Change::Disappears => {
                fs::remove_file(path).expect("remove the file that disappears");
            }
            Change::SameStampRewrite | Change::SameStampResize | Change::SameStampReplace => {
                // One handle on the file, opened without following a link:
                // what is checked is then what is read and rewritten,
                // whatever becomes of the path meanwhile.
                assert!(
                    fs::symlink_metadata(path).is_ok_and(|entry| entry.is_file()),
                    "{} is no regular file",
                    path.display()
                );
                let mut file = {
                    use std::os::unix::fs::OpenOptionsExt;
                    File::options()
                        .read(true)
                        .write(change != Change::SameStampReplace)
                        .custom_flags(libc::O_NOFOLLOW)
                        .open(path)
                        .expect("open the file to change")
                };
                let before = file.metadata().expect("stat the file to change");
                assert!(before.is_file(), "{} is no regular file", path.display());
                if change != Change::SameStampReplace {
                    use std::os::unix::fs::MetadataExt;
                    // A rewrite in place rewrites every name the file has,
                    // and another of them may be outside the tree.
                    assert_eq!(
                        before.nlink(),
                        1,
                        "{} has other hard links, which a rewrite in place would change too",
                        path.display()
                    );
                }
                let mut old = Vec::new();
                file.read_to_end(&mut old).expect("read the file to change");
                assert_ne!(old, new, "the change must change the bytes");
                match change {
                    Change::SameStampRewrite => assert_eq!(
                        old.len(),
                        new.len(),
                        "a same-stamp rewrite keeps the length"
                    ),
                    Change::SameStampResize => assert_ne!(
                        old.len(),
                        new.len(),
                        "a same-stamp resize changes the length"
                    ),
                    _ => {}
                }
                let stamp = before.modified().expect("the file's modification time");
                if change == Change::SameStampReplace {
                    let staged = self.target_dir(&self.aside).join("staged");
                    fs::write(&staged, new).expect("write the replacement");
                    set_modified(&staged, stamp);
                    // A rename replaces the entry at the path, link or file,
                    // and writes through neither.
                    fs::rename(&staged, path).expect("rename the replacement into place");
                } else {
                    file.set_len(0).expect("empty the file");
                    file.rewind().expect("return to the file's start");
                    file.write_all(new).expect("rewrite the file");
                    file.set_modified(stamp)
                        .expect("set the file's modification time");
                }
                drop(file);
                let after = fs::symlink_metadata(path).expect("stat the changed file");
                let kept = after.modified().expect("the file's modification time");
                if kept != stamp {
                    return Err(unkept(format!(
                        "the file system gave back {kept:?} for the modification time {stamp:?}"
                    )));
                }
            }
        }
        Ok(())
    }
}

/// Write `content` to a file made at `path`, where nothing may be: two
/// placements of one name collide here instead of one silently replacing the
/// other.
fn write_new(path: &Path, content: &[u8]) -> io::Result<()> {
    use std::io::Write;
    File::create_new(path)?.write_all(content)
}

/// Set `path`'s modification time.
fn set_modified(path: &Path, stamp: SystemTime) {
    File::options()
        .write(true)
        .open(path)
        .and_then(|f| f.set_modified(stamp))
        .unwrap_or_else(|e| panic!("set the modification time of {}: {e}", path.display()));
}

/// Why the platform refused to make a file of some name, if `error` is that
/// refusal: the name is too long, or is not text on a file system that
/// requires text (APFS).
fn name_refusal(error: &io::Error) -> Option<NameRefusal> {
    match error.raw_os_error()? {
        libc::ENAMETOOLONG => Some(NameRefusal::TooLong),
        libc::EILSEQ => Some(NameRefusal::NotUtf8),
        _ => None,
    }
}

/// [`name_refusal`], and the refusal some sandboxes give a name that is not
/// text: a plain permission error. That is the name's if another name can be
/// made in `dir`, the directory `name` was to be made in.
fn name_refusal_in(error: &io::Error, name: &Rendered, dir: &Path) -> Option<NameRefusal> {
    name_refusal(error).or_else(|| {
        (error.kind() == io::ErrorKind::PermissionDenied
            && name.to_str().is_none()
            && tempfile::tempfile_in(dir).is_ok())
        .then_some(NameRefusal::NotUtf8)
    })
}

fn mkfifo(path: &Path) -> io::Result<()> {
    use std::os::unix::ffi::OsStrExt;
    let c = std::ffi::CString::new(path.as_os_str().as_bytes())
        .expect("a path holding a NUL was refused as a component");
    // SAFETY: `c` is a NUL-terminated string that outlives the call.
    if unsafe { libc::mkfifo(c.as_ptr(), 0o600) } == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

enum SocketFailure {
    /// The socket's path does not fit a socket address.
    Path(String),
    Io(io::Error),
}

/// Bind a socket named `name` in `dir`, and leave it there.
///
/// A socket address holds about a hundred bytes of path, fewer than a
/// temporary directory's own path on macOS, so the bind goes through a short
/// link to `dir`: one under the temporary directory, and if that is itself
/// too long, one under `/tmp`.
fn bind_socket(dir: &Path, name: &OsStr) -> Result<(), SocketFailure> {
    let mut too_long = None;
    #[allow(
        clippy::disallowed_methods,
        reason = "a short directory for a socket's link, wherever one is; not a build's environment"
    )]
    let bases = [std::env::temp_dir(), PathBuf::from("/tmp")];
    for base in bases {
        let Ok(short) = tempfile::Builder::new().prefix("s").tempdir_in(&base) else {
            continue;
        };
        let link = short.path().join("d");
        symlink(dir, &link).map_err(SocketFailure::Io)?;
        match UnixListener::bind(link.join(name)) {
            Ok(_listener) => return Ok(()),
            // The standard library refuses a path that does not fit before
            // it asks the operating system.
            Err(e) if e.kind() == io::ErrorKind::InvalidInput => too_long = Some(e),
            Err(e) => return Err(SocketFailure::Io(e)),
        }
    }
    Err(SocketFailure::Path(match too_long {
        Some(e) => format!("a socket address has no room for the path: {e}"),
        None => "no short directory could be made to bind the socket through".into(),
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hostile::name::{self, PLAIN};

    fn plain(text: &str) -> Rendered {
        name::Name {
            parts: PLAIN,
            twin: None,
        }
        .render(text, "")
    }

    /// What the file system says is at `path`: the state as a reader meets it.
    fn observed(path: &Path) -> &'static str {
        let Ok(link) = fs::symlink_metadata(path) else {
            return "nothing";
        };
        let kind = link.file_type();
        if kind.is_symlink() {
            return match fs::metadata(path) {
                Ok(m) if m.file_type().is_char_device() => "link to a character device",
                Ok(m) if m.is_file() => "link to a file",
                Ok(_) => "link to something else",
                Err(e) if e.kind() == io::ErrorKind::NotFound => "dangling link",
                Err(_) => "unresolvable link",
            };
        }
        if kind.is_fifo() {
            "fifo"
        } else if kind.is_socket() {
            "socket"
        } else if kind.is_dir() {
            "directory"
        } else if link.len() == 0 {
            "empty file"
        } else {
            match link.permissions().mode() & 0o777 {
                0o000 => "unreadable file",
                0o444 => "read-only file",
                _ => "file",
            }
        }
    }

    #[test]
    fn every_state_is_what_it_says() {
        let fs_ = HostileFs::new();
        for (i, state) in State::ALL.iter().enumerate() {
            let placed = match fs_.place("d", &plain(&format!("f{i}")), *state, b"content") {
                Ok(placed) => placed,
                Err(unmakeable) => {
                    // A platform may be unable to make a state at all (a
                    // user whom modes do not bind, a sandbox with no
                    // sockets), and must say so. It makes files and
                    // directories, or nothing here means anything.
                    assert!(
                        unmakeable.excuses() == Some(state.dimension()),
                        "{unmakeable}"
                    );
                    assert!(
                        !matches!(
                            state,
                            State::Regular | State::Empty | State::Missing | State::Directory
                        ),
                        "{unmakeable}"
                    );
                    eprintln!("hostile fs: {unmakeable}");
                    continue;
                }
            };
            let expected = match state {
                State::Regular => "file",
                State::Empty => "empty file",
                State::Fifo => "fifo",
                State::Socket => "socket",
                State::CharDevice => "link to a character device",
                State::Symlink | State::SymlinkOutOfTree => "link to a file",
                State::DanglingSymlink => "dangling link",
                State::SymlinkLoop => "unresolvable link",
                State::Directory => "directory",
                State::Unreadable => "unreadable file",
                State::ReadOnly => "read-only file",
                State::Missing => "nothing",
            };
            assert_eq!(observed(&placed.path), expected, "{state:?}");
            assert!(placed.path.starts_with(fs_.tree()));
            match (state, &placed.target) {
                (State::Symlink, Some(target)) => {
                    assert!(target.starts_with(fs_.tree().join(LINKED)));
                    assert_eq!(fs::read(target).unwrap(), b"content");
                }
                (State::SymlinkOutOfTree, Some(target)) => {
                    assert!(!target.starts_with(fs_.tree()));
                    assert_eq!(fs::read(target).unwrap(), b"content");
                }
                (_, target) => assert_eq!(*target, None, "{state:?}"),
            }
        }
    }

    #[test]
    fn every_state_has_its_own_dimension_and_every_fs_dimension_a_state() {
        use crate::hostile::Kind;
        use std::collections::BTreeSet;
        let states: BTreeSet<_> = State::ALL.iter().map(|s| s.dimension()).collect();
        assert_eq!(states.len(), State::ALL.len());
        assert_eq!(states, Kind::FsState.dimensions().collect());
        // The alphabet holds every state once, under its own dimension.
        assert_eq!(alphabet().kind(), Kind::FsState);
        assert_eq!(alphabet().entries().len(), State::ALL.len());
        assert!(
            alphabet()
                .entries()
                .iter()
                .all(|e| e.dimension == e.value.dimension())
        );
        let changes: BTreeSet<_> = Change::ALL.iter().map(|c| c.dimension()).collect();
        assert_eq!(changes.len(), Change::ALL.len());
        assert_eq!(changes, Kind::FsChange.dimensions().collect());
        let races: BTreeSet<_> = Race::ALL.iter().map(|r| r.dimension()).collect();
        assert_eq!(races.len(), Race::ALL.len());
        assert_eq!(races, Kind::FsRace.dimensions().collect());
    }

    /// The twin probe says of every name of the alphabet what `place` says:
    /// one the platform refuses comes back as the name's refusal, where it
    /// is a name's refusal at all, and the probe never panics on one.
    #[test]
    fn the_twin_probe_refuses_a_name_as_placing_it_does() {
        let fs_ = HostileFs::new();
        let plain = name::Name {
            parts: name::PLAIN,
            twin: None,
        }
        .render("Lib", ".fs");
        for (i, entry) in name::alphabet().entries().iter().enumerate() {
            let rendered = entry.value.render("Lib", ".fs");
            let placed = fs_.place(format!("twins/{i}"), &rendered, State::Regular, b"x");
            for probe in [
                fs_.holds_apart(&plain, &rendered),
                fs_.holds_apart(&rendered, &plain),
            ] {
                match (&placed, probe) {
                    (Ok(_), Ok(())) => {}
                    // A name the file system takes for the plain one.
                    (
                        Ok(_),
                        Err(Unmakeable::Name {
                            why: NameRefusal::Folded,
                        }),
                    ) => {}
                    (
                        Err(Unmakeable::Name { why: placing }),
                        Err(Unmakeable::Name { why: probing }),
                    ) => assert_eq!(*placing, probing, "{rendered:?}"),
                    (placed, probe) => panic!("{rendered:?}: placed {placed:?}, probed {probe:?}"),
                }
            }
        }
    }

    /// Every name of the alphabet is made, or refused for a reason that is
    /// the name's: nothing else stops a hostile name from being a file.
    #[test]
    fn every_hostile_name_is_made_or_refused_by_name() {
        let fs_ = HostileFs::new();
        let (mut made, mut refused) = (0, Vec::new());
        for (i, entry) in name::alphabet().entries().iter().enumerate() {
            let rendered = entry.value.render("Lib", ".fs");
            // A directory each: a file system that folds case or normal forms
            // holds some of these names as one.
            match fs_.place(format!("names/{i}"), &rendered, State::Regular, b"x") {
                Ok(placed) => {
                    made += 1;
                    assert_eq!(fs::read(&placed.path).unwrap(), b"x");
                    assert_eq!(
                        placed.path.file_name().map(|n| n.to_owned()),
                        Some(rendered.to_os_string()),
                        "the file has the name asked for"
                    );
                }
                Err(refusal @ Unmakeable::Name { .. }) => {
                    // Only a file system that takes no such name at all
                    // excuses a dimension, and only the one.
                    assert!(matches!(refusal.excuses(), None | Some(Dimension::NonUtf8)));
                    refused.push((entry.dimension, refusal.to_string()));
                }
                Err(other) => panic!("{rendered:?}: {other}"),
            }
        }
        // What no platform makes: `.`, `..`, the NUL-bearing name and the
        // 256-byte one. A platform may refuse more (APFS, the names that are
        // not UTF-8), and must say so.
        assert!(refused.len() >= 4, "{refused:?}");
        assert!(made > refused.len(), "{made} made, refused {refused:?}");
        for (dimension, reason) in &refused {
            eprintln!("hostile fs: a {dimension} name cannot be made: {reason}");
        }
        for must in [
            Dimension::SwitchShaped,
            Dimension::LineBreak,
            Dimension::Backslash,
        ] {
            assert!(
                refused.iter().all(|(d, _)| *d != must),
                "every {must} name is a legal file name"
            );
        }
    }

    #[test]
    fn a_same_stamp_change_changes_the_bytes_and_keeps_the_stamp() {
        let fs_ = HostileFs::new();
        for (change, new) in [
            (Change::SameStampRewrite, &b"abd"[..]),
            (Change::SameStampResize, b"abcd"),
            (Change::SameStampReplace, b"xyz"),
        ] {
            let name = plain(&format!("{change:?}"));
            let path = fs_.place("", &name, State::Regular, b"abc").unwrap().path;
            // A stamp well in the past, so that "now" could not pass for it.
            let stamp = SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000_000);
            set_modified(&path, stamp);
            let inode = {
                use std::os::unix::fs::MetadataExt;
                fs::metadata(&path).unwrap().ino()
            };
            fs_.change(&path, change, new).unwrap();
            let after = fs::metadata(&path).unwrap();
            assert_eq!(fs::read(&path).unwrap(), new);
            assert_eq!(after.modified().unwrap(), stamp, "{change:?}");
            {
                use std::os::unix::fs::MetadataExt;
                assert_eq!(
                    after.ino() != inode,
                    change == Change::SameStampReplace,
                    "{change:?}: only a replacement is a new file"
                );
            }
        }
    }

    #[test]
    fn a_file_appears_and_disappears() {
        let fs_ = HostileFs::new();
        let path = fs_
            .place("", &plain("f"), State::Missing, b"")
            .unwrap()
            .path;
        fs_.change(&path, Change::Appears, b"here").unwrap();
        assert_eq!(fs::read(&path).unwrap(), b"here");
        fs_.change(&path, Change::Disappears, b"").unwrap();
        assert_eq!(observed(&path), "nothing");
    }

    #[test]
    #[should_panic(expected = "may name a directory outside the tree")]
    fn a_directory_that_climbs_out_of_the_tree_is_refused() {
        let _ = HostileFs::new().place("../escape", &plain("f"), State::Regular, b"");
    }

    #[test]
    #[should_panic(expected = "may name a directory outside the tree")]
    fn a_rooted_directory_is_refused() {
        let _ = HostileFs::new().place("/tmp", &plain("f"), State::Regular, b"");
    }

    #[test]
    fn a_name_that_is_several_components_is_unmakeable_not_made_elsewhere() {
        let fs_ = HostileFs::new();
        let name = name::Name {
            parts: &[name::Part::Lit(b"../escape")],
            twin: None,
        }
        .render("", "");
        assert!(matches!(
            fs_.place("d", &name, State::Regular, b""),
            Err(Unmakeable::Name { .. })
        ));
        assert!(!fs_.tree().join("escape").exists());
    }

    #[test]
    #[should_panic(expected = "is no directory of the tree")]
    fn a_directory_through_a_link_is_refused() {
        let fs_ = HostileFs::new();
        symlink(fs_.aside(), fs_.tree().join("out")).unwrap();
        let _ = fs_.place("out/d", &plain("f"), State::Regular, b"");
    }

    #[test]
    fn a_change_outside_the_tree_is_refused_however_it_is_spelt() {
        let fs_ = HostileFs::new();
        let outside = fs_.aside().join("victim");
        fs::write(&outside, b"mine").unwrap();
        symlink(fs_.aside(), fs_.tree().join("out")).unwrap();
        for spelt in [
            fs_.tree().join("../aside/victim"),
            fs_.tree().join("out/victim"),
            outside.clone(),
        ] {
            let refused = std::panic::catch_unwind(|| {
                let _guard = crate::panic_silence::silence_panics_here();
                let _ = fs_.change(&spelt, Change::Disappears, b"");
            });
            assert!(refused.is_err(), "{}", spelt.display());
            assert_eq!(fs::read(&outside).unwrap(), b"mine");
        }
    }

    #[test]
    fn a_link_target_never_reuses_a_directory_the_tree_already_has() {
        let root = tempfile::tempdir().unwrap();
        let (tree, aside) = (root.path().join("t"), root.path().join("a"));
        fs::create_dir_all(tree.join(LINKED).join("0")).unwrap();
        fs::create_dir(&aside).unwrap();
        fs::write(tree.join(LINKED).join("0").join("f"), b"the caller's").unwrap();
        // Relative roots are resolved, so the link does not dangle.
        let fs_ = HostileFs::over(&tree, &aside);
        let placed = fs_.place("", &plain("f"), State::Symlink, b"new").unwrap();
        assert_eq!(fs::read(&placed.path).unwrap(), b"new");
        assert_eq!(
            fs::read(fs_.tree().join(LINKED).join("0").join("f")).unwrap(),
            b"the caller's"
        );
        assert!(placed.path.is_absolute());
    }

    #[test]
    #[should_panic(expected = "has other hard links")]
    fn a_rewrite_in_place_of_a_file_with_another_link_is_refused() {
        let fs_ = HostileFs::new();
        let path = fs_
            .place("", &plain("f"), State::Regular, b"abc")
            .unwrap()
            .path;
        fs::hard_link(&path, fs_.aside().join("other-name")).unwrap();
        let _ = fs_.change(&path, Change::SameStampRewrite, b"abd");
    }

    #[test]
    fn twins_are_held_apart_only_if_both_can_be_made() {
        let fs_ = HostileFs::new();
        assert_eq!(fs_.holds_apart(&plain("a"), &plain("b")), Ok(()));
        // The same name twice is one file, whatever the file system.
        assert_eq!(
            fs_.holds_apart(&plain("a"), &plain("a")),
            Err(Unmakeable::Name {
                why: NameRefusal::Folded
            })
        );
    }

    #[test]
    fn only_a_refusal_of_every_value_excuses_a_dimension() {
        let name = |why| Unmakeable::Name { why };
        assert_eq!(
            name(NameRefusal::NotUtf8).excuses(),
            Some(Dimension::NonUtf8)
        );
        assert_eq!(name(NameRefusal::TooLong).excuses(), None);
        assert_eq!(name(NameRefusal::Folded).excuses(), None);
        assert_eq!(
            name(NameRefusal::NotAComponent(NotAComponent::Dots)).excuses(),
            None
        );
        let state = |whole| Unmakeable::State {
            state: State::Socket,
            reason: String::new(),
            whole,
        };
        assert_eq!(state(true).excuses(), Some(Dimension::Socket));
        assert_eq!(state(false).excuses(), None);
        let change = Unmakeable::Change {
            change: Change::SameStampRewrite,
            reason: String::new(),
        };
        assert_eq!(change.excuses(), None);
    }

    #[test]
    #[should_panic(expected = "exists already")]
    fn placing_over_an_existing_file_is_refused() {
        let fs_ = HostileFs::new();
        fs_.place("", &plain("f"), State::Regular, b"").unwrap();
        let _ = fs_.place("", &plain("f"), State::Fifo, b"");
    }
}
