//! Confirming recorded reads against the disk, once per generation, by
//! stamps (`docs/incremental-lsp-plan.md`, D1 and D3).
//!
//! A project evaluation records every file-system query it made with the
//! answer it got ([`borzoi_msbuild::observed::ReadSet`]). Before a cached
//! evaluation is served in a new generation, each of its reads must still get
//! the answer recorded. Asking every query again costs a `realpath` or a
//! directory listing apiece, which on a real project is most of a keystroke;
//! so a [`Check`] remembers, the first time it is confirmed, a **witness**:
//! what the entries that decide the answer were, taken before the query was
//! asked. While every one of them is unchanged, the answer is too, and
//! confirming it costs an `lstat` per entry, which reads that share an entry
//! share within a generation.
//!
//! Why a directory's stamp decides what its entries are: creating, removing
//! or renaming an entry moves its directory's mtime and ctime, and so does
//! replacing a symlink (its target cannot be changed in place), and a `chmod`
//! moves its ctime. So, while the stamp of `d` holds, **a listing** of `d`
//! holds (its entries and their types), when it read every entry: a listing
//! that failed at some entry can recover with no entry changing. A listing's
//! witness is its directory's stamp, following every symlink in its path, and
//! the walk to the directory (below), which enters it as any other: the walk's
//! items are spelt as where the path leads, so a watch event above the
//! directory distrusts them however the listing spells it, and the walk is
//! born wide as every other.
//!
//! **What a path names**, following symlinks or not, whether it is there, and
//! **its canonical spelling** are decided by the steps of its resolution,
//! which `ReadChecks::resolution` walks as the kernel does (following
//! symlinks, a link's target component by component, and taking each `..`
//! from the directory reached). Each step looks one name up in the directory
//! reached, and while every step finds what it found, the answer is the one
//! recorded. A witness holds each step by
//!
//! - **the identity of a directory the path goes on below** (and of the
//!   root, which every walk enters): what the name names now, not following
//!   it (`lstat`), is a directory of the same device and inode, mode and
//!   owners ([`Access`]: whether the walk may search it, and follow a symlink
//!   in it). The directory the name is looked up in may gain, lose and
//!   rename other entries without moving it, so a dotfile made in `$HOME`
//!   asks nothing below `$HOME` again (#776). An identity has no timestamp,
//!   so it is never racy. A watch event that names the directory, or one
//!   above it, distrusts it ([`ReadChecks::hint`]): on a file system whose
//!   stamps do not move, a directory moved into its place, with inodes
//!   reused below it, is seen by nothing else.
//! - **the stamp of a symlink it follows** (`lstat`): a link replaced is a
//!   new link, whose ctime is new even where its inode is reused.
//! - **the stamp of the directory the last name is looked up in**: its
//!   entries (and its search permission) decide the last lookup.
//! - **the identity of `d/..` for a `.` or `..` looked up in `d`**: an
//!   `lstat` finds it only with search permission in `d`, which the lookup
//!   takes, and it is the directory a `..` returns to.
//!
//! These suffice by induction along the walk: while each identity holds, the
//! path walked so far names, now, the directory the kernel's walk of the
//! read's path is in, by the same steps (a directory where there was a
//! directory, never a symlink to one, which would change the canonical
//! spelling and the count of links followed), and the lookup of the name had
//! search permission; a `..` leaves a directory its identity places under
//! the one the walk returns to; and the last directory's stamp says the last
//! lookup finds what it found. An absence stops the walk at the directory it
//! was looked up in, and a listing that found its directory absent is
//! witnessed the same way.
//!
//! **A witness is born wide, and narrows once confirmed.** An identity says
//! what an entry is when it is looked at, and nothing about the time between:
//! a directory renamed away and back has its identity again. A stamp moves
//! for good. A witness must say what the disk held when the query was asked,
//! which is after the walk took the witness, so it is born **wide**: it also
//! holds the stamp of every directory the walk looked a name up in, each
//! taken before the lookup. The first later generation that finds every one
//! unchanged (and none racy) shows that no step changed from before the walk
//! until then, so the walk is what the query saw; the witness then
//! **narrows** to the identities and stamps above, and only those decide it.
//!
//! A canonicalisation narrows only where it spells each name as the read's
//! path does ([`Probe::canonical_spells_as_asked`]). Where it spells a name
//! as the directory holding it does (macOS's `realpath`, which reads each
//! name back from the volume; Windows's final path name), a case-only
//! rename of a directory the path enters moves the answer and leaves every
//! identity on the walk unchanged, and only the stamp of the directory the
//! name was looked up in sees it, so the witness stays wide.
//!
//! A relative path has no witness, and neither has an `lstat` of a path not
//! spelt as its components: a trailing separator makes it follow a final
//! symlink.
//!
//! Only a fact has a witness ([`a_fact`]): an answer, or an absence. A
//! read that failed otherwise (a permission, an I/O error, a listing that
//! failed at an entry) can recover with nothing on disk changing, and is
//! asked in every generation.
//!
//! Whole-file reads are confirmed by the file's own stamp
//! ([`DiskCache::text_answer`]). A read that failed for any reason but
//! absence is asked again in every generation, as is one whose resolution
//! met anything but an answer the walk understands.
//!
//! **Within a generation** an entry is `lstat`ed once, so a check holds as of
//! the moment its entries were looked at in that generation, as a
//! [`DiskCache`] read holds as of its file's stamp; a change after that
//! moment moves a stamp or an identity, and the next generation asks again.
//!
//! **Racy stamps.** A witness any of whose stamps lies within
//! [`crate::vfs::RACY_WINDOW`] of the generation that took it is not
//! trusted: the read is asked again (and the witness taken again) in every
//! generation until it is old, as [`crate::vfs`] does for files. The
//! generated-clock model in this module's tests holds the witnesses to that,
//! at timestamp granularities the host does not have.
//!
//! **A witness belongs to a read, not to the reader that recorded it.** It
//! says that while its entries are unchanged, the query gets the answer it
//! got when the witness was taken, and the witness is kept only if that
//! answer was the recorded one. Nothing in that names the evaluation or
//! the env that recorded the read: any read with the same path, spelt the
//! same, and the same recorded answer is confirmed by it exactly as far as
//! the read it was taken for. So a checker hands out one [`Check`] per
//! distinct read ([`ReadChecks::check`]), shared by every holder of that
//! read while any holds it: a project evaluated again, whose reads are
//! mostly those of the evaluation it replaces, starts with that
//! evaluation's witnesses, and an env whose resolution read the project's
//! evaluation shares the evaluation's. A shared witness is the same value
//! a fresh check would take, carried with its stamps, the time of the
//! generation that took them and the watch events it had seen, so the racy
//! rule and the hints judge it as they would have judged it for the read
//! it was taken for; and it names its checker, so no other checker's
//! entries can confirm it.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::ffi::OsString;
use std::hash::{Hash as _, Hasher as _};
use std::io;
use std::path::{Path, PathBuf};
use std::rc::{Rc, Weak};

#[cfg(test)]
use borzoi_msbuild::observed::EntryKind;
use borzoi_msbuild::observed::{Failure, FileStamp, Listed, Observation, Read, ReadCounts};

use crate::observed::HostDisk;
use crate::paths::lexically_normalize;
use crate::vfs::{Disk, DiskCache, Nanos, Stamp};

/// Whether a query's answer is a fact about what the disk holds: an answer
/// with nothing in it that failed, or the absence of the path. Any other
/// failure (a permission, an I/O error, a listing that failed at an entry)
/// can clear with nothing on disk changing, so neither a witness nor the
/// immutability of an installed version may speak for it.
pub fn a_fact(observation: &Observation) -> bool {
    fn answered_or_absent<T>(answer: &Result<T, Failure>) -> bool {
        answer.as_ref().err().is_none_or(Failure::is_absent)
    }
    match observation {
        Observation::Text(answer) => answered_or_absent(answer),
        Observation::Prefix { answer, .. } => answered_or_absent(answer),
        Observation::Kind(answer) | Observation::LinkKind(answer) => answered_or_absent(answer),
        Observation::Listing(Ok(entries)) => entries
            .iter()
            .all(|entry| matches!(entry, Listed::Entry { kind: Ok(_), .. })),
        Observation::Listing(Err(failure)) => failure.is_absent(),
        Observation::Canonical(answer) => answered_or_absent(answer),
        Observation::Stamp(answer) => {
            answered_or_absent(answer)
                && !observation.is_racy_stamp()
                && !answer.as_ref().is_ok_and(|stamp| stamp.unreadable)
        }
    }
}

/// How many symlinks a walk follows before it gives up, as `ELOOP` does.
const MAX_LINKS: usize = 40;

/// What one directory entry is, not following it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Dir,
    Link,
    /// Anything else (a file, a socket).
    Other,
}

/// What an `lstat` of a path finds: the stamp of the entry it names, not
/// following a final symlink, what kind of entry that is, and who may do
/// what with it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lstat {
    pub stamp: Stamp,
    pub kind: Kind,
    pub access: Access,
}

/// An entry's mode and owners: what decides, beside its entries, whether a
/// walk may search it and follow a symlink in it (Linux's
/// `fs.protected_symlinks` refuses one in a sticky, world-writable directory
/// owned by neither the follower nor the link's owner). None of them moves
/// with the entries, so an identity holds them too.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Access {
    pub mode: u32,
    pub uid: u32,
    pub gid: u32,
}

/// The file-system calls a [`ReadChecks`] makes beyond a [`Disk`]'s.
pub trait Probe: Disk {
    /// What the entry at `path` is, not following it (`lstat`).
    fn lstat(&self, path: &Path) -> io::Result<Lstat>;
    /// The target of the symlink at `path`, as written (`readlink`).
    fn read_link(&self, path: &Path) -> io::Result<PathBuf>;
    /// `query`'s query asked at `path` now, with its answer, as
    /// `borzoi_msbuild::observed` would record it.
    fn answer(&self, path: &Path, query: &Observation) -> Observation;
    /// The file at `path`, read whole now: its stamp, taken before the read,
    /// if its bytes are the ones `digest` names ([`FileStamp::digest`]), and
    /// `None` otherwise. A disk that cannot say confirms nothing.
    fn racy_content(&self, _path: &Path, _digest: u128) -> Option<FileStamp> {
        None
    }
    /// What a whole-file read of `path` records now
    /// (`borzoi_msbuild::observed::read_stamped_now`): how the stamp of a
    /// file such a read could not read is asked again. A disk that cannot
    /// read answers as a `stat` would.
    fn read_stamped(&self, path: &Path, query: &Observation) -> Observation {
        self.answer(path, query)
    }
    /// Whether a canonicalisation spells each name it keeps as the path
    /// asked spells it: the identities of the directories a path enters
    /// then decide its answer with the last lookup. Where the volume may be
    /// case-insensitive and the canonical path reads each name back from it
    /// (macOS, Windows), a case-only rename moves the answer and no identity.
    fn canonical_spells_as_asked(&self) -> bool {
        !cfg!(any(target_os = "macos", windows))
    }
}

/// One recorded read, and the witness that confirmed it last: a handle to
/// what its checker holds for that read ([`ReadChecks::check`]), shared with
/// every other holder of an equal read.
#[derive(Clone, Debug)]
pub struct Check {
    shared: Rc<Shared>,
}

/// What a checker knows about one distinct read.
#[derive(Debug)]
struct Shared {
    read: Read,
    witness: RefCell<Option<Witness>>,
    /// For a racy stamp a whole-file read took: a stamp of the file, not
    /// racy, taken before a read that found the bytes the racy one saw.
    /// While the file keeps it, the read holds with no read of the file
    /// ([`ReadChecks::racy_stamp_holds`]).
    confirmed: Cell<Option<FileStamp>>,
}

impl Shared {
    fn new(read: Read) -> Shared {
        Shared {
            read,
            witness: RefCell::new(None),
            confirmed: Cell::new(None),
        }
    }
}

impl Check {
    /// A check of `read` that shares nothing: its first confirmation asks
    /// the query again.
    #[cfg(test)]
    pub fn new(read: Read) -> Check {
        Check {
            shared: Rc::new(Shared::new(read)),
        }
    }

    pub fn read(&self) -> &Read {
        &self.shared.read
    }

    /// Whether `self` and `other` are one shared check.
    #[cfg(test)]
    pub fn shares(&self, other: &Check) -> bool {
        Rc::ptr_eq(&self.shared, &other.shared)
    }

    /// Whether the check's witness is still wide (see the module docs).
    #[cfg(test)]
    pub fn wide(&self) -> Option<bool> {
        self.shared.witness.borrow().as_ref().map(|w| w.wide)
    }
}

/// What a witness says about one path, as an entry of
/// [`ReadChecks::entries`] saw it when the witness was taken.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Seen {
    /// The path names, not following it, a directory of this device, inode
    /// and access: a step of a resolution that went on below it.
    Identity(Identity),
    /// The path names, not following it, an entry with this stamp: a
    /// directory whose entries decide a lookup, or a symlink followed.
    Entry(Lstat),
    /// The path, following every symlink, has this stamp: a directory
    /// listed.
    Followed(Stamp),
}

/// What an identity holds of a directory: everything an `lstat` finds of
/// it but what its entries move (its times and size).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Identity {
    dev: u64,
    ino: u64,
    access: Access,
}

impl Identity {
    fn of(lstat: &Lstat) -> Self {
        Identity {
            dev: lstat.stamp.dev,
            ino: lstat.stamp.ino,
            access: lstat.access,
        }
    }
}

impl Seen {
    /// The stamp a witness must not trust while it is racy, if any.
    fn stamp(&self) -> Option<&Stamp> {
        match self {
            Seen::Identity(_) => None,
            Seen::Entry(lstat) => Some(&lstat.stamp),
            Seen::Followed(stamp) => Some(stamp),
        }
    }
}

/// One thing a witness holds about one path.
#[derive(Clone, Copy, Debug)]
struct Item {
    /// The path, as its index in [`ReadChecks::entries`].
    id: usize,
    seen: Seen,
    /// Held only while the witness is wide: the stamp of a directory the
    /// walk looked a name up in that decides nothing once the walk is shown
    /// to be what the query saw (see the module docs).
    wide: bool,
}

/// What decides a read's answer, as it was before the query was asked, and
/// the time of the generation that took it.
#[derive(Clone, Debug)]
struct Witness {
    /// The checker that took it ([`ReadChecks::id`]), whose entries
    /// `items` indexes.
    checker: u64,
    items: Vec<Item>,
    /// Whether some item is still [`Item::wide`].
    wide: bool,
    /// The generation that took it: only a later one, which looks at its
    /// entries again, can show that the walk is what the query saw.
    born: u64,
    taken: Nanos,
    /// The checker's [`ReadChecks::hints`] when it was taken: a path hinted
    /// since ([`Entry::hinted`]) speaks for nothing it witnessed.
    hints: u64,
}

/// One path a witness names, and what the generation that last looked at it
/// saw there.
#[derive(Debug)]
struct Entry {
    path: PathBuf,
    /// What an `lstat` of it found, or why it found nothing.
    lstat: Result<Lstat, Missing>,
    checked: u64,
    /// The stamp of the path following a final symlink, in generation
    /// `followed_checked`: the `lstat`'s, unless that found a symlink.
    followed: Option<Stamp>,
    followed_checked: u64,
    /// The target of the symlink there, in generation `target_checked`.
    target: Option<PathBuf>,
    target_checked: u64,
    /// The [`ReadChecks::hints`] count of the last watch event that named
    /// this path, 0 if none has.
    hinted: u64,
    /// The same, for the last that named an entry of the directory here.
    hinted_entries: u64,
}

/// Why an `lstat` found no entry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Missing {
    /// Nothing is there: a walk stops at the directory it looked in.
    Absent,
    /// Anything else: no witness.
    Failed,
}

/// The identity the next [`ReadChecks`] gets.
static NEXT_READ_CHECKS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Confirms [`Check`]s for the open generation.
#[derive(Debug)]
pub struct ReadChecks<D: Probe = HostDisk> {
    /// No two checkers share one: a [`Check`]'s witness names paths by
    /// their index in the checker that took it, so a holder of checks
    /// confirms them only through that checker ([`Self::id`]).
    id: u64,
    /// Whole-file reads, confirmed by the file's stamp.
    files: DiskCache<D>,
    /// Every path a witness has named, `lstat`ed at most once per
    /// generation; witnesses name them by index, so confirming one looks
    /// nothing up by path.
    entries: RefCell<Vec<Entry>>,
    /// The index of each path in `entries`, by its spelling: `Path`'s
    /// equality ignores a trailing separator, which makes an `lstat` follow
    /// a final symlink.
    entry_ids: RefCell<HashMap<OsString, usize>>,
    /// The queries asked this generation beyond `files`' reads.
    counts: Cell<ReadCounts>,
    /// How many queries [`Self::ask`] has asked, ever.
    asked: Cell<u64>,
    /// How many watch events have hinted the checker ([`Self::hint`]).
    hints: Cell<u64>,
    /// The checks this checker has handed out ([`Self::check`]), by a hash
    /// of their reads, while something holds them.
    shared: RefCell<HashMap<u64, Vec<Weak<Shared>>>>,
    /// How many entries `shared` holds, released ones included, and how
    /// many were held when it was last swept: it is swept once it holds
    /// twice that, so the released entries it keeps stay bounded by the
    /// held ones.
    shared_entries: Cell<usize>,
    shared_held: Cell<usize>,
}

impl<D: Probe + Default> Default for ReadChecks<D> {
    fn default() -> Self {
        Self::with_disk(D::default())
    }
}

impl<D: Probe> ReadChecks<D> {
    pub fn with_disk(disk: D) -> Self {
        ReadChecks {
            id: NEXT_READ_CHECKS.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
            files: DiskCache::with_disk(disk),
            entries: RefCell::new(Vec::new()),
            entry_ids: RefCell::new(HashMap::new()),
            counts: Cell::new(ReadCounts::default()),
            asked: Cell::new(0),
            hints: Cell::new(0),
            shared: RefCell::new(HashMap::new()),
            shared_entries: Cell::new(0),
            shared_held: Cell::new(0),
        }
    }

    /// The check of `read`: the one this checker already handed out for an
    /// equal read (the same path, spelt the same, and the same answer), if
    /// something still holds it, and otherwise a new one. A held check
    /// carries the witness its last confirmation took, which confirms
    /// `read` exactly as far as it confirms the read it was taken for (see
    /// the module docs), so a read set recorded again starts with the
    /// witnesses of the reads it shares with any read set still held.
    pub fn check(&self, read: &Read) -> Check {
        let mut hasher = std::hash::DefaultHasher::new();
        read.hash(&mut hasher);
        let hash = hasher.finish();
        let mut shared = self.shared.borrow_mut();
        let bucket = shared.entry(hash).or_default();
        let before = bucket.len();
        bucket.retain(|entry| entry.strong_count() > 0);
        let mut entries = self.shared_entries.get() - (before - bucket.len());
        if let Some(held) = bucket
            .iter()
            .filter_map(Weak::upgrade)
            .find(|held| held.read == *read)
        {
            self.shared_entries.set(entries);
            return Check { shared: held };
        }
        let check = Check {
            shared: Rc::new(Shared::new(read.clone())),
        };
        bucket.push(Rc::downgrade(&check.shared));
        entries += 1;
        if entries > 2 * self.shared_held.get().max(64) {
            shared.retain(|_, bucket| {
                bucket.retain(|entry| entry.strong_count() > 0);
                !bucket.is_empty()
            });
            entries = shared.values().map(Vec::len).sum();
            self.shared_held.set(entries);
        }
        self.shared_entries.set(entries);
        check
    }

    /// Start a generation at `now` ([`DiskCache::begin_generation`]).
    pub fn begin_generation(&mut self, now: Nanos) {
        self.files.begin_generation(now);
        self.counts.set(ReadCounts::default());
    }

    /// End the generation, returning what confirming reads cost it.
    pub fn end_generation(&mut self) -> ReadCounts {
        let (_, files) = self.files.end_generation();
        let counts = self.counts.get();
        ReadCounts {
            opens: files.opens + counts.opens,
            stats: files.stats + counts.stats,
            ..counts
        }
    }

    /// The open generation's number, or `None` between generations.
    pub fn generation(&self) -> Option<u64> {
        self.files.generation()
    }

    /// Which checker this is: the witnesses of the checks it confirms name
    /// its entries, and only its.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// What confirming reads has cost the open generation so far, as
    /// [`Self::end_generation`] will report it.
    pub fn counts_so_far(&self) -> ReadCounts {
        let files = self.files.generation_counts();
        let counts = self.counts.get();
        ReadCounts {
            opens: files.opens + counts.opens,
            stats: files.stats + counts.stats,
            ..counts
        }
    }

    /// How many recorded queries the checker has asked again, ever: each a
    /// read no witness confirmed.
    #[cfg(test)]
    pub fn asked(&self) -> u64 {
        self.asked.get()
    }

    /// The open generation's time, or `None` between generations.
    pub fn now(&self) -> Option<Nanos> {
        self.files.now()
    }

    /// The stamp of the file at `path` now (a counted `stat`), or `None`
    /// when it has none.
    pub fn stamp(&self, path: &Path) -> Option<Stamp> {
        self.count_stat();
        self.files.disk().stat(path).ok()
    }

    fn count_stat(&self) {
        let mut counts = self.counts.get();
        counts.stats += 1;
        self.counts.set(counts);
    }

    /// Watch events named `paths`: forget what the files there held, so the
    /// next check reads them again whatever their stamps say, and stop
    /// trusting every witness taken before now that holds anything of one of
    /// the paths or a path below one (a directory moved into place moves
    /// everything below it), or the stamp of a directory holding one, so the
    /// next check of each such read asks its query again. The identity of a
    /// directory, or the stamp of a symlink, is not distrusted by an event
    /// that names a sibling: the directory holding them does not decide what
    /// they say.
    ///
    /// That is what covers a file system whose stamps do not move (D1's "not
    /// covered") for the paths an event names: a file there is read again
    /// and compared, and what a path names, whether it is there, its
    /// canonical spelling and its directory's listing are asked again. A
    /// witness names a path by the spelling its walk reached it by, and a
    /// listing's by the spelling its read used, which may lead through a
    /// symlink, so a named path is matched by spelling
    /// ([`crate::paths::path_dedup_key`]) and by identity: the device and
    /// inode an `lstat` of it finds now (a `stat`, for the directory holding
    /// it), against those its last look found there or, through a final
    /// symlink, where it leads. A path that can no longer be
    /// looked at under a witness's spelling fails that witness anyway.
    pub fn hint<'a>(&self, paths: impl IntoIterator<Item = &'a Path>) {
        let paths: Vec<&Path> = paths.into_iter().collect();
        self.files.hint(paths.iter().copied());
        let named: Vec<PathBuf> = paths.iter().map(|path| lexically_normalize(path)).collect();
        if named.is_empty() {
            return;
        }
        let holding: Vec<PathBuf> = named
            .iter()
            .filter_map(|path| path.parent().map(Path::to_path_buf))
            .collect();
        let spellings = |paths: &[PathBuf]| -> std::collections::HashSet<String> {
            paths
                .iter()
                .map(|path| crate::paths::path_dedup_key(path))
                .collect()
        };
        let (named_spellings, holding_spellings) = (spellings(&named), spellings(&holding));
        let named_keys: std::collections::HashSet<&Path> =
            named_spellings.iter().map(Path::new).collect();
        // What a named path names, not following it: an event names what
        // changed, a symlink and not its target.
        let named_identities: std::collections::HashSet<(u64, u64)> = named
            .iter()
            .filter_map(|path| {
                self.count_stat();
                self.files.disk().lstat(path).ok()
            })
            .map(|lstat| (lstat.stamp.dev, lstat.stamp.ino))
            .collect();
        let holding_identities: std::collections::HashSet<(u64, u64)> = holding
            .iter()
            .filter_map(|path| {
                self.count_stat();
                self.files.disk().stat(path).ok()
            })
            .map(|stamp| (stamp.dev, stamp.ino))
            .collect();
        let hints = self.hints.get() + 1;
        self.hints.set(hints);
        for entry in self.entries.borrow_mut().iter_mut() {
            let lstat = entry.lstat.ok();
            let itself = lstat.map(|lstat| (lstat.stamp.dev, lstat.stamp.ino));
            let followed = match lstat {
                Some(Lstat {
                    kind: Kind::Link, ..
                }) => entry.followed,
                _ => lstat.map(|lstat| lstat.stamp),
            }
            .map(|stamp| (stamp.dev, stamp.ino));
            let key = crate::paths::path_dedup_key(&entry.path);
            // A path named, or below one: a directory moved into place moves
            // everything below it, which no other event may name. A path
            // that leads to a named one through a final symlink (a listing's
            // spelling) is matched by where it leads. Each of the path's
            // ancestors is looked up, so a batch of events costs the cached
            // paths' depth, not their count times the batch's.
            let below_named = Path::new(&key)
                .ancestors()
                .any(|ancestor| named_keys.contains(ancestor));
            if below_named
                || itself.is_some_and(|id| named_identities.contains(&id))
                || followed.is_some_and(|id| named_identities.contains(&id))
            {
                entry.hinted = hints;
            }
            if holding_spellings.contains(&key)
                || followed.is_some_and(|id| holding_identities.contains(&id))
            {
                entry.hinted_entries = hints;
            }
        }
    }

    /// Whether `check`'s read gets the answer recorded, now. Outside a
    /// generation, the query is asked.
    pub fn holds(&self, check: &Check) -> bool {
        let read = &check.shared.read;
        // A racy stamp speaks for the file only when it was taken; what it
        // saw is confirmed by the file's contents, when it says what they were.
        // The stamp of a file a whole-file read could not read is asked
        // again as that read: asked as a `stat`, it would succeed, and never
        // hold again with nothing changing. The read is what it rests on, so
        // whether the stamp was racy then or is now does not enter into it.
        if let Observation::Stamp(Ok(recorded)) = &read.observation
            && recorded.unreadable
        {
            let mut counts = self.counts.get();
            counts.opens += 1;
            self.counts.set(counts);
            let now = self
                .files
                .disk()
                .read_stamped(&read.path, &read.observation);
            return borzoi_msbuild::observed::same_unreadable(recorded, &now);
        }
        if let Observation::Stamp(Ok(recorded)) = &read.observation
            && recorded.racy
        {
            return self.racy_stamp_holds(check, recorded);
        }
        if let Observation::Text(recorded) = &read.observation {
            return self.files.text_answer(&read.path) == *recorded;
        }
        let (Some(generation), Some(now)) = (self.files.generation(), self.files.now()) else {
            return self.ask(read) == read.observation;
        };
        if self.witnessed(check, generation) {
            return true;
        }
        // Look, then ask: a change after the look moves a stamp or an
        // identity, so the next generation asks again.
        let witness = self.deciders(read, generation).map(|items| Witness {
            checker: self.id,
            wide: items.iter().any(|item| item.wide),
            items,
            born: generation,
            taken: now,
            hints: self.hints.get(),
        });
        let holds = self.ask(read) == read.observation;
        *check.shared.witness.borrow_mut() = witness.filter(|_| holds);
        holds
    }

    /// Whether the file a racy stamp `recorded` was taken of still holds the
    /// bytes the read that took it saw (git's rule for a racy index entry):
    /// never, when the stamp carries no digest of them; otherwise, by a
    /// stamp of the file confirmed so earlier (a `stat`), or by reading the
    /// file again (an open). A read that finds them, under a stamp no longer
    /// racy, leaves that stamp to confirm the next check by: a write after
    /// it moves it.
    fn racy_stamp_holds(&self, check: &Check, recorded: &FileStamp) -> bool {
        let Some(digest) = recorded.digest else {
            return false;
        };
        let path = &check.shared.read.path;
        if let Some(confirmed) = check.shared.confirmed.get() {
            self.count_stat();
            let now = self
                .files
                .disk()
                .answer(path, &check.shared.read.observation);
            if now == Observation::Stamp(Ok(confirmed)) {
                return true;
            }
            check.shared.confirmed.set(None);
        }
        let mut counts = self.counts.get();
        counts.opens += 1;
        self.counts.set(counts);
        match self.files.disk().racy_content(path, digest) {
            Some(now) => {
                if !now.racy {
                    check.shared.confirmed.set(Some(now));
                }
                true
            }
            None => false,
        }
    }

    /// List `dir` now, as a reader that will depend on the listing does,
    /// and return the read as a check (counted as a listing). Inside a
    /// generation the directory and the walk to it are looked at first (an
    /// `lstat` each, shared with every check that names the path this
    /// generation, and a `stat` of a symlink listed through), and when the
    /// listing is one they decide (a fact, and an answer: see the module
    /// docs) the check is born with them as its witness, so a later
    /// generation confirms it by them alone. A change after the look moves
    /// a stamp or an identity, so the witness is never newer than what the
    /// listing saw.
    pub fn list(&self, dir: &Path) -> Check {
        let query = Read {
            path: dir.to_path_buf(),
            observation: Observation::Listing(Ok(Vec::new())),
        };
        let looked = match (self.files.generation(), self.files.now()) {
            (Some(generation), Some(now)) => self
                .deciders(&query, generation)
                .map(|items| (items, generation, now)),
            _ => None,
        };
        let read = Read {
            observation: self.ask(&query),
            ..query
        };
        let witness = looked
            .filter(|_| matches!(read.observation, Observation::Listing(Ok(_))))
            .filter(|_| a_fact(&read.observation))
            .map(|(items, generation, taken)| Witness {
                checker: self.id,
                wide: items.iter().any(|item| item.wide),
                items,
                born: generation,
                taken,
                hints: self.hints.get(),
            });
        let check = self.check(&read);
        // A witness the check already carries confirms this read as well
        // as the one just taken would, so only a new one replaces it.
        if witness.is_some() {
            *check.shared.witness.borrow_mut() = witness;
        }
        check
    }

    /// Whether `check`'s witness, taken in an earlier generation, still holds:
    /// this checker took it, none of its stamps is racy, no watch event has
    /// named the path of one, or an entry of a directory whose entries one
    /// decides, since it was taken ([`Self::hint`]), and every item finds
    /// what it found. A wide witness that holds narrows (see the module
    /// docs).
    fn witnessed(&self, check: &Check, generation: u64) -> bool {
        let mut witness = check.shared.witness.borrow_mut();
        let Some(witness) = &mut *witness else {
            return false;
        };
        if witness.checker != self.id {
            return false;
        }
        let hinted = {
            let entries = self.entries.borrow();
            witness.items.iter().any(|item| {
                let entry = &entries[item.id];
                // What an identity or a symlink says is decided by the path
                // itself; a directory's stamp, by its entries too.
                match item.seen {
                    Seen::Identity(_)
                    | Seen::Entry(Lstat {
                        kind: Kind::Link, ..
                    }) => entry.hinted > witness.hints,
                    Seen::Entry(_) | Seen::Followed(_) => {
                        entry.hinted.max(entry.hinted_entries) > witness.hints
                    }
                }
            })
        };
        let holds = !hinted
            && !witness
                .items
                .iter()
                .filter_map(|item| item.seen.stamp())
                .any(|stamp| stamp.is_racy(witness.taken))
            && witness
                .items
                .iter()
                .all(|item| self.finds(item, generation));
        // The generation that took it finds its entries as the walk found
        // them, which says nothing of when the query was asked.
        let narrows = !matches!(check.shared.read.observation, Observation::Canonical(_))
            || self.files.disk().canonical_spells_as_asked();
        if holds && witness.wide && generation > witness.born && narrows {
            witness.items.retain(|item| !item.wide);
            witness.wide = false;
        }
        holds
    }

    /// Whether `item`'s path holds, in `generation`, what it saw.
    fn finds(&self, item: &Item, generation: u64) -> bool {
        match item.seen {
            Seen::Identity(seen) => matches!(
                self.lstat(item.id, generation),
                Ok(lstat @ Lstat { kind: Kind::Dir, .. }) if Identity::of(&lstat) == seen
            ),
            Seen::Entry(seen) => self.lstat(item.id, generation) == Ok(seen),
            Seen::Followed(seen) => self.followed(item.id, generation) == Some(seen),
        }
    }

    /// What decides `read`'s answer (see the module docs), for a read about
    /// to be asked, as `generation` sees it; `None` when nothing does, and
    /// the read is asked in every generation.
    fn deciders(&self, read: &Read, generation: u64) -> Option<Vec<Item>> {
        let path = &read.path;
        // A relative path is resolved from the working directory, and has
        // no witness. `lstat` follows a final symlink when the path ends
        // with a separator, so a path not spelt as its components has no
        // `LinkKind` witness; every other query resolves its whole path as
        // the walk does (a `..` from the directory reached).
        let spelt_as_components = lexically_normalize(path).as_os_str() == path.as_os_str();
        if !path.is_absolute()
            || (matches!(read.observation, Observation::LinkKind(_)) && !spelt_as_components)
            || !a_fact(&read.observation)
        {
            return None;
        }
        match &read.observation {
            // The directory's entries decide a listing, by its stamp; the
            // walk to it, entering it as any other, decides which directory
            // that is, by items spelt as where the path leads, so a watch
            // event above the directory distrusts them however the listing
            // spells it.
            Observation::Listing(Ok(_)) => {
                let mut items = self.resolution(path, true, true, generation)?;
                let id = self.entry_id(path);
                items.push(Item {
                    id,
                    seen: Seen::Followed(self.followed(id, generation)?),
                    wide: false,
                });
                Some(items)
            }
            Observation::Listing(Err(_)) | Observation::Kind(_) | Observation::Canonical(_) => {
                self.resolution(path, true, false, generation)
            }
            Observation::LinkKind(_) => self.resolution(path, false, false, generation),
            // A file's stamp, like its text, moves with no directory's
            // stamp moving.
            Observation::Text(_) | Observation::Stamp(_) | Observation::Prefix { .. } => None,
        }
    }

    /// The witness of resolving `path`, following every symlink (the final
    /// component's too, if `follow_last`) as the kernel resolves it: a
    /// link's target is taken component by component, so a separator it ends
    /// with is no different from none, and each `..` from the directory
    /// reached. Each directory is looked at before any name is looked up in
    /// it. With `enter_last`, the last directory is entered as every other
    /// is, held by its identity, and the walk meeting anything else there
    /// has no witness. `None` if `path` is relative, or the walk follows
    /// more symlinks than the kernel does or meets anything but a
    /// directory, a symlink, or the absence or final entry it stops at.
    fn resolution(
        &self,
        path: &Path,
        follow_last: bool,
        enter_last: bool,
        generation: u64,
    ) -> Option<Vec<Item>> {
        if !path.is_absolute() {
            return None;
        }
        let mut current = PathBuf::from("/");
        let mut here = self.entry_id(&current);
        let mut items: Vec<Item> = Vec::new();
        // Each item once, kept after narrowing if any step needs it then.
        let push = |items: &mut Vec<Item>, item: Item| match items
            .iter_mut()
            .find(|held| held.id == item.id && held.seen == item.seen)
        {
            Some(held) => held.wide &= item.wide,
            None => items.push(item),
        };
        let mut links = 0;
        // Segments still to resolve, last first, split on separators as the
        // kernel splits them (`Path::components` would drop a `.`, which
        // the kernel looks up). A path that is not UTF-8 has no witness.
        let mut rest: Vec<String> = Vec::new();
        let push_all = |rest: &mut Vec<String>, of: &Path| -> Option<()> {
            for segment in of.to_str()?.split('/').rev() {
                // An empty segment (a doubled or trailing separator) names
                // no entry.
                if !segment.is_empty() {
                    rest.push(segment.to_string());
                }
            }
            Some(())
        };
        push_all(&mut rest, path)?;
        while let Some(name) = rest.pop() {
            // The directory reached, looked at before the name is looked up
            // in it: its stamp holds whatever the lookup finds while the
            // witness is wide, and after, where the lookup decides the
            // answer.
            let Ok(
                directory @ Lstat {
                    kind: Kind::Dir, ..
                },
            ) = self.lstat(here, generation)
            else {
                return None;
            };
            let looked_up_in = move |wide: bool| Item {
                id: here,
                seen: Seen::Entry(directory),
                wide,
            };
            // The root is entered with no name looked up for it, so no step
            // holds its identity: it does here, for its mode and owners
            // decide whether a symlink in it is followed.
            if current == Path::new("/") {
                push(
                    &mut items,
                    Item {
                        id: here,
                        seen: Seen::Identity(Identity::of(&directory)),
                        wide: false,
                    },
                );
            }
            match name.as_str() {
                // Every segment, `.` and `..` included, is looked up in the
                // directory reached, which takes search permission there. A
                // `chmod` moves its stamp, which holds while the witness is
                // wide; after, an `lstat` of its `..`, which finds the
                // directory the walk returns to only with that permission.
                // (`Path` drops a trailing `.`, so a `.` is held the same
                // way.)
                "." | ".." => {
                    push(&mut items, looked_up_in(true));
                    let up = current.join("..");
                    let up_id = self.entry_id(&up);
                    let Ok(
                        up @ Lstat {
                            kind: Kind::Dir, ..
                        },
                    ) = self.lstat(up_id, generation)
                    else {
                        return None;
                    };
                    push(
                        &mut items,
                        Item {
                            id: up_id,
                            seen: Seen::Identity(Identity::of(&up)),
                            wide: false,
                        },
                    );
                    if name == ".." {
                        current.pop();
                        here = self.entry_id(&current);
                    }
                    continue;
                }
                _ => {}
            }
            let child = current.join(&name);
            let child_id = self.entry_id(&child);
            let last = rest.is_empty();
            match self.lstat(child_id, generation) {
                Ok(
                    entered @ Lstat {
                        kind: Kind::Dir, ..
                    },
                ) if !last || enter_last => {
                    push(&mut items, looked_up_in(true));
                    push(
                        &mut items,
                        Item {
                            id: child_id,
                            seen: Seen::Identity(Identity::of(&entered)),
                            wide: false,
                        },
                    );
                    current = child;
                    here = child_id;
                }
                Ok(
                    link @ Lstat {
                        kind: Kind::Link, ..
                    },
                ) if !last || follow_last => {
                    push(&mut items, looked_up_in(true));
                    push(
                        &mut items,
                        Item {
                            id: child_id,
                            seen: Seen::Entry(link),
                            wide: false,
                        },
                    );
                    links += 1;
                    if links > MAX_LINKS {
                        return None;
                    }
                    let target = self.target(child_id, generation)?;
                    if target.is_absolute() {
                        current = PathBuf::from("/");
                        here = self.entry_id(&current);
                    }
                    push_all(&mut rest, &target)?;
                }
                // What a listing lists is no directory: what it found was
                // there after the walk, which says nothing of it.
                Ok(_) | Err(Missing::Absent) if enter_last => return None,
                // The last name decides the answer by what its directory
                // holds.
                Ok(_) if last => {
                    push(&mut items, looked_up_in(false));
                    return Some(items);
                }
                // A file in the middle of the path: the query fails, as no
                // answer a witness keeps does.
                Ok(_) => return None,
                Err(Missing::Absent) => {
                    push(&mut items, looked_up_in(false));
                    return Some(items);
                }
                Err(Missing::Failed) => return None,
            }
        }
        Some(items)
    }

    /// `read`'s query asked now, counted.
    fn ask(&self, read: &Read) -> Observation {
        let mut counts = self.counts.get();
        match read.observation {
            Observation::Text(_) | Observation::Prefix { .. } => counts.opens += 1,
            Observation::Kind(_) | Observation::LinkKind(_) | Observation::Stamp(_) => {
                counts.stats += 1;
            }
            Observation::Listing(_) => counts.listings += 1,
            Observation::Canonical(_) => counts.canonicalizations += 1,
        }
        self.counts.set(counts);
        self.asked.set(self.asked.get() + 1);
        self.files.disk().answer(&read.path, &read.observation)
    }

    /// The index of `path` in [`Self::entries`], added unlooked-at if new.
    fn entry_id(&self, path: &Path) -> usize {
        let mut ids = self.entry_ids.borrow_mut();
        if let Some(&id) = ids.get(path.as_os_str()) {
            return id;
        }
        let mut entries = self.entries.borrow_mut();
        let id = entries.len();
        ids.insert(path.as_os_str().to_owned(), id);
        entries.push(Entry {
            path: path.to_path_buf(),
            lstat: Err(Missing::Failed),
            checked: 0,
            followed: None,
            followed_checked: 0,
            target: None,
            target_checked: 0,
            hinted: 0,
            hinted_entries: 0,
        });
        id
    }

    /// What an `lstat` in `generation` of the path `id` names finds, asked
    /// once per generation.
    fn lstat(&self, id: usize, generation: u64) -> Result<Lstat, Missing> {
        let mut entries = self.entries.borrow_mut();
        let entry = &mut entries[id];
        if entry.checked != generation {
            self.count_stat();
            entry.lstat = self
                .files
                .disk()
                .lstat(&entry.path)
                .map_err(|err| match err.kind() {
                    io::ErrorKind::NotFound => Missing::Absent,
                    _ => Missing::Failed,
                });
            entry.checked = generation;
        }
        entry.lstat
    }

    /// The stamp in `generation` of the path `id` names, following every
    /// symlink: its `lstat`'s, unless that found a symlink, which is then
    /// `stat`ed, once per generation. `None` when it has none.
    fn followed(&self, id: usize, generation: u64) -> Option<Stamp> {
        let lstat = self.lstat(id, generation).ok()?;
        if lstat.kind != Kind::Link {
            return Some(lstat.stamp);
        }
        let mut entries = self.entries.borrow_mut();
        let entry = &mut entries[id];
        if entry.followed_checked != generation {
            self.count_stat();
            entry.followed = self.files.disk().stat(&entry.path).ok();
            entry.followed_checked = generation;
        }
        entry.followed
    }

    /// The target of the symlink at the path `id` names, in `generation`,
    /// read once per generation, after the `lstat` that found it.
    fn target(&self, id: usize, generation: u64) -> Option<PathBuf> {
        let mut entries = self.entries.borrow_mut();
        let entry = &mut entries[id];
        if entry.target_checked != generation {
            self.count_stat();
            entry.target = self.files.disk().read_link(&entry.path).ok();
            entry.target_checked = generation;
        }
        entry.target.clone()
    }
}

#[cfg(test)]
mod tests;

#[cfg(all(test, unix))]
mod host_tests {
    use super::*;
    use crate::observed::host_fs;
    use proptest::prelude::*;

    /// Names in the generated trees.
    const NAMES: [&str; 4] = ["a", "b", "l", "m"];

    /// Symlink targets, relative to the tree's root or to the link: the
    /// spellings the kernel resolves in ways a component walk must follow.
    const TARGETS: [&str; 8] = [
        "a", "a/", "b/a", "../a", "./b", "a/../b", "ROOT/b/", "ROOT/a",
    ];

    #[derive(Clone, Debug)]
    enum Change {
        File(Vec<usize>),
        Dir(Vec<usize>),
        Link(Vec<usize>, usize),
        Remove(Vec<usize>),
        Rename(Vec<usize>, Vec<usize>),
        /// Take away, or give back, a directory's search permission.
        Search(Vec<usize>, bool),
        /// Exchange two entries by three renames.
        Swap(Vec<usize>, Vec<usize>),
        /// Replace a directory with a copy of it, less the second path: a
        /// directory moved into its place.
        Replace(Vec<usize>, Vec<usize>),
        /// Replace an entry with a symlink, by renaming one over it.
        Relink(Vec<usize>, usize),
    }

    fn rel(names: &[usize]) -> PathBuf {
        names.iter().map(|&i| NAMES[i]).collect()
    }

    /// Copy the tree at `from` to `to`, symlinks as symlinks, leaving out
    /// `without` and what is below it.
    fn copy_tree(from: &Path, to: &Path, without: &Path) -> io::Result<()> {
        std::fs::create_dir(to)?;
        for entry in host_fs::read_dir(from)? {
            let entry = entry?;
            let (source, copy) = (entry.path(), to.join(entry.file_name()));
            if source.starts_with(without) {
                continue;
            }
            let kind = entry.file_type()?;
            if kind.is_symlink() {
                std::os::unix::fs::symlink(host_fs::read_link(&source)?, &copy)?;
            } else if kind.is_dir() {
                copy_tree(&source, &copy, without)?;
            } else {
                std::fs::write(&copy, host_fs::read(&source)?)?;
            }
        }
        Ok(())
    }

    fn apply(root: &Path, change: &Change) {
        let at = |names: &[usize]| root.join(rel(names));
        // Where a change puts an entry for a moment: in no generated path.
        let aside = root.join(".aside");
        // Failures (a missing parent, an existing entry) leave the tree as
        // it was, which is a change like any other for the property.
        let _ = match change {
            Change::File(p) => std::fs::write(at(p), b"x"),
            Change::Dir(p) => std::fs::create_dir(at(p)),
            Change::Link(p, t) => {
                let target = TARGETS[*t].replace("ROOT", &root.display().to_string());
                std::os::unix::fs::symlink(target, at(p))
            }
            Change::Remove(p) => {
                let path = at(p);
                std::fs::remove_file(&path).or_else(|_| std::fs::remove_dir_all(&path))
            }
            Change::Rename(from, to) => std::fs::rename(at(from), at(to)),
            Change::Search(p, allowed) => {
                use std::os::unix::fs::PermissionsExt as _;
                let mode = if *allowed { 0o755 } else { 0o644 };
                std::fs::set_permissions(at(p), std::fs::Permissions::from_mode(mode))
            }
            Change::Swap(a, b) => std::fs::rename(at(a), &aside).and_then(|()| {
                let moved = std::fs::rename(at(b), at(a));
                std::fs::rename(&aside, at(b)).and(moved)
            }),
            Change::Replace(p, without) => {
                let copy = root.join(".copy");
                let replaced = copy_tree(&at(p), &copy, &at(without))
                    .and_then(|()| std::fs::rename(at(p), &aside))
                    .and_then(|()| std::fs::rename(&copy, at(p)));
                let _ = std::fs::remove_dir_all(&copy);
                let _ = std::fs::remove_dir_all(&aside);
                replaced
            }
            Change::Relink(p, t) => {
                let target = TARGETS[*t].replace("ROOT", &root.display().to_string());
                std::os::unix::fs::symlink(target, &aside)
                    .and_then(|()| std::fs::rename(&aside, at(p)))
                    .inspect_err(|_| {
                        let _ = std::fs::remove_file(&aside);
                    })
            }
        };
    }

    fn restore_search(dir: &Path) {
        use std::os::unix::fs::PermissionsExt as _;
        let _ = std::fs::set_permissions(dir, std::fs::Permissions::from_mode(0o755));
        if let Ok(entries) = host_fs::read_dir(dir) {
            for entry in entries.flatten() {
                if entry.file_type().is_ok_and(|kind| kind.is_dir()) {
                    restore_search(&entry.path());
                }
            }
        }
    }

    fn names() -> impl Strategy<Value = Vec<usize>> {
        prop::collection::vec(0..NAMES.len(), 1..3)
    }

    fn change() -> impl Strategy<Value = Change> {
        prop_oneof![
            names().prop_map(Change::File),
            names().prop_map(Change::Dir),
            (names(), 0..TARGETS.len()).prop_map(|(p, t)| Change::Link(p, t)),
            names().prop_map(Change::Remove),
            (names(), names()).prop_map(|(a, b)| Change::Rename(a, b)),
            (names(), any::<bool>()).prop_map(|(p, allowed)| Change::Search(p, allowed)),
            (names(), names()).prop_map(|(a, b)| Change::Swap(a, b)),
            (names(), names()).prop_map(|(p, without)| Change::Replace(p, without)),
            (names(), 0..TARGETS.len()).prop_map(|(p, t)| Change::Relink(p, t)),
        ]
    }

    /// A `..` is looked up in the directory it leaves, and a `.` in the
    /// directory it names, each needing search permission there: taking it
    /// away changes where the path leads without changing any directory the
    /// rest of the path names (Codex, twice). Each case is a path, or a link
    /// whose target is that path, to a directory through `gate`.
    #[test]
    fn a_directory_a_dot_is_looked_up_in_is_witnessed() {
        use std::os::unix::fs::PermissionsExt as _;
        for (spelling, through_link) in [
            ("gate/../target", true),
            ("gate/.", true),
            ("gate/.", false),
        ] {
            let tmp = tempfile::TempDir::new().unwrap();
            let root = host_fs::canonicalize(tmp.path()).unwrap();
            std::fs::create_dir(root.join("gate")).unwrap();
            std::fs::create_dir(root.join("target")).unwrap();
            let path = if through_link {
                std::os::unix::fs::symlink(spelling, root.join("through")).unwrap();
                root.join("through")
            } else {
                PathBuf::from(format!("{}/{spelling}", root.display()))
            };
            let check = Check::new(Read {
                observation: HostDisk.answer(&path, &Observation::Kind(Ok(EntryKind::Dir))),
                path,
            });
            let mut checker = ReadChecks::<HostDisk>::default();
            let mut at = Nanos(i128::MAX / 2);
            for _ in 0..2 {
                checker.begin_generation(at);
                assert!(checker.holds(&check));
                checker.end_generation();
                at = Nanos(at.0 + 1);
            }
            let gate = root.join("gate");
            std::fs::set_permissions(&gate, std::fs::Permissions::from_mode(0o644)).unwrap();
            checker.begin_generation(at);
            let truth = HostDisk.answer(&check.read().path, &check.read().observation);
            let holds = checker.holds(&check);
            checker.end_generation();
            std::fs::set_permissions(&gate, std::fs::Permissions::from_mode(0o755)).unwrap();
            if truth == check.read().observation {
                // The tests run with the permission to search any directory
                // (as root, say), so the change moved nothing to notice.
                eprintln!("{spelling}: search permission is not enforced here; skipped");
                continue;
            }
            assert!(!holds, "{spelling} (through a link: {through_link}) held");
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 24, ..ProptestConfig::default() })]

        /// On the host's file system, with symlinks of every spelling: a
        /// check that holds in a generation after a change gets the answer
        /// recorded. Each change is followed by a pause longer than a coarse
        /// filesystem tick, since the generations run on a clock ahead of the
        /// files (so that witnesses are used), which the racy rule would
        /// otherwise answer for.
        #[test]
        fn a_check_that_holds_is_right_on_the_host(
            setup in prop::collection::vec(change(), 0..12),
            rounds in prop::collection::vec(prop::collection::vec(change(), 0..3), 1..6),
        ) {
            let tmp = tempfile::TempDir::new().unwrap();
            let root = host_fs::canonicalize(tmp.path()).unwrap();
            for change in &setup {
                apply(&root, change);
            }
            let mut paths = vec![root.clone()];
            for a in NAMES {
                paths.push(root.join(a));
                // Spellings the kernel resolves otherwise than by components.
                paths.push(PathBuf::from(format!("{}/{a}/", root.display())));
                paths.push(root.join("l/..").join(a));
                paths.push(root.join("a/..").join(a));
                paths.push(PathBuf::from(format!("{}/{a}/.", root.display())));
                for b in NAMES {
                    paths.push(root.join(a).join(b));
                }
            }
            let queries = [
                Observation::Kind(Ok(EntryKind::File)),
                Observation::LinkKind(Ok(EntryKind::File)),
                Observation::Listing(Ok(Vec::new())),
                Observation::Canonical(Ok(PathBuf::new())),
            ];
            let checks: Vec<Check> = paths
                .iter()
                .flat_map(|path| {
                    queries.iter().map(move |query| {
                        Check::new(Read {
                            path: path.clone(),
                            observation: HostDisk.answer(path, query),
                        })
                    })
                })
                .collect();
            let mut checker = ReadChecks::<HostDisk>::default();
            let mut at = Nanos(i128::MAX / 2);
            for round in rounds.iter().chain([&Vec::new()]) {
                for change in round {
                    apply(&root, change);
                    std::thread::sleep(std::time::Duration::from_millis(15));
                }
                checker.begin_generation(at);
                for check in &checks {
                    if checker.holds(check) {
                        let truth = HostDisk.answer(&check.read().path, &check.read().observation);
                        prop_assert_eq!(&truth, &check.read().observation, "{:?}", check.read().path);
                    }
                }
                checker.end_generation();
                at = Nanos(at.0 + 1);
            }
            // Give every directory its search permission back, so the
            // temporary directory can be removed.
            restore_search(&root);
        }
    }

    /// On the host (#776): once its witness has narrowed, a read is asked
    /// nothing again when entries are made, removed and renamed in the
    /// directories its path only passes through, the temporary directory
    /// among them (as `$HOME` is in the server), whose ancestors other tests
    /// and processes change as they please. A change in the directory whose
    /// entries decide a read asks it again. Each path is read through
    /// symlinks too, relative and absolute.
    #[test]
    fn sibling_changes_above_a_read_ask_it_nothing_on_the_host() {
        let tmp = tempfile::TempDir::new().unwrap();
        let root = host_fs::canonicalize(tmp.path()).unwrap();
        std::fs::create_dir_all(root.join("a/b/c/d")).unwrap();
        std::fs::write(root.join("a/b/c/f"), b"x").unwrap();
        std::os::unix::fs::symlink("a/b", root.join("l")).unwrap();
        std::os::unix::fs::symlink("../a/b/c", root.join("a/m")).unwrap();
        std::os::unix::fs::symlink(root.join("a/b/c"), root.join("a/b/n")).unwrap();
        let deciding = root.join("a/b/c");
        let paths = [
            "a/b/c/f",
            "a/b/c/g",
            "a/b/c/d",
            "a/b/c/d/",
            "l/c/f",
            "a/m/f",
            "a/m/g",
            "a/b/n/f",
            "a/b/../b/c/f",
        ];
        let queries = [
            Observation::Kind(Ok(EntryKind::File)),
            Observation::LinkKind(Ok(EntryKind::File)),
            Observation::Canonical(Ok(PathBuf::new())),
        ];
        let mut checks: Vec<Check> = paths
            .iter()
            .flat_map(|rel| {
                let path = PathBuf::from(format!("{}/{rel}", root.display()));
                queries.iter().map(move |query| {
                    Check::new(Read {
                        observation: HostDisk.answer(&path, query),
                        path: path.clone(),
                    })
                })
            })
            .collect();
        for listed in ["a/b/c", "a/b/c/d", "l/c", "a/m"] {
            let path = root.join(listed);
            checks.push(Check::new(Read {
                observation: HostDisk.answer(&path, &Observation::Listing(Ok(Vec::new()))),
                path,
            }));
        }
        let mut checker = ReadChecks::<HostDisk>::default();
        let mut at = Nanos(i128::MAX / 2);
        let mut generation = |checker: &mut ReadChecks<HostDisk>| {
            checker.begin_generation(at);
            let asked = checker.asked();
            for check in &checks {
                if checker.holds(check) {
                    let truth = HostDisk.answer(&check.read().path, &check.read().observation);
                    assert_eq!(truth, check.read().observation, "{:?}", check.read().path);
                }
            }
            let asked = checker.asked() - asked;
            checker.end_generation();
            at = Nanos(at.0 + 1);
            asked
        };
        // A witness narrows in the first later generation that finds the
        // stamps it was born with, unless it is a canonicalisation's and the
        // host spells its answer as the disk does. Other tests and processes
        // make entries in the temporary directory's ancestors, which would
        // keep it wide, so their stamps are held still until it narrows;
        // their identities, which narrowed witnesses keep, are their own.
        let stays_wide = |check: &Check| {
            matches!(check.read().observation, Observation::Canonical(_))
                && !HostDisk.canonical_spells_as_asked()
        };
        {
            let _still = host_fs::hold_ancestors_still(&root);
            generation(&mut checker);
            generation(&mut checker);
        }
        assert!(
            checks
                .iter()
                .all(|check| check.wide() != Some(true) || stays_wide(check)),
            "a quiet generation left a witness wide"
        );
        // An `lstat` of a path ending in a separator, or spelt with a `..`,
        // has none.
        let unwitnessed = checks.iter().filter(|check| check.wide().is_none()).count();
        assert_eq!(unwitnessed, 2, "precondition");
        let wide = checks
            .iter()
            .filter(|check| check.wide() == Some(true))
            .count();
        for dir in [root.clone(), root.join("a"), root.join("a/b")] {
            std::fs::write(dir.join("s"), b"x").unwrap();
            std::fs::create_dir(dir.join("t")).unwrap();
            std::os::unix::fs::symlink("s", dir.join("u")).unwrap();
            std::fs::rename(dir.join("s"), dir.join("s2")).unwrap();
            std::fs::remove_dir(dir.join("t")).unwrap();
        }
        assert_eq!(
            generation(&mut checker),
            (unwitnessed + wide) as u64,
            "a sibling change asked a narrowed read again"
        );
        std::thread::sleep(std::time::Duration::from_millis(15));
        std::fs::write(deciding.join("s"), b"x").unwrap();
        assert!(
            generation(&mut checker) > 0,
            "a change in the deciding directory asked nothing"
        );
    }

    /// A path the kernel resolves differently from its components (a
    /// trailing separator follows a final symlink, `..` is taken from the
    /// directory reached) has no witness: it is asked in every generation.
    /// Here `link/` names the target directory through a symlink, and the
    /// target's deletion is noticed though the link's directory is unchanged.
    #[test]
    fn a_spelling_the_stamps_cannot_follow_is_asked_every_time() {
        let tmp = tempfile::TempDir::new().unwrap();
        let root = host_fs::canonicalize(tmp.path()).unwrap();
        std::fs::create_dir_all(root.join("elsewhere/target")).unwrap();
        std::fs::create_dir(root.join("here")).unwrap();
        std::os::unix::fs::symlink(root.join("elsewhere/target"), root.join("here/link")).unwrap();
        // A link whose target ends with a separator, to a link (Codex).
        std::os::unix::fs::symlink(format!("{}/here/link/", root.display()), root.join("chain"))
            .unwrap();
        let spellings = [
            PathBuf::from(format!("{}/here/link/", root.display())),
            root.join("here/link/../target"),
            root.join("chain"),
        ];
        let queries = [
            Observation::Kind(Ok(EntryKind::Dir)),
            // `lstat` of `link/` follows the link.
            Observation::LinkKind(Ok(EntryKind::Dir)),
        ];
        let checks: Vec<Check> = spellings
            .iter()
            .flat_map(|path| {
                queries.iter().map(move |query| {
                    Check::new(Read {
                        path: path.clone(),
                        observation: HostDisk.answer(path, query),
                    })
                })
            })
            .collect();
        let mut checker = ReadChecks::<HostDisk>::default();
        // Far enough ahead that no stamp is racy, so a witness would be used.
        let mut at = Nanos(i128::MAX / 2);
        for _ in 0..2 {
            checker.begin_generation(at);
            assert!(checks.iter().all(|check| checker.holds(check)));
            checker.end_generation();
            at = Nanos(at.0 + 1);
        }
        std::fs::remove_dir(root.join("elsewhere/target")).unwrap();
        checker.begin_generation(at);
        for check in &checks {
            // Every answer moved but `lstat` of `chain`, which is the link.
            let truth = HostDisk.answer(&check.read().path, &check.read().observation);
            assert_eq!(
                checker.holds(check),
                truth == check.read().observation,
                "{:?} {:?}",
                check.read().path,
                check.read().observation
            );
        }
        checker.end_generation();
    }
}
