//! The read-set soundness oracle (`docs/incremental-lsp-plan.md`, D7).
//!
//! [`sweep`] perturbs the files under a directory one at a time and, after
//! each perturbation, asks two things of an evaluation's read set. It
//! asserts the first and counts failures of the second:
//!
//! - **Sound**: if every answer in the read set still stands
//!   ([`ReadSet::first_stale`] is `None`), evaluating again gives the same
//!   `ParsedProject`, read set and counts included. A file-system query the
//!   evaluation made without recording it is how this fails: the
//!   perturbation moves the answer, the evaluation moves with it, and the
//!   read set does not notice.
//! - **Precise**: a perturbation that touches no path the read set names
//!   (nor an ancestor of one), and adds no entry to a directory it listed,
//!   leaves every answer standing. Deciding what a change touches means
//!   knowing which spellings the file system takes for one file (through a
//!   symlink, a `..` after one, a case-insensitive volume), and the check
//!   compares spellings lexically; so a failure here may be the check's,
//!   not the read set's, and is counted ([`Tally::imprecise`]) for a caller
//!   whose tree has one spelling per file to assert on. An imprecise read
//!   set costs a needless re-evaluation, never a wrong one.
//!
//! The perturbations are: every regular file rewritten (an MSBuild file with
//! one more property written, anything else with a byte appended), rewritten
//! at the same size (one character of its first text changed), and deleted;
//! a file created in every directory under `root` under every name in a
//! vocabulary (the implicit-import names, `global.json`, a new `.fs` and
//! `.props` name, and the name of every file in the tree and every path the
//! read set names), chosen without regard to what the read set recorded so
//! that a query it failed to record still meets a perturbation; every path
//! the read set recorded absent created, as an MSBuild file that writes a
//! property, and every directory it listed given a new `.fs` entry and a new
//! `.props` entry (which reach paths whose parent does not yet exist); and
//! every symlink under `root` deleted, retargeted to a path that does not
//! exist, and retargeted to every other symlink (so that it names whatever
//! that one names), with a dangling symlink's missing target created where it
//! lies under `root`. What a link names is the file system's to say: the
//! sweep resolves no target itself, and checks a target it creates against
//! the file system's resolution of the link. A caller adds
//! its own (installing a new SDK version, or retargeting a link to a tree of
//! its own, say) through `extra`.
//!
//! One such rule the sweep cannot make by itself, since `std` cannot make a
//! FIFO: every regular file replaced by a link to a FIFO the caller made
//! outside `root` ([`fifo_perturbations`]). Opening a FIFO to read it blocks
//! until a writer arrives, so a query that opened one would hang the sweep.
//! While a perturbation links to a FIFO, a watchdog opens it to write once
//! the computation has run a while, so such an open returns (reading nothing)
//! and the sweep panics, naming the perturbation, rather than hanging. The
//! open cannot return before the watchdog writes, so none goes unseen.
//!
//! This is test support: it writes into `root` and restores what it changed.

use std::path::{Path, PathBuf};

use std::collections::BTreeSet;
use std::ffi::OsString;

use super::host_fs;
use super::{Observation, ReadSet};
use crate::ParsedProject;

/// One change to the files under the swept root.
#[derive(Clone, Debug)]
pub enum Edit {
    /// Write the file, creating any missing parent directory.
    Write(PathBuf, Vec<u8>),
    /// Delete the file, the symlink (not what it leads to), or the directory
    /// and everything in it.
    Delete(PathBuf),
    /// Make the path a symlink whose target is the second path (relative to
    /// the link's directory, unless absolute), replacing what is there and
    /// creating any missing parent directory. Unix only: elsewhere it cannot
    /// be made, and the perturbation is skipped.
    Link(PathBuf, PathBuf),
    /// Create, as a file, what the dangling symlink `link` names, as the file
    /// system resolves it: in the directory the file system resolves the
    /// target's directory to, under the target's last component. Made only
    /// where that directory exists and lies under `within`, and where the
    /// file system then resolves the link to the file made; otherwise the
    /// perturbation is skipped.
    CreateTarget { link: PathBuf, within: PathBuf },
}

impl Edit {
    /// The path the edit names: for [`Edit::CreateTarget`], the link.
    pub fn path(&self) -> &Path {
        match self {
            Edit::Write(path, _)
            | Edit::Delete(path)
            | Edit::Link(path, _)
            | Edit::CreateTarget { link: path, .. } => path,
        }
    }
}

/// A perturbation: some edits, applied together, and what made it.
#[derive(Clone, Debug)]
pub struct Perturbation {
    pub why: Why,
    pub edits: Vec<Edit>,
}

/// Which rule made a perturbation, so a caller can see each rule fire.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Why {
    Rewrite,
    RewriteSameSize,
    CreateNew,
    Delete,
    CreateAbsent,
    GrowListing,
    /// A symlink deleted or retargeted, or a dangling one's target created.
    Relink,
    /// A regular file replaced by a link to a FIFO ([`fifo_perturbations`]).
    Fifo,
    /// The caller's own.
    Extra,
}

/// What a sweep saw, by rule.
#[derive(Clone, Debug, Default)]
pub struct Tally {
    /// Perturbations made.
    pub made: std::collections::BTreeMap<Why, usize>,
    /// Perturbations after which some answer moved.
    pub stale: std::collections::BTreeMap<Why, usize>,
    /// Perturbations after which the evaluation itself moved (for
    /// [`sweep_with`], its value, whatever its read set did).
    pub moved: std::collections::BTreeMap<Why, usize>,
    /// Perturbations that touched nothing the read set names.
    pub untouched: usize,
    /// Of those, the ones after which some answer moved anyway.
    pub imprecise: usize,
    /// Perturbations that could not be made.
    pub skipped: usize,
}

impl Tally {
    pub fn absorb(&mut self, other: &Tally) {
        for (why, n) in &other.made {
            *self.made.entry(*why).or_default() += n;
        }
        for (why, n) in &other.stale {
            *self.stale.entry(*why).or_default() += n;
        }
        for (why, n) in &other.moved {
            *self.moved.entry(*why).or_default() += n;
        }
        self.untouched += other.untouched;
        self.imprecise += other.imprecise;
        self.skipped += other.skipped;
    }

    pub fn moved(&self, why: Why) -> usize {
        self.moved.get(&why).copied().unwrap_or(0)
    }
}

/// The sweep. `evaluate` must evaluate the same source with the same
/// arguments each time (in particular, it must not re-read the entry project
/// from disk: that read is the caller's input, not the evaluation's).
///
/// Panics, naming the perturbation, on a soundness failure.
pub fn sweep(root: &Path, evaluate: &dyn Fn() -> ParsedProject, extra: &[Perturbation]) -> Tally {
    sweep_with(
        root,
        &|| {
            let parsed = evaluate();
            let reads = parsed.read_set.clone();
            (parsed, reads)
        },
        extra,
    )
}

/// [`sweep`] for any computation that records what it read: `compute`
/// returns its value, compared whole, and its read set. The value must be
/// the computation's whole output, read set and counts included where it
/// carries them, so that "the same" means the same.
///
/// Panics, naming the perturbation, on a soundness failure.
pub fn sweep_with<T: PartialEq + std::fmt::Debug>(
    root: &Path,
    compute: &dyn Fn() -> (T, ReadSet),
    extra: &[Perturbation],
) -> Tally {
    let base = compute();
    assert_eq!(
        base.1.first_stale(),
        None,
        "a read set is stale straight after its evaluation"
    );
    assert!(compute() == base, "the evaluation is not deterministic");
    let before = snapshot(root);
    let mut tally = Tally::default();
    for perturbation in perturbations(root, &base.1).iter().chain(extra) {
        let undo = match apply(&perturbation.edits) {
            Ok(undo) => undo,
            Err(partial) => {
                // An unwritable directory (a test of unreadable trees).
                partial.restore();
                tally.skipped += 1;
                continue;
            }
        };
        let fifos: Vec<&Path> = perturbation
            .edits
            .iter()
            .filter_map(|edit| match edit {
                Edit::Link(_, target) if is_fifo(target) => Some(target.as_path()),
                _ => None,
            })
            .collect();
        // The read set asked again is watched too: that asks every read's
        // query, a whole-file read of the FIFO among them.
        let watched = |patience| {
            let watches: Vec<FifoWatch> = fifos
                .iter()
                .map(|fifo| FifoWatch::arm(fifo, patience))
                .collect();
            let stale = base.1.first_stale().cloned();
            let after = compute();
            let rescued: Vec<bool> = watches.into_iter().map(FifoWatch::disarm).collect();
            (stale, after, rescued.contains(&true))
        };
        let (mut stale, mut after, rescued) = watched(FIFO_PATIENCE);
        if rescued {
            // Either an open waited on the FIFO, or the computation outlasted
            // the watch's patience: asked again with far more, an open still
            // waits, and nothing else should.
            let again;
            (stale, after, again) = watched(FIFO_PATIENCE * 10);
            assert!(
                !again,
                "{perturbation:?}: the evaluation, or the read set asked again, opened \
                 {fifos:?} to read it, which waits for a writer that here might never come \
                 (the sweep's watch had to write to it, twice)"
            );
        }
        let touched = undo.changed().any(|path| names(root, &base.1, path));
        undo.restore();
        *tally.made.entry(perturbation.why).or_default() += 1;
        if !touched {
            tally.untouched += 1;
            if stale.is_some() {
                tally.imprecise += 1;
            }
        }
        match stale {
            None => assert!(
                after == base,
                "{perturbation:?} left every answer in the read set standing, yet \
                 the evaluation moved:\n{}",
                difference(&base, &after)
            ),
            Some(_) => {
                *tally.stale.entry(perturbation.why).or_default() += 1;
                if after.0 != base.0 {
                    *tally.moved.entry(perturbation.why).or_default() += 1;
                }
            }
        }
        assert!(
            snapshot(root) == before,
            "restoring after {perturbation:?} left the tree changed"
        );
        assert_eq!(
            base.1.first_stale(),
            None,
            "restoring after {perturbation:?} left a read stale"
        );
    }
    tally
}

/// Make `edits` as a sweep makes a perturbation's, run `f` on the changed
/// tree, and restore it: `None` when an edit could not be made (and nothing
/// is left changed). For a test of the perturbations themselves.
pub fn with_edits<T>(edits: &[Edit], f: impl FnOnce() -> T) -> Option<T> {
    match apply(edits) {
        Ok(undo) => {
            let out = f();
            undo.restore();
            Some(out)
        }
        Err(partial) => {
            partial.restore();
            None
        }
    }
}

/// Everything under `root` a restore must put back: each entry's kind,
/// permissions, and bytes (a file's, if readable) or target (a symlink's).
fn snapshot(root: &Path) -> std::collections::BTreeMap<PathBuf, (String, Option<Vec<u8>>)> {
    let mut out = std::collections::BTreeMap::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let Ok(entries) = host_fs::read_dir(&dir) else {
            continue;
        };
        for path in entries.flatten().map(|e| e.path()) {
            let Ok(meta) = host_fs::symlink_metadata(&path) else {
                continue;
            };
            let kind = format!("{:?} {:?}", meta.file_type(), meta.permissions());
            let content = if meta.file_type().is_symlink() {
                host_fs::read_link(&path)
                    .ok()
                    .map(|t| t.into_os_string().into_encoded_bytes())
            } else if meta.is_file() {
                host_fs::read(&path).ok()
            } else {
                if meta.is_dir() {
                    stack.push(path.clone());
                }
                None
            };
            out.insert(path, (kind, content));
        }
    }
    out
}

/// The first field that differs, for a failure message.
fn difference(base: &impl std::fmt::Debug, after: &impl std::fmt::Debug) -> String {
    let base = format!("{base:#?}");
    let after = format!("{after:#?}");
    let line = base
        .lines()
        .zip(after.lines())
        .position(|(a, b)| a != b)
        .unwrap_or(0);
    let window = |text: &str| {
        text.lines()
            .skip(line.saturating_sub(3))
            .take(8)
            .collect::<Vec<_>>()
            .join("\n")
    };
    format!("before:\n{}\nafter:\n{}", window(&base), window(&after))
}

/// Whether the read set names `path`: a read of it, or a listing of its
/// directory.
/// Paths compare lexically, `..` collapsed, since the read set keeps the
/// spelling the evaluation used; a change to a directory on the way to a
/// read's path touches it too. A read whose path passes through a symlink
/// under `root` (itself included) depends on wherever the link leads, so it
/// counts as named by every change.
fn names(root: &Path, read_set: &ReadSet, path: &Path) -> bool {
    let path = lexical(path);
    read_set.reads().iter().any(|read| {
        let read_path = lexical(&read.path);
        read_path == path
            || read_path.starts_with(&path)
            || (matches!(read.observation, Observation::Listing(_))
                && path.parent() == Some(read_path.as_path()))
            || through_a_link(root, &read_path)
    })
}

/// Whether `path`, or a directory on the way to it below `root`, is a symlink.
fn through_a_link(root: &Path, path: &Path) -> bool {
    path.ancestors()
        .take_while(|dir| dir.starts_with(root) && *dir != root)
        .any(|dir| host_fs::symlink_metadata(dir).is_ok_and(|meta| meta.file_type().is_symlink()))
}

/// `path` with `.` dropped and each `..` collapsed into its parent.
fn lexical(path: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            std::path::Component::CurDir => {}
            std::path::Component::ParentDir => {
                out.pop();
            }
            other => out.push(other),
        }
    }
    out
}

/// The perturbations the module docs list, which [`sweep`] makes.
pub fn perturbations(root: &Path, read_set: &ReadSet) -> Vec<Perturbation> {
    let mut out = Vec::new();
    let mut files = Vec::new();
    let mut dirs = vec![root.to_path_buf()];
    let mut links = Vec::new();
    walk(root, &mut files, &mut dirs, &mut links);
    // Created without consulting the read set, so that a query the read set
    // failed to record still meets a perturbation that moves its answer.
    let mut names: BTreeSet<OsString> = [
        "Directory.Build.props",
        "Directory.Build.targets",
        "Directory.Packages.props",
        "global.json",
        "zz_perturbed.fs",
        "zz_perturbed.props",
    ]
    .into_iter()
    .map(OsString::from)
    .collect();
    let under_root = |path: &Path| path.starts_with(root) && path != root;
    names.extend(
        files
            .iter()
            .map(PathBuf::as_path)
            .chain(links.iter().map(PathBuf::as_path))
            .chain(
                read_set
                    .reads()
                    .iter()
                    .map(|r| r.path.as_path())
                    .filter(|p| under_root(p)),
            )
            .filter_map(|path| path.file_name().map(OsString::from)),
    );
    for dir in &dirs {
        for name in &names {
            let path = dir.join(name);
            if host_fs::symlink_metadata(&path).is_err() {
                out.push(Perturbation {
                    why: Why::CreateNew,
                    edits: vec![Edit::Write(path, PROPERTY_FILE.to_vec())],
                });
            }
        }
    }
    for file in files {
        let bytes = host_fs::read(&file).unwrap_or_default();
        out.push(Perturbation {
            why: Why::Rewrite,
            edits: vec![Edit::Write(file.clone(), rewritten(&file, &bytes))],
        });
        if let Some(same_size) = rewritten_same_size(&bytes) {
            out.push(Perturbation {
                why: Why::RewriteSameSize,
                edits: vec![Edit::Write(file.clone(), same_size)],
            });
        }
        out.push(Perturbation {
            why: Why::Delete,
            edits: vec![Edit::Delete(file)],
        });
    }
    // A read set may name paths outside the root (`../outside/…`, or through a
    // symlink); the sweep changes only the paths that lie, lexically and
    // physically, under it, and spells each lexically.
    let inside = |path: &Path| {
        let path = lexical(path);
        (under_root(&path) && !through_a_link(root, &path)).then_some(path)
    };
    // Every link is deleted and dangled, whatever its target. It is
    // retargeted to every other link, so that it names whatever that link
    // names, and to what the file system says that link names now (which
    // differs where that link's own target passes through this one). A link
    // the file system finds dangling has its missing target created
    // ([`Edit::CreateTarget`]). No target is resolved here.
    let named: Vec<(&PathBuf, Option<PathBuf>)> = links
        .iter()
        .map(|link| (link, host_fs::canonicalize(link).ok()))
        .collect();
    for link in &links {
        let mut relinks = vec![
            Edit::Delete(link.clone()),
            Edit::Link(link.clone(), PathBuf::from("zz_perturbed_missing_target")),
        ];
        for (other, names) in named.iter().filter(|(other, _)| *other != link) {
            relinks.push(Edit::Link(link.clone(), (*other).clone()));
            if let Some(names) = names {
                relinks.push(Edit::Link(link.clone(), names.clone()));
            }
        }
        if host_fs::metadata(link).is_err() {
            relinks.push(Edit::CreateTarget {
                link: link.clone(),
                within: root.to_path_buf(),
            });
        }
        out.extend(relinks.into_iter().map(|edit| Perturbation {
            why: Why::Relink,
            edits: vec![edit],
        }));
    }
    for (read, path) in read_set
        .reads()
        .iter()
        .filter_map(|read| inside(&read.path).map(|path| (read, path)))
    {
        let absent = match &read.observation {
            Observation::Text(Err(failure))
            | Observation::Kind(Err(failure))
            | Observation::LinkKind(Err(failure))
            | Observation::Canonical(Err(failure))
            | Observation::Stamp(Err(failure)) => failure.is_absent(),
            _ => false,
        };
        // A dangling symlink fails a following query as absent, but its
        // entry is there: it is not a path to create a file at.
        if absent && host_fs::symlink_metadata(&path).is_err() {
            out.push(Perturbation {
                why: Why::CreateAbsent,
                edits: vec![Edit::Write(path.clone(), PROPERTY_FILE.to_vec())],
            });
        }
        if let Observation::Listing(Ok(_)) = &read.observation {
            for name in ["zz_perturbed.fs", "zz_perturbed.props"] {
                out.push(Perturbation {
                    why: Why::GrowListing,
                    edits: vec![Edit::Write(path.join(name), PROPERTY_FILE.to_vec())],
                });
            }
        }
    }
    out
}

/// Every regular file under `root` replaced by a link to `fifo`, a FIFO the
/// caller made outside `root` (`std` cannot make one): perturbations for a
/// sweep's `extra`, under which the sweep holds every query to not opening
/// the FIFO (see the module docs). Empty off Unix, where a FIFO is no entry
/// of the file system.
pub fn fifo_perturbations(root: &Path, fifo: &Path) -> Vec<Perturbation> {
    assert!(
        is_fifo(fifo) && fifo.is_absolute() && !fifo.starts_with(root),
        "{} is no FIFO by an absolute path outside {}",
        fifo.display(),
        root.display()
    );
    let mut files = Vec::new();
    walk(root, &mut files, &mut Vec::new(), &mut Vec::new());
    files
        .into_iter()
        .map(|file| Perturbation {
            why: Why::Fifo,
            edits: vec![Edit::Link(file, fifo.to_path_buf())],
        })
        .collect()
}

/// Whether `path` names a FIFO, following symlinks.
#[cfg(unix)]
fn is_fifo(path: &Path) -> bool {
    use std::os::unix::fs::FileTypeExt as _;
    host_fs::metadata(path).is_ok_and(|meta| meta.file_type().is_fifo())
}

#[cfg(not(unix))]
fn is_fifo(_path: &Path) -> bool {
    false
}

/// How long a computation under a [`FifoWatch`] may run before the watch
/// opens the FIFO to write, which a query waiting in its open of the FIFO
/// needs to go on.
const FIFO_PATIENCE: std::time::Duration = std::time::Duration::from_secs(1);

/// A watchdog for a FIFO while a perturbation links to it. Opening a FIFO to
/// read it waits until a writer opens it too, and nothing else ever will, so
/// a query that opens it waits for good. Once the computation has run for the
/// watch's patience, and again each patience after, the watchdog opens the
/// FIFO to write, which lets such a query go on, reading nothing.
///
/// So any such open makes the watchdog write ([`FifoWatch::disarm`]), however
/// the threads are scheduled: the open cannot return before it does. A
/// computation that merely outlasts the patience makes it write too; the
/// sweep tells the two apart by asking again with ten times the patience.
struct FifoWatch {
    fifo: PathBuf,
    state: std::sync::Arc<(std::sync::Mutex<WatchState>, std::sync::Condvar)>,
    watchdog: Option<std::thread::JoinHandle<()>>,
}

#[derive(Default)]
struct WatchState {
    /// The computation has returned.
    done: bool,
    /// The watchdog has opened, or is opening, the FIFO to write.
    writing: bool,
}

impl FifoWatch {
    fn arm(fifo: &Path, patience: std::time::Duration) -> Self {
        let state = std::sync::Arc::new((
            std::sync::Mutex::new(WatchState::default()),
            std::sync::Condvar::new(),
        ));
        let watchdog = {
            let (fifo, state) = (fifo.to_path_buf(), state.clone());
            std::thread::spawn(move || {
                let (lock, done) = &*state;
                loop {
                    let guard = lock.lock().unwrap_or_else(|e| e.into_inner());
                    let (mut guard, _) = done
                        .wait_timeout_while(guard, patience, |state| !state.done)
                        .unwrap_or_else(|e| e.into_inner());
                    if guard.done {
                        return;
                    }
                    guard.writing = true;
                    drop(guard);
                    // Returns once a reader opens the FIFO: a query waiting
                    // in its open, or `disarm`'s own.
                    if host_fs::open_for_writing(&fifo).is_err() {
                        return;
                    }
                }
            })
        };
        FifoWatch {
            fifo: fifo.to_path_buf(),
            state,
            watchdog: Some(watchdog),
        }
    }

    /// Whether the watchdog opened the FIFO to write, once the computation
    /// had returned; the watchdog is stopped.
    fn disarm(mut self) -> bool {
        self.stop()
    }

    /// Stop the watchdog, and say whether it opened the FIFO to write. The
    /// state is read and `done` set under the lock the watchdog decides
    /// under, so a watchdog that had not begun to write never will.
    ///
    /// One that had may still be waiting in its open, with no reader left:
    /// the FIFO is opened to read and write, which waits for no peer (on
    /// Linux and macOS), and held until the watchdog has returned. It is held
    /// with no child being launched, since a child between its fork and its
    /// `exec` holds a copy of it: a writer that an open of this FIFO under the
    /// next watch could meet without that watchdog ever writing.
    fn stop(&mut self) -> bool {
        let Some(watchdog) = self.watchdog.take() else {
            return false;
        };
        let (lock, done) = &*self.state;
        let writing = {
            let mut state = lock.lock().unwrap_or_else(|e| e.into_inner());
            state.done = true;
            state.writing
        };
        done.notify_all();
        if !writing {
            let _ = watchdog.join();
            return false;
        }
        // Nothing in here panics, which would poison the spawn lock.
        let woken = borzoi_spawn::without_spawns(|| {
            let wake = host_fs::open_to_read_and_write(&self.fifo)?;
            let _ = watchdog.join();
            drop(wake);
            Ok::<(), std::io::Error>(())
        });
        if let Err(e) = woken {
            panic!(
                "open the FIFO {} to read and write: {e}",
                self.fifo.display()
            );
        }
        true
    }
}

impl Drop for FifoWatch {
    fn drop(&mut self) {
        self.stop();
    }
}

/// An MSBuild file writing one property.
const PROPERTY_FILE: &[u8] =
    b"<Project><PropertyGroup><Perturbed>yes</Perturbed></PropertyGroup></Project>\n";

/// `bytes`, with one more property written if it is an MSBuild file the
/// evaluation could import, and a byte appended otherwise.
fn rewritten(path: &Path, bytes: &[u8]) -> Vec<u8> {
    let msbuild = matches!(
        path.extension().and_then(|e| e.to_str()),
        Some("props" | "targets" | "fsproj" | "csproj" | "proj")
    );
    let text = String::from_utf8_lossy(bytes);
    match text.rfind("</Project>") {
        Some(end) if msbuild => {
            let mut out = text[..end].to_string();
            out.push_str("<PropertyGroup><Perturbed>yes</Perturbed></PropertyGroup>");
            out.push_str(&text[end..]);
            out.into_bytes()
        }
        _ => {
            let mut out = bytes.to_vec();
            out.push(b'\n');
            out
        }
    }
}

/// `bytes` with the first character of its first non-blank text node changed
/// (`a` to `b`, anything else to `a`), so the file keeps its size: a text
/// digest that hashed only the length would miss it.
fn rewritten_same_size(bytes: &[u8]) -> Option<Vec<u8>> {
    let mut inside_text = false;
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'>' => inside_text = true,
            b'<' => inside_text = false,
            b if inside_text && b.is_ascii_alphanumeric() => {
                let mut out = bytes.to_vec();
                out[i] = if b == b'a' { b'b' } else { b'a' };
                return Some(out);
            }
            _ => {}
        }
    }
    None
}

/// Every regular file, directory and symlink under `dir`, not following
/// symlinks.
fn walk(dir: &Path, files: &mut Vec<PathBuf>, dirs: &mut Vec<PathBuf>, links: &mut Vec<PathBuf>) {
    let Ok(entries) = host_fs::read_dir(dir) else {
        return;
    };
    let mut entries: Vec<_> = entries.flatten().map(|e| e.path()).collect();
    entries.sort();
    for path in entries {
        match host_fs::symlink_metadata(&path) {
            Ok(meta) if meta.is_dir() => {
                dirs.push(path.clone());
                walk(&path, files, dirs, links);
            }
            Ok(meta) if meta.is_file() => files.push(path),
            Ok(meta) if meta.file_type().is_symlink() => links.push(path),
            _ => {}
        }
    }
}

/// What a path held before a perturbation.
enum Prior {
    Absent {
        /// The topmost directory the perturbation had to create, if any.
        created: Option<PathBuf>,
    },
    /// Its bytes and permissions.
    File(Vec<u8>, std::fs::Permissions),
    Dir(PathBuf),
    /// A symlink, with its target.
    Link(PathBuf),
}

struct Undo {
    priors: Vec<(PathBuf, Prior)>,
}

/// Make the edits; `Err` holds what to undo when one could not be made.
fn apply(edits: &[Edit]) -> Result<Undo, Undo> {
    let mut priors = Vec::new();
    for edit in edits {
        if let Edit::CreateTarget { link, within } = edit {
            match create_target(link, within, 0) {
                Some(file) => priors.push((file, Prior::Absent { created: None })),
                None => return Err(Undo { priors }),
            }
            continue;
        }
        let path = edit.path();
        let prior = match host_fs::symlink_metadata(path) {
            Ok(meta) if meta.is_file() => match host_fs::read(path) {
                Ok(bytes) => Prior::File(bytes, meta.permissions()),
                // An unreadable file (a test of unreadable trees) cannot be
                // put back as it was, so it is not perturbed.
                Err(_) => return Err(Undo { priors }),
            },
            Ok(meta) if meta.is_dir() => {
                let aside = path.with_extension("perturbation-aside");
                std::fs::rename(path, &aside).expect("move the directory aside");
                Prior::Dir(aside)
            }
            Ok(meta) if meta.file_type().is_symlink() && cfg!(unix) => {
                let target = host_fs::read_link(path).expect("read the symlink's target");
                // Writing through the link would change what it leads to,
                // which may be shared, or outside the root: every edit
                // replaces the link itself.
                std::fs::remove_file(path).expect("remove the symlink");
                Prior::Link(target)
            }
            // A socket, a symlink where none can be made again: not something
            // the sweep perturbs.
            Ok(_) => return Err(Undo { priors }),
            Err(_) => Prior::Absent {
                created: topmost_missing_ancestor(path),
            },
        };
        let made = match edit {
            Edit::Write(path, bytes) => path
                .parent()
                .map_or(Ok(()), std::fs::create_dir_all)
                .and_then(|()| std::fs::write(path, bytes)),
            Edit::Delete(path) => match prior {
                Prior::File(..) => std::fs::remove_file(path),
                _ => Ok(()),
            },
            Edit::Link(path, target) => match prior {
                Prior::File(..) => std::fs::remove_file(path),
                _ => Ok(()),
            }
            .and_then(|()| path.parent().map_or(Ok(()), std::fs::create_dir_all))
            .and_then(|()| symlink(target, path)),
            Edit::CreateTarget { .. } => unreachable!("made above, without a prior of the link"),
        };
        priors.push((path.to_path_buf(), prior));
        if made.is_err() {
            return Err(Undo { priors });
        }
    }
    Ok(Undo { priors })
}

impl Undo {
    /// Every path whose state the edits changed: each edited path, the
    /// directories created for it, and the sibling a directory was moved
    /// aside to.
    fn changed(&self) -> impl Iterator<Item = &Path> {
        self.priors.iter().flat_map(|(path, prior)| {
            let mut changed = vec![path.as_path()];
            match prior {
                Prior::Absent {
                    created: Some(created),
                } => changed.extend(
                    path.ancestors()
                        .skip(1)
                        .take_while(|dir| dir.starts_with(created)),
                ),
                Prior::Dir(aside) => changed.push(aside.as_path()),
                _ => {}
            }
            changed
        })
    }

    fn restore(self) {
        for (path, prior) in self.priors.into_iter().rev() {
            if let Ok(meta) = host_fs::symlink_metadata(&path) {
                if meta.is_dir() {
                    std::fs::remove_dir_all(&path).expect("remove");
                } else {
                    std::fs::remove_file(&path).expect("remove");
                }
            }
            match prior {
                Prior::Absent { created } => {
                    if let Some(created) = created {
                        std::fs::remove_dir_all(created).expect("remove created directories");
                    }
                }
                Prior::File(bytes, permissions) => {
                    std::fs::write(&path, bytes).expect("restore");
                    std::fs::set_permissions(&path, permissions).expect("restore permissions");
                }
                Prior::Dir(aside) => std::fs::rename(aside, &path).expect("restore"),
                Prior::Link(target) => symlink(&target, &path).expect("restore the symlink"),
            }
        }
    }
}

/// [`Edit::CreateTarget`]: the file made, or `None` (with nothing made) where
/// it cannot be. Where the target's last component is itself a dangling
/// link, its target is created in turn, `depth` bounding a cycle as the file
/// system's own limit does.
fn create_target(link: &Path, within: &Path, depth: usize) -> Option<PathBuf> {
    if depth > 32 || host_fs::metadata(link).is_ok() {
        return None;
    }
    let joined = link.parent()?.join(host_fs::read_link(link).ok()?);
    let std::path::Component::Normal(name) = joined.components().next_back()? else {
        return None;
    };
    let dir = host_fs::canonicalize(joined.parent()?).ok()?;
    if !dir.starts_with(host_fs::canonicalize(within).ok()?) {
        return None;
    }
    let file = dir.join(name);
    match host_fs::symlink_metadata(&file) {
        Ok(meta) if meta.file_type().is_symlink() => {
            return create_target(&file, within, depth + 1);
        }
        Ok(_) => return None,
        Err(_) => {}
    }
    std::fs::write(&file, PROPERTY_FILE).ok()?;
    // The file system is the judge of what the link names.
    if host_fs::canonicalize(link).ok().as_deref() != Some(file.as_path()) {
        std::fs::remove_file(&file).expect("remove a target the link does not name");
        return None;
    }
    Some(file)
}

/// Make `link` a symlink to `target`.
#[cfg(unix)]
fn symlink(target: &Path, link: &Path) -> std::io::Result<()> {
    std::os::unix::fs::symlink(target, link)
}

#[cfg(not(unix))]
fn symlink(_target: &Path, _link: &Path) -> std::io::Result<()> {
    Err(std::io::Error::new(
        std::io::ErrorKind::Unsupported,
        "the sweep makes symlinks on Unix only",
    ))
}

/// The topmost ancestor of `path` (not `path` itself) that does not exist.
fn topmost_missing_ancestor(path: &Path) -> Option<PathBuf> {
    let mut missing = None;
    let mut cursor = path.parent();
    while let Some(dir) = cursor {
        if host_fs::symlink_metadata(dir).is_ok() {
            break;
        }
        missing = Some(dir.to_path_buf());
        cursor = dir.parent();
    }
    missing
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use crate::observed::{Observer, read_to_string};

    /// The FIFO rule's controls, over a tree of one file: a computation
    /// that reads it only through [`read_to_string`] passes the sweep, and
    /// one that also opens it (and looks at the open file, as a reader that
    /// checks what it opened before reading would) fails it, rather than
    /// hanging in that open, which waits for a writer.
    #[test]
    fn a_computation_that_opens_the_fifo_fails_the_sweep() {
        let tmp = tempfile::TempDir::new().unwrap();
        let root = host_fs::canonicalize(tmp.path()).unwrap();
        let file = root.join("a.props");
        std::fs::write(&file, "<Project />").unwrap();
        let fifo = crate::with_imports_tests::Fifo::new().unwrap();
        let extra = fifo_perturbations(&root, &fifo.path);
        assert_eq!(extra.len(), 1);
        let sweep_opening = |opens: bool| {
            let compute = || {
                let observer = Observer::new();
                let _ = read_to_string(&observer, &file);
                if opens {
                    let _ = host_fs::open_for_reading(&file).and_then(|open| open.metadata());
                }
                ((), observer.finish().0)
            };
            sweep_with(&root, &compute, &extra)
        };
        let tally = sweep_opening(false);
        assert_eq!(tally.made.get(&Why::Fifo), Some(&1), "{tally:?}");
        let failed =
            borzoi_oracle_harness::panic_silence::catch_unwind_silent(|| sweep_opening(true));
        assert!(failed.is_err(), "a computation that opened the FIFO passed");
        let panic =
            borzoi_oracle_harness::panic_silence::take_silenced_panic().expect("the sweep's panic");
        assert!(
            panic.message.contains("which waits for a writer"),
            "{}",
            panic.message
        );
    }
}
