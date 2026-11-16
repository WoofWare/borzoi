//! Entries a resolver's existence probe can meet at a path besides a regular
//! file: the shapes on which `stat` (Rust's `Path::is_file`), CLR
//! `File.Exists`, `Directory.Exists` and hostfxr's native probe part. The
//! differentials over the SDK resolvers' probes put one of these at a probed
//! path and hold our answer to the real resolver's.
//!
//! Unix only: every shape but [`Odd::Dir`] is a symlink or a special file.

use std::path::{Path, PathBuf};

/// A non-regular entry, or a link to a regular one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Odd {
    /// A symlink whose target is missing: `stat` fails, `lstat` succeeds.
    Dangling,
    /// A symlink to itself: `stat` fails with `ELOOP`, `lstat` succeeds.
    Loop,
    /// A directory.
    Dir,
    /// A symlink to a directory.
    DirLink,
    /// A symlink to a regular file holding the entry's usual content.
    FileLink,
    /// A Unix domain socket: `stat` succeeds, and `open` fails (`ENXIO`).
    Socket,
    /// A named pipe: `stat` succeeds, and `open` for reading blocks until a
    /// writer arrives, so it belongs only at a path no reader opens.
    Fifo,
}

impl Odd {
    pub const ALL: &[Odd] = &[
        Odd::Dangling,
        Odd::Loop,
        Odd::Dir,
        Odd::DirLink,
        Odd::FileLink,
        Odd::Socket,
        Odd::Fifo,
    ];

    /// Every shape but [`Odd::Fifo`]: the shapes that may sit where the
    /// real resolver opens what it finds.
    pub const OPENABLE: &[Odd] = &[
        Odd::Dangling,
        Odd::Loop,
        Odd::Dir,
        Odd::DirLink,
        Odd::FileLink,
        Odd::Socket,
    ];

    /// `File.Exists` of the entry: something is there that `stat` (failing
    /// that, `lstat`) does not call a directory.
    pub fn file_exists_to_dotnet(self) -> bool {
        !matches!(self, Odd::Dir | Odd::DirLink)
    }

    /// `Directory.Exists` of the entry: `stat` calls it a directory.
    pub fn directory_exists_to_dotnet(self) -> bool {
        matches!(self, Odd::Dir | Odd::DirLink)
    }

    /// Whether a read of the entry yields its usual content.
    pub fn reads_as_file(self) -> bool {
        self == Odd::FileLink
    }
}

/// Put `odd` at `path`, replacing whatever is there. A link's target, and
/// the file a [`Odd::FileLink`] reaches (holding `content`), are made under
/// `aside`, a directory outside the tree being probed, so nothing they add is
/// enumerated with it. A socket is bound under `aside` and renamed into place,
/// since a path in `sun_path` is limited to about a hundred bytes; `aside`
/// must be short enough for that.
pub fn place(odd: Odd, path: &Path, content: &str, aside: &Path) {
    use std::os::unix::fs::symlink;
    std::fs::create_dir_all(path.parent().expect("a probed path has a parent")).unwrap();
    remove(path);
    std::fs::create_dir_all(aside).unwrap();
    let fresh = fresh_name(aside);
    match odd {
        Odd::Dangling => symlink(aside.join("missing"), path).unwrap(),
        Odd::Loop => symlink(path, path).unwrap(),
        Odd::Dir => std::fs::create_dir(path).unwrap(),
        Odd::DirLink => {
            std::fs::create_dir(&fresh).unwrap();
            symlink(&fresh, path).unwrap();
        }
        Odd::FileLink => {
            std::fs::write(&fresh, content).unwrap();
            symlink(&fresh, path).unwrap();
        }
        Odd::Socket => {
            let listener = std::os::unix::net::UnixListener::bind(&fresh)
                .unwrap_or_else(|e| panic!("bind a socket at {}: {e}", fresh.display()));
            drop(listener);
            std::fs::rename(&fresh, path).unwrap();
        }
        Odd::Fifo => {
            let mut cmd = std::process::Command::new("mkfifo");
            cmd.arg(path);
            borzoi_oracle_harness::BoundedCommand::new(cmd)
                .timeout(std::time::Duration::from_secs(30))
                .run_ok(format_args!("mkfifo {}", path.display()));
        }
    }
}

/// Remove whatever entry is at `path`, following no link.
fn remove(path: &Path) {
    match borzoi_msbuild::observed::host_fs::symlink_metadata(path) {
        Ok(meta) if meta.is_dir() => std::fs::remove_dir_all(path).unwrap(),
        Ok(_) => std::fs::remove_file(path).unwrap(),
        Err(_) => {}
    }
}

/// A name under `aside` nothing has used yet.
fn fresh_name(aside: &Path) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    aside.join(format!("o{}", NEXT.fetch_add(1, Ordering::Relaxed)))
}
