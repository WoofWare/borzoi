//! The one way the crate reads a file whole: [`read`] opens a path only when
//! it names a regular file.
//!
//! Opening a FIFO to read it waits until a writer opens it too, which may be
//! never, and a device such as `/dev/zero` reads without end. NuGet's own
//! reads block on a FIFO as well, so there is no restore answer to be exact
//! with; a reader here declines instead, as it does for a file it cannot
//! read. The crate's `clippy.toml` bans the `std` calls that open a file
//! everywhere but here.

use std::io::{ErrorKind, Read as _};
use std::path::Path;

/// The bytes of the file at `path` ([`std::fs::read`]), when `path` names a
/// regular file, following symlinks.
///
/// Anything else (a FIFO, a socket, a device, a directory) fails, unopened,
/// as [`ErrorKind::InvalidInput`]. A path that cannot be `stat`ed fails as its
/// open would: absent, a loop of links, a component that is no directory or
/// cannot be searched.
///
/// The check is a `stat` of the path before the open, so a regular file
/// replaced by a FIFO between the two still blocks the open: `std` offers no
/// portable way to open without blocking (`O_NONBLOCK`), and the crate takes
/// no dependency for one. The open file is checked again (`fstat`), so
/// whatever was swapped in is never read.
#[allow(clippy::disallowed_methods)]
pub(crate) fn read(path: &Path) -> std::io::Result<Vec<u8>> {
    let not_regular = || std::io::Error::new(ErrorKind::InvalidInput, "not a regular file");
    if !std::fs::metadata(path)?.is_file() {
        return Err(not_regular());
    }
    let mut file = std::fs::File::open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file() {
        return Err(not_regular());
    }
    // Reserved fallibly, as `std::fs::read` does: a file too large to hold
    // fails the read rather than aborting the process.
    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(usize::try_from(meta.len()).unwrap_or(0))
        .map_err(|e| std::io::Error::new(ErrorKind::OutOfMemory, e))?;
    file.read_to_end(&mut bytes)?;
    Ok(bytes)
}

/// [`read`], as UTF-8 ([`std::fs::read_to_string`]): a file that is not fails
/// as [`ErrorKind::InvalidData`].
pub(crate) fn read_to_string(path: &Path) -> std::io::Result<String> {
    String::from_utf8(read(path)?).map_err(|_| {
        std::io::Error::new(ErrorKind::InvalidData, "stream did not contain valid UTF-8")
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use std::collections::HashSet;

    /// Make a FIFO at `path`, which `std` cannot.
    pub(crate) fn make_fifo(path: &Path) {
        let mut mkfifo = std::process::Command::new("mkfifo");
        mkfifo.arg(path);
        borzoi_oracle_harness::BoundedCommand::new(mkfifo)
            .timeout(std::time::Duration::from_secs(30))
            .run_ok(format_args!("mkfifo {}", path.display()));
    }

    /// `f`'s result, computed on a thread of its own, or a panic naming
    /// `what` when none comes within two minutes: for a test of a read that
    /// would block for good (a FIFO's open), which then fails rather than
    /// hangs.
    pub(crate) fn within_deadline<T: Send + 'static>(
        what: &str,
        f: impl FnOnce() -> T + Send + 'static,
    ) -> T {
        let (sender, receiver) = std::sync::mpsc::channel();
        std::thread::spawn(move || {
            let _ = sender.send(f());
        });
        match receiver.recv_timeout(std::time::Duration::from_secs(120)) {
            Ok(out) => out,
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                panic!("{what} did not return within two minutes: some read blocked")
            }
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => panic!("{what} panicked"),
        }
    }

    /// A FIFO, a link to one, and a directory each fail unopened, as
    /// invalid input; a regular file and a link to one read as `std` reads
    /// them; an absent path fails as `std`'s read does.
    #[test]
    #[cfg(unix)]
    fn only_a_regular_file_is_opened() {
        let tmp = tempfile::TempDir::new().unwrap();
        let dir = tmp.path().to_path_buf();
        make_fifo(&dir.join("pipe"));
        std::os::unix::fs::symlink(dir.join("pipe"), dir.join("pipe-link")).unwrap();
        std::fs::create_dir(dir.join("dir")).unwrap();
        std::fs::write(dir.join("file"), "text").unwrap();
        std::os::unix::fs::symlink(dir.join("file"), dir.join("file-link")).unwrap();
        within_deadline("reading a FIFO", move || {
            for name in ["pipe", "pipe-link", "dir"] {
                let error = read(&dir.join(name)).unwrap_err();
                assert_eq!(error.kind(), ErrorKind::InvalidInput, "{name}: {error}");
                let error = read_to_string(&dir.join(name)).unwrap_err();
                assert_eq!(error.kind(), ErrorKind::InvalidInput, "{name}: {error}");
            }
            for name in ["file", "file-link"] {
                assert_eq!(read(&dir.join(name)).unwrap(), b"text");
                assert_eq!(read_to_string(&dir.join(name)).unwrap(), "text");
            }
            assert_eq!(
                read(&dir.join("absent")).unwrap_err().kind(),
                ErrorKind::NotFound
            );
            std::fs::write(dir.join("latin1"), b"\xe9").unwrap();
            assert_eq!(
                read_to_string(&dir.join("latin1")).unwrap_err().kind(),
                ErrorKind::InvalidData
            );
        });
    }

    /// Clippy reads only the nearest `clippy.toml`, so the crate's replaces
    /// the workspace's: it must carry every one of the workspace's settings,
    /// or this crate silently loses a ban every other crate keeps.
    #[test]
    fn clippy_config_repeats_the_workspace_bans() {
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        let workspace = read_to_string(&manifest.join("../../clippy.toml")).unwrap();
        let crate_config = read_to_string(&manifest.join("clippy.toml")).unwrap();
        let crate_lines: HashSet<&str> = crate_config.lines().collect();
        let settings: Vec<&str> = workspace
            .lines()
            .filter(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
            .collect();
        assert!(
            settings
                .iter()
                .any(|line| line.contains("std::process::Command::spawn")),
            "the workspace's clippy.toml no longer holds the spawn ban: {workspace}"
        );
        for line in settings {
            assert!(
                crate_lines.contains(line),
                "crates/nuget/clippy.toml is missing the workspace's {line:?}"
            );
        }
    }
}
