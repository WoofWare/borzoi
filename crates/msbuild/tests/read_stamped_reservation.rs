//! A whole-file read whose buffer cannot be reserved
//! (`borzoi_msbuild::observed::read_stamped`).
//!
//! The read reserves the file's size before it reads, fallibly, so a file too
//! large to hold fails the read with `OutOfMemory` rather than aborting the
//! process, and before it holds any of the file. Only an allocator that
//! refuses the reservation reaches that branch, so this binary installs the
//! allocation-limit allocator (`borzoi_oracle_harness::alloc_limit`), and is
//! a binary of its own because the limit holds for every thread of the
//! process. The file is sparse, so its size costs no disk.

use std::path::Path;

use borzoi_msbuild::observed::{self, Observation, Observer, ReadCounts};
use borzoi_oracle_harness::alloc_limit::{self, LimitedAlloc};

#[global_allocator]
static ALLOC: LimitedAlloc = LimitedAlloc;

/// The file's size: cheap to read once the limit is lifted.
const SIZE: u64 = 64 << 20;

/// How far past what is live the limit lies: short of the file, so its
/// reservation is refused, and far past what a refused read holds, so a read
/// that grew its buffer as it read rather than reserving it first would hold
/// more than [`HELD_BY_A_REFUSED_READ`] before it failed.
const MARGIN: usize = (SIZE / 2) as usize;

/// The most a read whose reservation is refused may hold: its path and its
/// error, never any of the file.
const HELD_BY_A_REFUSED_READ: usize = 64 << 10;

/// Holds the allocation limit at [`MARGIN`] past what is live, and lifts it
/// when dropped, a failed assertion's unwinding included.
struct Limited;

impl Limited {
    fn new() -> Self {
        alloc_limit::limit_live_bytes(alloc_limit::live_bytes() + MARGIN);
        Limited
    }
}

impl Drop for Limited {
    fn drop(&mut self) {
        alloc_limit::limit_live_bytes(usize::MAX);
    }
}

/// A read whose reservation fails fails as `OutOfMemory` before it holds any
/// of the file, and records one open: the stamp the open file had, marked
/// unreadable, with no digest. That read holds while the reservation keeps
/// failing, and is stale once the file can be read, as it would be had the
/// file changed.
#[test]
fn a_read_whose_reservation_fails_records_the_file_unreadable() {
    let tmp = tempfile::TempDir::new().unwrap();
    let path = tmp.path().join("Huge.dll");
    std::fs::File::create(&path)
        .and_then(|file| file.set_len(SIZE))
        .unwrap();

    let observer = Observer::new();
    let (result, held, asked_again) = {
        let _limited = Limited::new();
        let base = alloc_limit::live_bytes();
        alloc_limit::reset_peak();
        let result = observed::read_stamped(&observer, &path).map(|bytes| bytes.len());
        let held = alloc_limit::peak_bytes().saturating_sub(base);
        (result, held, observed::read_stamped_now(&path))
    };
    let failure = result.expect_err("the reservation was refused");
    assert_eq!(failure.kind(), std::io::ErrorKind::OutOfMemory, "{failure}");
    assert!(
        held <= HELD_BY_A_REFUSED_READ,
        "the refused read held {held} bytes at its peak"
    );

    let (reads, counts) = observer.finish();
    assert_eq!(
        counts,
        ReadCounts {
            opens: 1,
            ..ReadCounts::default()
        }
    );
    let [read] = reads.reads() else {
        panic!("one read: {reads:#?}")
    };
    assert_eq!(read.path, path);
    let Observation::Stamp(Ok(stamp)) = read.observation else {
        panic!("a stamp: {read:#?}")
    };
    assert!(stamp.unreadable, "{stamp:?}");
    assert_eq!((stamp.len, stamp.digest), (SIZE, None), "{stamp:?}");
    assert!(
        observed::same_unreadable(&stamp, &asked_again),
        "asked again under the limit, the read was not the same: {asked_again:?}"
    );
    assert!(
        !read.still_holds(),
        "the read held once the file could be read"
    );
    assert_readable(&path);
}

/// The file, read with no limit, is its size in zeros.
fn assert_readable(path: &Path) {
    let bytes = observed::read_stamped(&Observer::new(), path).unwrap();
    assert_eq!(bytes.len() as u64, SIZE);
    assert!(bytes.iter().all(|&byte| byte == 0));
}
