//! Matching a condition atom against NuGet's restore guards allocates
//! nothing of its own: it runs on every conjunct of every group condition
//! outside the install. (Reading whether a guard's value expands is the
//! evaluator's own scan, which these atoms never reach.) The count is the
//! measuring thread's alone, so the test runner's own threads move nothing.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

use borzoi_msbuild::test_support::nuget_group_atom;

/// The system allocator, counting each thread's allocations.
struct PerThread;

thread_local! {
    static ALLOCATIONS: Cell<usize> = const { Cell::new(0) };
}

// SAFETY: every call is passed straight to `System`; the count is a
// const-initialised thread-local, which allocates nothing.
unsafe impl GlobalAlloc for PerThread {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let _ = ALLOCATIONS.try_with(|n| n.set(n.get() + 1));
        // SAFETY: the caller's contract is `System`'s.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: the caller's contract is `System`'s.
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOC: PerThread = PerThread;

/// This thread's allocations so far.
fn allocations() -> usize {
    ALLOCATIONS.with(Cell::get)
}

#[test]
fn matching_a_guard_allocates_nothing() {
    // Fixed-value guards, and atoms that are no guard: none reaches the
    // scan of a value.
    let atoms = [
        "'$(ExcludeRestorePackageImports)' != 'true'",
        "'$(TargetFramework)' == ''",
        "'$(ExcludeRestorePackageImports)' != 'false'",
        "'$(Configuration)' == 'Debug'",
        "'$(Language)' <> 'F#'",
        "not an atom",
    ];
    let before = allocations();
    let matched = atoms.iter().filter(|atom| nuget_group_atom(atom)).count();
    let allocated = allocations() - before;
    assert_eq!(matched, 2);
    assert_eq!(
        allocated,
        0,
        "matching {} atoms allocated {allocated} blocks",
        atoms.len()
    );
}

/// The count sees this thread's allocations, so a zero above is the
/// matcher's.
#[test]
fn the_count_sees_this_thread() {
    let before = allocations();
    let boxed = std::hint::black_box(Box::new(1u64));
    assert!(allocations() > before);
    drop(boxed);
}

/// Another thread's allocations are not this thread's: the runner's own
/// threads cannot move the count above.
#[test]
fn another_thread_is_not_counted() {
    let before = allocations();
    std::thread::scope(|scope| {
        scope.spawn(|| {
            for i in 0..100u64 {
                drop(std::hint::black_box(Box::new(i)));
            }
        });
    });
    // Spawning the thread allocates on this one; its hundred boxes do not.
    assert!(allocations() - before < 100);
}
