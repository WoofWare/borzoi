//! Matching a condition atom against NuGet's restore guards allocates
//! nothing of its own: it runs on every conjunct of every group condition
//! outside the install. (Reading whether a guard's value expands is the
//! evaluator's own scan; the values here are ones it reads without
//! allocating.) The count is the measuring thread's alone
//! (`alloc_limit::thread_allocations`), so the test runner's own threads
//! move nothing.

use borzoi_msbuild::test_support::nuget_group_atom;
use borzoi_oracle_harness::alloc_limit::{self, LimitedAlloc};

#[global_allocator]
static ALLOC: LimitedAlloc = LimitedAlloc;

#[test]
fn matching_a_guard_allocates_nothing() {
    let atoms = [
        // The fixed-value rows.
        "'$(ExcludeRestorePackageImports)' != 'true'",
        "'$(TargetFramework)' == ''",
        // Each row that takes any literal, on one the value scan reads
        // without allocating.
        "'$(TargetFramework)' == ' '",
        "'$(Language)' == ' '",
        "'$(Language)' != ' '",
        // No guard.
        "'$(ExcludeRestorePackageImports)' != 'false'",
        "'$(Configuration)' == 'Debug'",
        "'$(Language)' <> 'F#'",
        "not an atom",
    ];
    let before = alloc_limit::thread_allocations();
    let matched = atoms.iter().filter(|atom| nuget_group_atom(atom)).count();
    let allocated = alloc_limit::thread_allocations() - before;
    assert_eq!(matched, 5);
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
    let before = alloc_limit::thread_allocations();
    let boxed = std::hint::black_box(Box::new(1u64));
    assert!(alloc_limit::thread_allocations() > before);
    drop(boxed);
}

/// Another thread's allocations are not this thread's: the runner's own
/// threads cannot move the count above.
#[test]
fn another_thread_is_not_counted() {
    let before = alloc_limit::thread_allocations();
    std::thread::scope(|scope| {
        scope.spawn(|| {
            for i in 0..100u64 {
                drop(std::hint::black_box(Box::new(i)));
            }
        });
    });
    // Spawning the thread allocates on this one; its hundred boxes do not.
    assert!(alloc_limit::thread_allocations() - before < 100);
}
