//! Matching a condition atom against NuGet's restore guards allocates
//! nothing of its own: it runs on every conjunct of every group condition
//! outside the install. (Reading whether a guard's value expands is the
//! evaluator's own scan, which these atoms never reach.) A binary of its
//! own, as the count is the whole process's.

use borzoi_msbuild::test_support::nuget_group_atom;
use borzoi_oracle_harness::alloc_limit::{self, LimitedAlloc};

#[global_allocator]
static ALLOC: LimitedAlloc = LimitedAlloc;

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
    let before = alloc_limit::allocations();
    let matched = atoms.iter().filter(|atom| nuget_group_atom(atom)).count();
    let allocated = alloc_limit::allocations() - before;
    assert_eq!(matched, 2);
    assert_eq!(
        allocated,
        0,
        "matching {} atoms allocated {allocated} blocks",
        atoms.len()
    );
}
