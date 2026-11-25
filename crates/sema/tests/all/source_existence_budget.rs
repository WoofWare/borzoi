//! The walk's [`Budget`], over the input families whose rows grow faster
//! than their source: many types in one module (rows linear in the input),
//! a type at the bottom of a deep nest and a long dotted namespace (row
//! bytes quadratic in the depth), and long names. Judged by counts, never by
//! time:
//!
//! - **the charge is honest**: under no limit, the walk's charge is at least
//!   what its rows hold, counted from the rows themselves ([`measure`]);
//! - **the cap holds**: under any budget, the walk reads a producer exactly
//!   when the charge it makes under no limit fits, and then charges the same;
//!   it declines with the budget as the cause otherwise;
//! - **the charge is memory**: at the default budget's corner, the bytes the
//!   walk allocates are at most a small multiple of what it charged, in a
//!   child process whose allocator counts them.

use std::time::Duration;

use borzoi_assembly::existence::PickledEntityRow;
use borzoi_oracle_harness::alloc_limit;
use borzoi_oracle_harness::stack_probe::{self, Limited};
use borzoi_sema::{Budget, Charged, ExistenceUnread, SourceExistence};
use proptest::prelude::*;

use crate::source_existence_diff::{Cell, ours_under};

/// No limit.
const UNBOUNDED: Budget = Budget {
    rows: usize::MAX,
    bytes: usize::MAX,
};

/// A family whose rows grow faster than their source.
#[derive(Clone, Copy, Debug)]
enum Family {
    /// `n` types in one module.
    Wide,
    /// `n` nested modules, a type at the bottom.
    Deep,
    /// A namespace of `n` segments, a type in it.
    Dotted,
    /// A module and a type whose names are `n` bytes long.
    Long,
    /// A module of `n` values, which declare no entity: one row, however
    /// wide.
    Values,
}

/// The family's member of size `n`.
fn source(family: Family, n: usize) -> String {
    match family {
        Family::Wide => {
            let mut src = "module W\n".to_owned();
            for k in 0..n {
                src.push_str(&format!("type T{k} = int\n"));
            }
            src
        }
        Family::Deep => {
            let mut src = "module D\n".to_owned();
            for depth in 0..n {
                src.push_str(&format!("{}module M{depth} =\n", "    ".repeat(depth)));
            }
            src.push_str(&format!("{}type Bottom = int\n", "    ".repeat(n)));
            src
        }
        Family::Dotted => {
            let segments: Vec<String> = (0..n.max(1)).map(|k| format!("S{k}")).collect();
            format!("namespace {}\ntype T = int\n", segments.join("."))
        }
        Family::Long => {
            let name = format!("L{}", "x".repeat(n));
            format!("module Top\nmodule {name} =\n    type {name} = int\n")
        }
        Family::Values => {
            let mut src = "module Top\nmodule V =\n".to_owned();
            for k in 0..n {
                src.push_str(&format!("    let v{k} = {k}\n"));
            }
            src
        }
    }
}

fn walk(family: Family, n: usize, budget: Budget) -> SourceExistence {
    let cell = Cell::new("budget", &[("Lib.fs", &source(family, n))]);
    ours_under(&cell, budget)
}

/// What `rows` hold, counted from the rows: each row itself, and each name
/// it holds as a `String` and its text.
fn measure(rows: &[PickledEntityRow]) -> Charged {
    let name = |s: &String| std::mem::size_of::<String>() + s.len();
    let bytes = rows
        .iter()
        .map(|r| {
            std::mem::size_of::<PickledEntityRow>()
                + r.namespace.iter().map(name).sum::<usize>()
                + r.enclosing.iter().map(name).sum::<usize>()
                + name(&r.logical_name)
                + name(&r.compiled_name)
        })
        .sum();
    Charged {
        rows: rows.len(),
        bytes,
    }
}

fn family() -> impl Strategy<Value = Family> {
    prop_oneof![
        Just(Family::Wide),
        Just(Family::Deep),
        Just(Family::Dotted),
        Just(Family::Long),
        Just(Family::Values),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    /// Under no limit, the walk reads every member, and charges at least
    /// what its rows hold.
    #[test]
    fn the_charge_holds_the_rows(family in family(), n in 0usize..120) {
        let SourceExistence::Read(surface) = walk(family, n, UNBOUNDED) else {
            panic!("{family:?} {n} is in the domain");
        };
        let held = measure(&surface.entities);
        prop_assert!(surface.charged.rows >= held.rows, "{family:?} {n}: {:?} {held:?}", surface.charged);
        prop_assert!(surface.charged.bytes >= held.bytes, "{family:?} {n}: {:?} {held:?}", surface.charged);
    }

    /// Under any budget, the walk reads exactly the members whose unlimited
    /// charge fits it, charging the same, and declines the rest with the
    /// budget as the cause.
    #[test]
    fn the_cap_holds(
        family in family(),
        n in 0usize..120,
        rows in 0usize..200,
        bytes in 0usize..400_000,
    ) {
        let SourceExistence::Read(free) = walk(family, n, UNBOUNDED) else {
            panic!("{family:?} {n} is in the domain");
        };
        let need = free.charged;
        let fits = need.rows <= rows && need.bytes <= bytes;
        match walk(family, n, Budget { rows, bytes }) {
            SourceExistence::Read(surface) => {
                prop_assert!(fits, "{family:?} {n}: read under {rows}/{bytes}, needing {need:?}");
                prop_assert_eq!(surface.charged, need);
                prop_assert_eq!(surface.entities, free.entities);
            }
            SourceExistence::Unread(ExistenceUnread::Budget(over)) => {
                prop_assert!(!fits, "{family:?} {n}: declined under {rows}/{bytes}, needing {need:?}");
                prop_assert!(over.charged_rows <= rows && over.charged_bytes <= bytes);
            }
            other => prop_assert!(false, "{family:?} {n}: {other:?}"),
        }
    }
}

/// Each family grows faster than linearly where it should: the deep and the
/// dotted families' charge is quadratic in their size, so a budget that is
/// linear in the input would not bound them.
#[test]
fn the_families_grow_as_they_claim() {
    let bytes = |family, n| match walk(family, n, UNBOUNDED) {
        SourceExistence::Read(s) => s.charged.bytes,
        other => panic!("{family:?} {n}: {other:?}"),
    };
    for family in [Family::Deep, Family::Dotted] {
        let (small, large) = (bytes(family, 50), bytes(family, 100));
        assert!(
            large > 3 * small,
            "{family:?}: 50 charges {small}, 100 charges {large}, which is not quadratic"
        );
    }
    let (small, large) = (bytes(Family::Wide, 50), bytes(Family::Wide, 100));
    assert!(large < 3 * small, "Wide: {small} then {large}");
}

const CHILD: &str = "source_existence_budget::budget_child";

const CASE_VAR: &str = "BORZOI_SOURCE_EXISTENCE_BUDGET_CASE";

const CASE_TIMEOUT: Duration = Duration::from_secs(600);

/// The size at which `family`'s member charges the most bytes that still fit
/// [`Budget::DEFAULT`]: its corner.
fn corner(family: Family) -> usize {
    let fits = |n| matches!(walk(family, n, Budget::DEFAULT), SourceExistence::Read(_));
    let (mut lo, mut hi) = (0usize, 1usize);
    while fits(hi) {
        lo = hi;
        hi *= 2;
    }
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if fits(mid) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    lo
}

/// Child entry: walk the named family's corner, and report what the walk
/// charged against what the allocator counted it taking.
#[test]
#[ignore = "child-process entry for source_existence_budget"]
fn budget_child() {
    let Some(case) = stack_probe::requested_case(CASE_VAR) else {
        return;
    };
    let (family, n) = match case.as_str() {
        "Dotted" => (Family::Dotted, corner(Family::Dotted)),
        "Values" => (Family::Values, VALUES),
        other => panic!("no budget case {other}"),
    };
    let cell = Cell::new("corner", &[("Lib.fs", &source(family, n))]);
    let project = crate::source_existence_diff::project_files(&cell);
    let items: Vec<borzoi_sema::CompileItem<'_>> = project
        .iter()
        .map(borzoi_sema::CompileItem::Parsed)
        .collect();
    let base = alloc_limit::live_bytes();
    alloc_limit::reset_peak();
    let read = borzoi_sema::source_existence(
        borzoi_sema::Producer {
            items: &items,
            providers: borzoi_sema::ProviderReferences::None,
        },
        Budget::DEFAULT,
    );
    let peak = alloc_limit::peak_bytes().saturating_sub(base);
    let charged = match &read {
        SourceExistence::Read(s) => s.charged.bytes,
        other => panic!("the corner is read: {other:?}"),
    };
    stack_probe::report(&format!("{n} {charged} {peak}"));
}

/// The values in [`the_walk_allocates_nothing_for_what_declares_no_entity`]'s
/// module.
const VALUES: usize = 50_000;

/// A module of many values is two rows, and the walk's memory beyond them
/// does not grow with the values: it reads each declaration list as the tree
/// holds it, never collected.
#[test]
fn the_walk_allocates_nothing_for_what_declares_no_entity() {
    let verdict = match stack_probe::run_case_limited(CHILD, CASE_VAR, "Values", CASE_TIMEOUT) {
        Limited::Survived(verdict) => verdict,
        other => panic!("Values: {other:?}"),
    };
    let numbers: Vec<usize> = verdict
        .split(' ')
        .map(|n| n.parse().expect("a count"))
        .collect();
    let [_, charged, peak] = numbers[..] else {
        panic!("Values: {verdict}");
    };
    // A small constant: two rows, and the walk's own bookkeeping.
    assert!(
        peak <= charged + 16 * 1024,
        "{VALUES} values charge {charged} and allocate {peak}"
    );
}

/// At the default budget's corner, the walk allocates at most a few times
/// what it charged: the charge is the memory, not a proxy for it. The dotted
/// family reaches the corner; the deep one meets the parser's height bound
/// first, and the wide one only at hundreds of thousands of declarations.
#[test]
fn the_default_budget_bounds_the_memory_at_its_corner() {
    let family = "Dotted";
    let verdict = match stack_probe::run_case_limited(CHILD, CASE_VAR, family, CASE_TIMEOUT) {
        Limited::Survived(verdict) => verdict,
        other => panic!("{family}: {other:?}"),
    };
    let numbers: Vec<usize> = verdict
        .split(' ')
        .map(|n| n.parse().expect("a count"))
        .collect();
    let [n, charged, peak] = numbers[..] else {
        panic!("{family}: {verdict}");
    };
    eprintln!("{family}: the corner is {n}, charging {charged} and allocating {peak}");
    assert!(
        charged > Budget::DEFAULT.bytes / 2,
        "{family}: the corner ({n}) charges {charged}, far from the budget"
    );
    assert!(
        peak <= 4 * charged,
        "{family}: the corner ({n}) charges {charged} and allocates {peak}"
    );
}
