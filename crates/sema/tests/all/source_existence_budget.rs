//! The walk's input bound holds memory: a producer at the corner of every
//! bound at once (`MAX_DECLARATIONS` declarations, each at `MAX_DEPTH`
//! under names of `MAX_NAME_BYTES`) is walked and then built into the
//! existence set, as the consumer builds it, in a child process whose
//! allocator refuses more than a small multiple of what those rows' paths
//! can take. Inside the bound there is no metering: the rows are one per
//! declaration, so this corner is the most any input inside it can hold.

use std::time::Duration;

use borzoi_oracle_harness::alloc_limit;
use borzoi_oracle_harness::stack_probe::{self, Limited};
use borzoi_sema::{MAX_DECLARATIONS, MAX_DEPTH, MAX_NAME_BYTES, SourceExistence};

use crate::source_existence_diff::{Cell, ours};

const CHILD: &str = "source_existence_budget::budget_child";

const CASE_VAR: &str = "BORZOI_SOURCE_EXISTENCE_BUDGET_CASE";

/// What the corner's rows' paths can take: one path of `MAX_DEPTH` names of
/// `MAX_NAME_BYTES` per declaration.
const PATH_BYTES: usize = MAX_DECLARATIONS * MAX_DEPTH * MAX_NAME_BYTES;

/// What the case may hold past the child's baseline: the source text and
/// its tree, the rows, and the set built from them.
const MEMORY_ALLOWANCE: usize = 12 * PATH_BYTES;

const CASE_TIMEOUT: Duration = Duration::from_secs(600);

/// A name of `MAX_NAME_BYTES`, distinct by `stem`.
fn long(stem: &str) -> String {
    format!("{stem}{}", "x".repeat(MAX_NAME_BYTES - stem.len()))
}

/// The corner: a namespace segment, `MAX_DEPTH - 2` nested modules beneath
/// it, and as many types in the innermost as fill `MAX_DECLARATIONS` (each a
/// path of `MAX_DEPTH` names), every name `MAX_NAME_BYTES` long.
fn corner() -> String {
    let mut src = format!("namespace {}\n", long("N"));
    for depth in 0..MAX_DEPTH - 2 {
        src.push_str(&format!(
            "{}module {} =\n",
            "    ".repeat(depth),
            long(&format!("M{depth}"))
        ));
    }
    let indent = "    ".repeat(MAX_DEPTH - 2);
    for k in 0..MAX_DECLARATIONS - (MAX_DEPTH - 1) {
        src.push_str(&format!("{indent}type {} = int\n", long(&format!("T{k}"))));
    }
    src
}

/// Child entry: walk the corner under the memory allowance, build the
/// existence set from what it read, and report how many entities it holds.
#[test]
#[ignore = "child-process entry for source_existence_budget"]
fn budget_child() {
    let Some(_) = stack_probe::requested_case(CASE_VAR) else {
        return;
    };
    let src = corner();
    let cell = Cell::new("corner", &[("Lib.fs", &src)]);
    let base = alloc_limit::live_bytes();
    alloc_limit::limit_live_bytes(base + MEMORY_ALLOWANCE);
    let verdict = match ours(&cell, None).0 {
        SourceExistence::Read(surface) => {
            let facts = borzoi_sema::test_support::existence_facts(
                &surface.index(),
                &surface.assembly_auto_opens,
            );
            format!("read {}", facts.entities.len())
        }
        SourceExistence::Unread(why) => format!("{why:?}"),
    };
    stack_probe::report(&verdict);
}

#[test]
fn the_bound_corner_is_read_within_the_allowance() {
    match stack_probe::run_case_limited(CHILD, CASE_VAR, "corner", CASE_TIMEOUT) {
        Limited::Survived(verdict) => {
            // Every declaration but the namespace's is an entity.
            let expected = format!("read {}", MAX_DECLARATIONS - 1);
            assert_eq!(verdict, expected, "the corner is inside the bound");
        }
        other => panic!("the bound corner: {other:?}"),
    }
}
