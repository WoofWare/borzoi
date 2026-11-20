//! The walk's byte budget holds before it allocates: hostile producers whose
//! names multiply (a long name under every line of a long head and every
//! binder; long names under nested modules whose names end in `Module`; a
//! long member name under every arity reading of a many-parametered
//! augmentation) decline within a memory allowance a few times
//! `MAX_ROW_BYTES`, each in a child process whose allocator refuses more.
//! A walk that built its names before charging them would hold gigabytes
//! first, and the child would run out of memory instead of declining.

use std::time::Duration;

use borzoi_oracle_harness::alloc_limit;
use borzoi_oracle_harness::stack_probe::{self, Limited};
use borzoi_sema::{ExistenceUnread, MAX_ROW_BYTES, SourceExistence};

use crate::source_existence_diff::{Cell, ours};

const CHILD: &str = "source_existence_budget::budget_child";

const CASE_VAR: &str = "BORZOI_SOURCE_EXISTENCE_BUDGET_CASE";

/// What a case may hold past the child's baseline: the budget, and room for
/// the walk's own working set.
const MEMORY_ALLOWANCE: usize = 4 * MAX_ROW_BYTES;

const CASE_TIMEOUT: Duration = Duration::from_secs(180);

/// A name long enough that its copies, multiplied, are gigabytes.
fn long(stem: &str) -> String {
    format!("{stem}{}", "x".repeat(10_000))
}

/// The cases, by name: each within the row budget, and over the byte budget
/// by a factor of ten or more.
fn source(case: &str) -> String {
    match case {
        // 301 lines × ~600 binders of a 10 kB name: 1.8 GB of names, under
        // 200,000 rows.
        "class_let_names" => {
            let args: String = (0..300)
                .map(|i| format!("\n            (a{i}: int)"))
                .collect();
            format!(
                "module B\nopen System.Runtime.CompilerServices\ntype T() =\n    [<Extension>]\n    static let {}{args} = 1\n    member _.G = 1\n",
                long("f")
            )
        }
        // 2^12 readings of a path of twelve 10 kB names.
        "module_paths" => {
            let mut src = String::from("namespace N\n");
            for depth in 0..12 {
                src.push_str(&format!(
                    "{}module {}Module =\n",
                    "    ".repeat(depth),
                    long(&format!("M{depth}"))
                ));
            }
            src.push_str(&format!("{}type T = int\n", "    ".repeat(12)));
            src
        }
        // 300 arity readings × every spelling and suffix of each of ten
        // members' 10 kB names.
        "augmentation_names" => {
            let typars: Vec<String> = (0..300).map(|i| format!("'a{i}")).collect();
            let members: String = (0..10)
                .map(|i| format!("    member x.{}() = 1\n", long(&format!("M{i}"))))
                .collect();
            format!(
                "module B\ntype {}<{}> with\n{members}",
                long("T"),
                typars.join(", ")
            )
        }
        other => panic!("no budget case {other}"),
    }
}

const CASES: [&str; 3] = ["class_let_names", "module_paths", "augmentation_names"];

/// Child entry: walk one case under the memory allowance and report the
/// verdict.
#[test]
#[ignore = "child-process entry for source_existence_budget"]
fn budget_child() {
    let Some(case) = stack_probe::requested_case(CASE_VAR) else {
        return;
    };
    let cell = Cell::new(case.clone(), &[("Lib.fs", &source(&case))]);
    let base = alloc_limit::live_bytes();
    alloc_limit::limit_live_bytes(base + MEMORY_ALLOWANCE);
    let verdict = match ours(&cell, None).0 {
        SourceExistence::Read(_) => "read".to_owned(),
        SourceExistence::Unread(why) => format!("{why:?}"),
    };
    stack_probe::report(&verdict);
}

#[test]
fn multiplied_names_decline_within_the_allowance() {
    let mut failures = Vec::new();
    for case in CASES {
        match stack_probe::run_case_limited(CHILD, CASE_VAR, case, CASE_TIMEOUT) {
            Limited::Survived(verdict)
                if verdict == format!("{:?}", ExistenceUnread::TooManyReadings) => {}
            other => failures.push(format!("{case}: {other:?}")),
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
