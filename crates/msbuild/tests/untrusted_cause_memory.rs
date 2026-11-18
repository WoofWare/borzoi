//! What an evaluation holds when one long piece of text is the cause of many
//! properties' doubt (#899): a condition the walk cannot decide, or the name
//! of a property it reads undefined.
//!
//! Each doubted property carries its cause, and so does each one published
//! untrusted. A cause that owned its text would cost the text's length per
//! property, which a project file can ask for: 4,000 properties under one
//! 64 KiB condition would hold 250 MiB. The text is shared, so the evaluation
//! holds it a bounded number of times.
//!
//! The bound is drawn in the allocator (`borzoi_oracle_harness::alloc_limit`),
//! and this is a binary of its own because the count is the whole process's.

use std::collections::HashMap;
use std::sync::Mutex;

use borzoi_msbuild::{ParsedProject, PropertyRead};
use borzoi_oracle_harness::alloc_limit::{self, LimitedAlloc};

#[global_allocator]
static ALLOC: LimitedAlloc = LimitedAlloc;

/// One measurement at a time: the peak is the process's.
static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

const PROPERTIES: usize = 4_000;
const CONDITION_BYTES: usize = 64 << 10;

/// The most an evaluation may hold above what was live before it. A copy of
/// the condition per property would be [`PROPERTIES`] × [`CONDITION_BYTES`],
/// 250 MiB; the evaluation's own tables and the project's text are a few MiB.
const MAY_HOLD: usize = 32 << 20;

/// A condition MSBuild evaluates to `true`, [`CONDITION_BYTES`] long, that the
/// walk cannot evaluate.
fn long_undecidable_condition() -> String {
    format!(
        "$([System.String]::IsNullOrWhiteSpace('{}'))",
        " ".repeat(CONDITION_BYTES)
    )
}

fn properties() -> String {
    (0..PROPERTIES)
        .map(|i| format!("    <P{i}>v</P{i}>\n"))
        .collect()
}

/// Evaluate `source`, returning the project and the most the process held
/// above what was live before, with the project still alive.
fn evaluate(source: &str) -> (ParsedProject, usize) {
    let tmp = tempfile::TempDir::new().unwrap();
    let project = tmp.path().join("p.fsproj");
    std::fs::write(&project, source).unwrap();
    std::fs::write(tmp.path().join("Hidden.props"), "<Project />\n").unwrap();
    let base = alloc_limit::live_bytes();
    alloc_limit::reset_peak();
    let parsed = borzoi_msbuild::parse_fsproj_with_imports(
        &borzoi_msbuild::ProjectFile::buffer(&project, source)
            .expect("a project path spelt as its full path"),
        &HashMap::new(),
        &HashMap::new(),
        None,
        None,
    )
    .unwrap();
    let held = alloc_limit::peak_bytes().saturating_sub(base);
    (parsed, held)
}

fn assert_every_property_is_untrusted(parsed: &ParsedProject) {
    for i in [0, PROPERTIES / 2, PROPERTIES - 1] {
        let name = format!("P{i}");
        assert!(
            matches!(parsed.property(&name), PropertyRead::Untrusted(_)),
            "{name}: {:?}",
            parsed.property(&name)
        );
    }
}

/// Every property bound before an import the walk cannot decide is stale, and
/// published untrusted with the import's condition as its cause.
#[test]
fn many_properties_before_an_undecided_import_share_its_condition() {
    let _one = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
    let source = format!(
        "<Project>\n  <PropertyGroup>\n{}  </PropertyGroup>\n  \
         <Import Project=\"Hidden.props\" Condition=\"{}\" />\n</Project>\n",
        properties(),
        long_undecidable_condition()
    );
    let (parsed, held) = evaluate(&source);
    assert_every_property_is_untrusted(&parsed);
    assert!(
        held <= MAY_HOLD,
        "the evaluation held {held} bytes at its peak"
    );
}

/// Every property a group writes under a condition the walk cannot decide is
/// unpinned with that condition as its root.
#[test]
fn many_properties_under_an_undecided_group_condition_share_it() {
    let _one = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
    let source = format!(
        "<Project>\n  <PropertyGroup Condition=\"{}\">\n{}  </PropertyGroup>\n</Project>\n",
        long_undecidable_condition(),
        properties()
    );
    let (parsed, held) = evaluate(&source);
    assert_every_property_is_untrusted(&parsed);
    assert!(
        held <= MAY_HOLD,
        "the evaluation held {held} bytes at its peak"
    );
}

/// Every property bound before an import gated on a name the walk reads
/// undefined, and cannot call unset (its only write is one the walk refuses),
/// is published untrusted with that name in its cause.
#[test]
fn many_properties_before_an_import_gated_on_a_long_name_share_the_name() {
    let _one = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
    let name = format!("N{}", "a".repeat(CONDITION_BYTES));
    let source = format!(
        "<Project>\n  <PropertyGroup>\n{}    <{name}>$([System.Guid]::NewGuid())</{name}>\n  \
         </PropertyGroup>\n  <Import Project=\"Hidden.props\" Condition=\"'$({name})' == ''\" />\n\
         </Project>\n",
        properties()
    );
    let (parsed, held) = evaluate(&source);
    assert_every_property_is_untrusted(&parsed);
    assert!(
        held <= MAY_HOLD,
        "the evaluation held {held} bytes at its peak"
    );
}
