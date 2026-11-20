//! The certified domain of `source_existence`: every form of every leaf the
//! walk interprets ([`borzoi_sema::LEAF_FORMS`]), each a producer graded
//! like any other cell, and the walk held to the row's verdict. A form the
//! table says is read must be read and covered; one it says is declined
//! must decline. The table is the predicate's specification, so a change to
//! either alone fails here.

use borzoi_oracle_harness::manifest::Manifest;
use borzoi_sema::{LEAF_FORMS, ProviderReferences, Verdict};

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::source_existence_diff::{Cell, grade_cells};

#[test]
fn every_leaf_form_is_read_or_declined_as_the_table_says() {
    let cells: Vec<Cell> = LEAF_FORMS
        .iter()
        .map(|f| {
            let mut cell = Cell::new(
                format!("domain_{:?}_{}", f.leaf, f.form),
                &[("Lib.fs", f.source)],
            );
            cell.providers_possible = f.providers == ProviderReferences::Possible;
            cell
        })
        .collect();
    let (entries, failures) = grade_cells(&cells);
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let mut wrong = Vec::new();
    for (form, cell) in LEAF_FORMS.iter().zip(&cells) {
        let verdict = entries
            .iter()
            .find(|(name, _)| *name == cell.name)
            .map(|(_, v)| v.as_str())
            .unwrap_or("");
        let read = !verdict.starts_with("certified: unread");
        let expected = form.verdict == Verdict::Read;
        if read != expected {
            wrong.push(format!(
                "{}: the table says {:?}, the walk gave {verdict}",
                cell.name, form.verdict
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    let manifest = Manifest::from_keyed(entries).expect("well-formed entries");
    check_manifest(
        "source_existence_domain",
        &manifest,
        &regenerate(
            "source_existence_domain::every_leaf_form_is_read_or_declined_as_the_table_says",
        ),
    );
}
