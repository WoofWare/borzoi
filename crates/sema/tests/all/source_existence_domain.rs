//! The domain of `source_existence`: every [`Form`] of every leaf the walk
//! interprets, its witness graded against FCS like any other cell, and the
//! walk held to the form's verdict. A form whose verdict is `Read` must be
//! read and covered; one whose verdict is `Declined` must decline. The forms
//! are the classifiers' closed list, so this grid is the enum: a form added
//! without a witness FCS grades, or a verdict the walk does not keep, fails
//! here.

use borzoi_oracle_harness::manifest::Manifest;
use borzoi_oracle_harness::project_graph::Target;
use borzoi_sema::{Form, Verdict};

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::source_existence_diff::{Cell, grade_cells};

#[test]
fn every_form_is_read_or_declined_as_its_verdict_says() {
    let cells: Vec<Cell> = Form::ALL
        .iter()
        .map(|f| {
            let mut cell = Cell::new(
                format!("domain_{:?}_{:?}", f.leaf(), f),
                &[("Lib.fs", f.witness())],
            );
            // A headerless file is the last of an executable.
            if *f == Form::AnonymousModule {
                cell.target = Target::Exe;
            }
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
    for (form, cell) in Form::ALL.iter().zip(&cells) {
        let verdict = entries
            .iter()
            .find(|(name, _)| *name == cell.name)
            .map(|(_, v)| v.as_str())
            .unwrap_or("");
        let read = !verdict.starts_with("certified: unread");
        if read != (form.verdict() == Verdict::Read) {
            wrong.push(format!(
                "{}: the form says {:?}, the walk gave {verdict}",
                cell.name,
                form.verdict()
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    let manifest = Manifest::from_keyed(entries).expect("well-formed entries");
    check_manifest(
        "source_existence_domain",
        &manifest,
        &regenerate("source_existence_domain::every_form_is_read_or_declined_as_its_verdict_says"),
    );
}
