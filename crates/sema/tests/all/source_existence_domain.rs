//! The domain of `source_existence`: every [`Form`] the walk classifies, its
//! witness graded against FCS like any other cell, and the walk held to the
//! form's verdict. A form whose verdict is `Read` must be read and graded
//! (FCS found it, and ours holds its facts); one whose verdict is `Declined`
//! must decline with itself as the reason. The forms are the classifiers'
//! closed list, so this grid is the enum: a form added without a witness FCS
//! grades, or a verdict the walk does not keep, fails here.

use borzoi_oracle_harness::manifest::Manifest;
use borzoi_oracle_harness::project_graph::Target;
use borzoi_sema::{ExistenceUnread, Form, SourceExistence, Verdict};

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::source_existence_diff::{Cell, grade_cells, graded, ours};

/// A form's witness as a cell: a signature and its implementation for
/// `SignatureFile`, one implementation file otherwise, an executable for a
/// headerless one.
fn witness(form: Form) -> Cell {
    let name = format!("domain_{:?}_{form:?}", form.leaf());
    let mut cell = match form.witness().split_once("//--\n") {
        Some((sig, imp)) => Cell::new(name, &[("Lib.fsi", sig), ("Lib.fs", imp)]),
        None => Cell::new(name, &[("Lib.fs", form.witness())]),
    };
    if form == Form::AnonymousModule {
        cell.graph.target = Target::Exe;
    }
    cell
}

#[test]
fn every_form_is_read_or_declined_as_its_verdict_says() {
    let cells: Vec<Cell> = Form::ALL.iter().map(|f| witness(*f)).collect();
    let (entries, failures) = grade_cells(&cells);
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let mut wrong = Vec::new();
    for (form, cell) in Form::ALL.iter().zip(&cells) {
        let Some(verdict) = entries
            .iter()
            .find(|(name, _)| *name == cell.name)
            .map(|(_, v)| v.as_str())
        else {
            wrong.push(format!("{}: no verdict", cell.name));
            continue;
        };
        let kept = match form.verdict() {
            // Graded against FCS, not merely not declined.
            Verdict::Read => graded(verdict),
            // The walk's own reason, whether or not FCS's reading is graded.
            Verdict::Declined => matches!(
                ours(cell),
                SourceExistence::Unread(ExistenceUnread::Declined(_, f)) if f == *form
            ),
        };
        if !kept {
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
