//! The layout sweep: every grid cell whose reading depends on where a token
//! sits, with layout trivia inserted at every place it can go.
//!
//! The walk reads a position only for the names FCS mangles by line (a
//! marked class `let`'s `basic@line`). A reader that takes that position
//! from a node's range rather than from its first token reads the node's
//! leading trivia's line, which is wrong exactly when a line break sits
//! between the node's start and its first token. The generator
//! (`source_existence_gen`) mixes layout into random cases; this sweep puts
//! a [`Layout::LineBreak`] before every token that is not its line's first,
//! and a [`Layout::CommentLine`] before every line, in every grid cell whose
//! certified reading carries [`Approximation::ClassLetName`], one case per
//! place, each graded against FCS and pinned. The ignored `deep_` twin does
//! every [`Layout`] in every grid cell our walk reads.

use borzoi_oracle_harness::manifest::Manifest;
use borzoi_sema::{Approximation, SourceExistence};

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::source_existence_diff::{Cell, grade_cells, ours};
use crate::source_existence_gen::{Layout, insert_all, layout_lines};

/// Whether our certified reading of `cell` is read and holds `approximation`.
fn read_with(cell: &Cell, approximation: Option<Approximation>) -> bool {
    match ours(cell, None).0 {
        SourceExistence::Read(surface) => {
            approximation.is_none_or(|a| surface.approximations.contains(&a))
        }
        SourceExistence::Unread(_) => false,
    }
}

/// The 1-based line and column of `at` in `text`.
fn line_col(text: &str, at: usize) -> (usize, usize) {
    let line = text[..at].matches('\n').count() + 1;
    let col = at - text[..at].rfind('\n').map_or(0, |i| i + 1);
    (line, col)
}

/// Every cell `ops` make of `cells`: one per op, file and place.
fn perturbed(cells: &[Cell], ops: &[Layout]) -> Vec<Cell> {
    let mut out = Vec::new();
    for cell in cells {
        for (i, (file, text)) in cell.files.iter().enumerate() {
            for (start, inner) in layout_lines(text) {
                for &op in ops {
                    let places: Vec<usize> = if Layout::AT_LINE.contains(&op) {
                        vec![start]
                    } else {
                        inner.clone()
                    };
                    for at in places {
                        let (line, col) = line_col(text, at);
                        let mut c = cell.clone();
                        c.name = format!("{}@{file}:{line}:{col}:{op:?}", cell.name);
                        c.files[i].1 = insert_all(text, vec![op.edit(start, at)]);
                        out.push(c);
                    }
                }
            }
        }
    }
    out
}

fn assert_no_failures(failures: &[String]) {
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn layout_inside_every_position_reading_cell() {
    let cells: Vec<Cell> = crate::source_existence_grid::cells()
        .into_iter()
        .filter(|c| read_with(c, Some(Approximation::ClassLetName)))
        .collect();
    assert!(
        !cells.is_empty(),
        "no grid cell reads a position: the sweep grades nothing"
    );
    let cases = perturbed(&cells, &[Layout::LineBreak, Layout::CommentLine]);
    eprintln!("{} cells, {} cases", cells.len(), cases.len());
    let (entries, failures) = grade_cells(&cases);
    assert_no_failures(&failures);
    let manifest = Manifest::from_keyed(entries).expect("well-formed entries");
    check_manifest(
        "source_existence_layout",
        &manifest,
        &regenerate("source_existence_layout::layout_inside_every_position_reading_cell"),
    );
}

#[test]
#[ignore = "every layout perturbation at every place of every read grid cell: thousands of FCS checks"]
fn deep_layout_inside_every_read_cell() {
    let cells: Vec<Cell> = crate::source_existence_grid::cells()
        .into_iter()
        .filter(|c| read_with(c, None))
        .collect();
    let all = [
        Layout::CommentLine,
        Layout::BlankLine,
        Layout::BlockComment,
        Layout::MultiLineComment,
        Layout::LineBreak,
    ];
    let cases = perturbed(&cells, &all);
    eprintln!("{} cells, {} cases", cells.len(), cases.len());
    let (_, failures) = grade_cells(&cases);
    assert_no_failures(&failures);
}
