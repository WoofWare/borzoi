//! Differential test (`parser::parse` vs FCS): the `..` token in each place F#
//! spells it, generated as a grid so the neighbours of each shape are graded
//! too.
//!
//! `..` is FCS's `DOT_DOT`. It is three things to the grammar:
//!
//! * the range operator of `declExpr` (`declExpr DOT_DOT declExpr`, and the
//!   open forms `declExpr DOT_DOT` and `DOT_DOT declExpr`), which FCS's parser
//!   admits in *any* expression position: `s..` after a receiver parses as
//!   `IndexRange(Some s, None)`, and only the type checker rejects a range
//!   outside a list, array, `for` or slice (FS0751, `tcInvalidIndexerExpression`);
//! * an operator name, `operatorName: DOT_DOT { ".." } | DOT_DOT DOT_DOT
//!   { ".. .." }`, so `( .. )` is `op_Range` and `( .. .. )` is `op_RangeStep`,
//!   in a `let` or member head and as a value;
//! * part of the lexer's longer tokens (`...`, `..^`, `1..`), which decide how
//!   glued spellings split.
//!
//! Each cell goes to [`assert_parse_verdicts_match`], so FCS decides whether it
//! parses: a cell we wrongly reject, wrongly accept or accept with a divergent
//! tree fails. A cell both reject is followed by a declaration that FCS keeps,
//! and the recovered trees are graded on it
//! ([`assert_recovered_trees_agree`]).

use crate::common::assert_parse_verdicts_match;
use crate::common::recovery::assert_recovered_trees_agree;
use borzoi_oracle_harness::panic_silence::{catch_unwind_silent, take_silenced_panic};

/// The hole each template's shape fills.
const HOLE: &str = "@";

/// A declaration after every cell, outside any damage a cell's shape causes.
const AFTER: &str = "let after = 1\n";

/// Run every cell through the verdict oracle, and every cell both reject
/// through the recovery oracle, collecting (rather than stopping at)
/// divergences, and assert both verdicts were exercised.
fn sweep(what: &str, cells: impl IntoIterator<Item = String>) {
    let mut total = 0;
    let mut accepted = 0;
    let mut failures = Vec::new();
    for body in cells {
        total += 1;
        let source = format!("module M\n{body}{AFTER}");
        let graded = catch_unwind_silent(|| {
            let fcs_accepts = assert_parse_verdicts_match(&source);
            if !fcs_accepts {
                assert_recovered_trees_agree(&source, 0);
            }
            fcs_accepts
        });
        match graded {
            Ok(true) => accepted += 1,
            Ok(false) => {}
            Err(_) => {
                let message = take_silenced_panic().map_or_else(String::new, |p| p.message);
                let first_line = message.lines().next().unwrap_or_default().to_owned();
                failures.push(first_line);
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {total} {what} cells diverge from FCS:\n{}",
        failures.len(),
        failures.join("\n"),
    );
    assert!(
        accepted > 0 && accepted < total,
        "the {what} sweep should both accept and reject, but accepted {accepted} of {total}",
    );
}

/// Every template with every shape in its hole.
fn cross<'a>(templates: &'a [&str], shapes: &'a [&str]) -> impl Iterator<Item = String> + 'a {
    templates
        .iter()
        .flat_map(move |t| shapes.iter().map(move |s| t.replace(HOLE, s)))
}

/// Range shapes, several with a receiver before the `..`: open, closed,
/// stepped, nested, spaced and glued, and the longer tokens a glued `..`
/// becomes (`...`, `..^`).
const RANGE_SHAPES: &[&str] = &[
    "s..",
    "s ..",
    "s.. 1",
    "s..1",
    "s .. 1",
    "s..t",
    "s..Length",
    "s.Length..",
    "s.Length..t",
    "s.[0]..",
    "..s",
    ".. s",
    "s.. ..t",
    "s..1..3",
    "s .. 1 .. 3",
    "1..",
    "1.. ..3",
    "s..^1",
    "s..-1",
    "s..+1",
    "s..|t",
    "s...",
    "s...t",
    "s....t",
    "s. ..",
    "..",
];

/// Where a range shape sits: a plain binding body, after a receiver's own
/// application, and the places a range is legal to the type checker (a list,
/// array, sequence, `for`, slice and indexer), parenthesised and in a tuple.
const RANGE_CONTEXTS: &[&str] = &[
    "let f (s: string) = @\n",
    "let x = f @\n",
    "let x = (@)\n",
    "let x = f (@)\n",
    "let x = @, 1\n",
    "let x = [@]\n",
    "let x = [|@|]\n",
    "let x = seq { @ }\n",
    "let x = [ for i in @ -> i ]\n",
    "for i in @ do ()\n",
    "let x = a.[@]\n",
    "let x = a[@]\n",
    "let x = a.[@, 0]\n",
    "let x = a[0, @]\n",
];

/// Every range shape in every range context.
#[test]
fn diff_dot_dot_grid_ranges() {
    sweep("range", cross(RANGE_CONTEXTS, RANGE_SHAPES));
}

/// `..` spelt as an operator name, spaced and glued, with the neighbours a
/// glued spelling lexes into.
const OPERATOR_SHAPES: &[&str] = &[
    "( .. )",
    "(..)",
    "( .. .. )",
    "(.. ..)",
    "(..   ..)",
    "( ....)",
    "( ... )",
    "( ..^ )",
    "( .. .. .. )",
];

/// Where an operator name sits: a `let` head (plain, `inline`, `rec`, with
/// an access modifier), a member head (static and instance, in a type and in
/// an augmentation), an abstract slot, and a use as a value, applied,
/// piped and qualified.
const OPERATOR_CONTEXTS: &[&str] = &[
    "let @ a b = [a .. b]\n",
    "let inline @ a b = [a .. b]\n",
    "let rec @ a b = [a .. b]\n",
    "let private @ a b c = [a .. b .. c]\n",
    "let @ = fun a b -> [a .. b]\n",
    "type T() =\n    static member @ (a: T, b: int) = 0\n",
    "type T() =\n    static member inline @ (a: T, b: int, c: int) = 0\n",
    "type T() =\n    member _.@ (b: int) = 0\n",
    "type T =\n    abstract @ : int -> int\n",
    "type System.String with\n    static member (*) (a: string, b: int) = 0L\n    static member @ (a: string, b: int, c: int) = 0L\n",
    "type System.String with\n    static member @ (a: string, b: int) = 0L\n",
    "let x = @\n",
    "let x = @ 1 2\n",
    "let x = 1 |> @ 0\n",
    "let x = Operators.@ 1 2\n",
    "let x = id @\n",
];

/// Every operator shape in every operator context.
#[test]
fn diff_dot_dot_grid_operator_names() {
    sweep("operator-name", cross(OPERATOR_CONTEXTS, OPERATOR_SHAPES));
}
