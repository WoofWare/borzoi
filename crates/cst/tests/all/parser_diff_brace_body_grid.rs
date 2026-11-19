//! Differential test (`parser::parse` vs FCS): a brace body followed, past its
//! own closer, by a token that would classify it.
//!
//! FCS's `braceExprBody` is a record when its leading long identifier is
//! followed by `=` (a field binding) or `with` (a copy-and-update), and a
//! computation expression otherwise. LexFilter swallows the `}` of the brace
//! and any `)` around it, so in the filtered stream the token after `{ a` may
//! be an `=` or `with` that belongs to an enclosing expression:
//! `((builder { a }) = b)` is an equality whose left operand is a
//! computation expression, not a record with a field `a`. The grid puts brace
//! bodies of each shape into contexts where such a token follows their closer,
//! swallowed or emitted, and FCS decides every cell.
//!
//! Each cell goes to [`grade_cell`]: a cell we wrongly reject, wrongly accept
//! or accept with a divergent tree fails. A cell both reject is followed by a
//! declaration that FCS keeps; the recovered trees are graded and that
//! declaration must survive ours.
//!
//! The `seq { @ = b }` context ([`KNOWN_CONTEXT`]) is a known divergence:
//! FCS shifts an `=` directly after the brace body's first `appExpr` into a
//! record field binding, which is FS0609 when that `appExpr` is not a long
//! identifier, and we parse an equality (WoofWare/borzoi#1054).

use crate::common::normalised_ast::{normalise_fcs_dump, normalise_parse};
use crate::common::recovery::{Relation, fcs_units, grade, our_units};
use crate::common::{fcs_ast_batch, fcs_parse_had_errors};
use borzoi_oracle_harness::panic_silence::{catch_unwind_silent, take_silenced_panic};
use std::collections::HashSet;
use std::io::Write;

/// The hole each template's shape fills.
const HOLE: &str = "@";

/// A declaration after every cell, outside any damage a cell's shape causes.
const AFTER: &str = "let after = 1\n";

/// How a cell's parse relates to FCS's.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Outcome {
    /// Both parse cleanly, to the same normalised tree.
    Accepted,
    /// Both report errors, and the recovered trees agree.
    Rejected,
    /// We parse cleanly and FCS reports errors: the one divergence a known
    /// cell may show.
    OnlyFcsRejects,
}

/// Grade one cell against FCS, panicking on a divergence no cell may show.
///
/// We must not reject what FCS accepts. When FCS rejects, the trees must
/// agree outside the damage ([`grade`]), whichever our verdict. And whatever
/// the verdicts, every declaration FCS keeps from [`AFTER`] on must be one of
/// ours: the recovery grade compares only declarations outside both sides'
/// damage, so a recovery that swallowed `after` under a wider error span would
/// otherwise still agree, and the divergence a known cell is excused for is
/// about its brace, not about the declaration after it.
fn grade_cell(source: &str) -> Outcome {
    let json = {
        let mut tmp = tempfile::NamedTempFile::with_suffix(".fs").expect("create tempfile");
        tmp.write_all(source.as_bytes()).expect("write source");
        fcs_ast_batch(tmp.path())
    };
    let parse = borzoi_cst::parser::parse(source);
    let fcs_rejects = fcs_parse_had_errors(&json);
    let we_reject = !parse.errors.is_empty();
    assert!(
        !we_reject || fcs_rejects,
        "parse-verdict divergence for {source:?}: we reject, FCS accepts; our errors: {:?}",
        parse.errors,
    );
    let after = source.rfind(AFTER).expect("every cell ends with AFTER");
    let ours = our_units(&parse);
    for unit in fcs_units(&json, source)
        .iter()
        .filter(|u| u.key.start >= after)
    {
        assert!(
            ours.iter().any(|o| o.key == unit.key),
            "we lose `{}`, which FCS keeps, in {source:?}",
            source[unit.key.start..].lines().next().unwrap_or(""),
        );
    }
    match (we_reject, fcs_rejects) {
        (false, false) => {
            let (ours, theirs) = (normalise_parse(&parse), normalise_fcs_dump(&json));
            assert_eq!(
                ours, theirs,
                "AST divergence for {source:?}\n  rust: {ours:#?}\n  fcs:  {theirs:#?}",
            );
            Outcome::Accepted
        }
        (false, true) => {
            assert_agree_outside_damage(source, &parse, &json);
            Outcome::OnlyFcsRejects
        }
        (true, true) => {
            assert_agree_outside_damage(source, &parse, &json);
            Outcome::Rejected
        }
        (true, false) => unreachable!("asserted above"),
    }
}

/// Assert that every declaration outside FCS's and our damage agrees, key for
/// key and shape for shape ([`grade`]).
fn assert_agree_outside_damage(source: &str, parse: &borzoi_cst::parser::Parse, json: &str) {
    let verdict = grade(parse, &HashSet::new(), json, source);
    assert!(
        verdict.relation != Relation::Divergent,
        "recovered trees diverge for {source:?}: {}\n{}\n  our errors: {:?}",
        verdict.token(),
        verdict.first_divergence.as_deref().unwrap_or(""),
        parse.errors,
    );
}

/// Grade every cell, collecting (rather than stopping at) divergences, and
/// assert both shared verdicts were exercised.
///
/// `known` lists cells (the declaration, without the module header and the
/// trailing [`AFTER`]) that diverge for a reason outside this grid's subject,
/// as [`Outcome::OnlyFcsRejects`] and in no other way. Each must still diverge, so
/// the list cannot outlive the defect it records.
fn sweep(what: &str, cells: impl IntoIterator<Item = String>, known: &[String]) {
    let mut total = 0;
    let mut accepted = 0;
    let mut rejected = 0;
    let mut known_seen = 0;
    let mut failures = Vec::new();
    let mut known_now_agreeing = Vec::new();
    for body in cells {
        total += 1;
        let is_known = known.contains(&body);
        known_seen += usize::from(is_known);
        let source = format!("module M\n{body}{AFTER}");
        match catch_unwind_silent(|| grade_cell(&source)) {
            Ok(Outcome::OnlyFcsRejects) => {
                if !is_known {
                    failures.push(format!("we accept, FCS rejects: {source:?}"));
                }
            }
            Ok(agrees) => {
                if agrees == Outcome::Accepted {
                    accepted += 1;
                } else {
                    rejected += 1;
                }
                if is_known {
                    known_now_agreeing.push(body);
                }
            }
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
    assert_eq!(
        known_seen,
        known.len(),
        "every known {what} divergence must be a cell of the grid",
    );
    assert!(
        known_now_agreeing.is_empty(),
        "these {what} cells are listed as known divergences but now agree with FCS; \
         remove them from the list:\n{known_now_agreeing:#?}",
    );
    assert!(
        accepted > 0 && rejected > 0,
        "the {what} sweep should both accept and reject, but of {total} cells both \
         parsers accepted {accepted} and both rejected {rejected}",
    );
}

/// Every template with every shape in its hole.
fn cross<'a>(templates: &'a [&str], shapes: &'a [&str]) -> impl Iterator<Item = String> + 'a {
    templates
        .iter()
        .flat_map(move |t| shapes.iter().map(move |s| t.replace(HOLE, s)))
}

/// Brace bodies, with and without a builder in front: a bare long identifier
/// (the shape whose classification looks past the `}`), dotted and
/// `global`-rooted, a sequence, an application, a record and a copy-and-update
/// (whose own `=`/`with` sit inside the brace), each with a trailing separator,
/// and the empty record and copy-and-update, whose field list is empty because
/// the `}` comes first.
const BRACE_SHAPES: &[&str] = &[
    "builder { a }",
    "builder { a.b }",
    "builder { global.a }",
    "builder { a; b }",
    "builder { f x }",
    "builder { A = 1 }",
    "builder { a.B = 1 }",
    "builder { r with A = 1 }",
    "builder { A = 1; }",
    "builder { r with A = 1; }",
    "builder { a; }",
    "builder { }",
    "builder { r with }",
    "seq { a }",
    "{ a }",
    "{ a.b }",
    "{ A = 1 }",
    "{ r with A = 1 }",
    "{ }",
];

/// Where a brace shape sits: followed by an `=` past the closers LexFilter
/// swallows (`}`, and one or two `)`), and, as controls, past the ones it
/// emits (`]`, `|]`, `end`); by a member access before the `=` or `with`; by
/// a `with` that belongs to an enclosing copy-and-update; and by an `=` of
/// the next declaration, with a few controls whose operator is not `=`.
const CONTEXTS: &[&str] = &[
    "let x = @\n",
    "let x = @ = b\n",
    "let x = (@) = b\n",
    "let x = ((@) = b)\n",
    "let x = ((@) = (b))\n",
    "let x = f (@) = b\n",
    "let x = (@, c) = b\n",
    "let x = [@] = b\n",
    "let x = [|@|] = b\n",
    "let x = begin @ end = b\n",
    "let x = ((@)) = b\n",
    "let x = seq { @ = b }\n",
    "let x = seq { yield (@) = b }\n",
    "let x = { R = (@) = b }\n",
    "let x = { r with R = (@) = b }\n",
    "let x = { f (@) with R = 1 }\n",
    "let x = { (@) with R = 1 }\n",
    "let x = (@) <> b\n",
    "let x = (@) b\n",
    "let x = (@).M\n",
    "let x = (@).M = b\n",
    "let x = (@).M.N = b\n",
    "let x = f (@).M = b\n",
    "let x = { (@).M with R = 1 }\n",
    "let x = (@) :: b\n",
    "let x = [@; c] = b\n",
    "let x = (@) == b\n",
    "let x = (@)\nlet y = b\n",
    "let x =\n    (@)\n    = b\n",
];

/// The context whose every cell is a known divergence: each shape is an
/// `appExpr` other than a long identifier, directly followed by the `=`, so
/// FCS shifts the `=` into a record field binding and reports FS0609, while we
/// parse an equality (WoofWare/borzoi#1054).
const KNOWN_CONTEXT: &str = "let x = seq { @ = b }\n";

/// Every brace shape in every context.
#[test]
fn diff_brace_body_followed_by_a_classifying_token() {
    let known: Vec<String> = cross(&[KNOWN_CONTEXT], BRACE_SHAPES).collect();
    sweep("brace-body", cross(CONTEXTS, BRACE_SHAPES), &known);
}
