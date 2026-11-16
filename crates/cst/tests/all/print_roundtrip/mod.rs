//! The correctness oracle for `borzoi-print`'s reference printer.
//!
//! The property: for a tree `t`, FCS parses the text `print(t)` with no
//! diagnostic at all, and its parse lowers back to `t` exactly. FCS is the
//! authority on what the text means, read in the normalised currency the parser
//! differential compares in. A printer bug that FCS reads differently from the
//! tree, or rejects, fails here; so does a value the tree's types admit that F#
//! cannot express, which is a hole in the types.
//!
//! Every printed text is also a parser differential for free: our parser must
//! parse it cleanly to the same normalised tree. Two refusals of ours are
//! exempt. One is by design: past `MAX_TREE_HEIGHT` our parser stops rather
//! than risk its stack, and the printer's parentheses roughly double a tree's
//! height, which the corpus's stress tests (`LargeSequential-500.fs`) cross.
//! The other is the known divergence #947 (our offside rule counts byte
//! columns where FCS counts UTF-16 ones), in exactly the shape the printer
//! produces it ([`hits_issue_947`]).
//!
//! The trees come from two places: a generator over the tree's whole surface
//! ([`generate`]), and every corpus file, lowered with the declarations the
//! tree does not model dropped ([`lower`]).

mod corpus;
mod fantomas;
mod generate;
mod lower;
mod names;

use std::io::Write as _;

use borzoi_print::print_impl_file;
use borzoi_print::tree::ImplFile;

use crate::common::normalised_ast::{normalise_fcs_dump, normalise_parse};
use crate::common::{fcs_all_diagnostics, fcs_ast_batch, fcs_parse_had_errors};

/// Why [`check_printed`] did not pass.
#[derive(Debug)]
enum CheckFailure {
    /// fcs-dump answered with an error record instead of a parse, so nothing
    /// was graded: its JSON writer cannot serialise a tree deeper than its
    /// depth limit, which the corpus's stress tests reach.
    FcsError(String),
    /// The property does not hold.
    Failed(String),
}

impl std::fmt::Display for CheckFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CheckFailure::FcsError(e) => write!(f, "fcs-dump failed: {e}"),
            CheckFailure::Failed(why) => f.write_str(why),
        }
    }
}

/// The error field of an `ast-batch` record that has one.
#[derive(serde::Deserialize)]
struct FcsErrorRecord {
    #[serde(rename = "Error")]
    error: Option<String>,
}

fn failed<T>(why: String) -> Result<T, CheckFailure> {
    Err(CheckFailure::Failed(why))
}

/// Check `printed`, the printing of `tree`, against the property.
fn check_printed(printed: &str, tree: &ImplFile) -> Result<(), CheckFailure> {
    // An anonymous module takes its name from the file's, which must be an
    // identifier or FCS warns.
    let mut tmp = tempfile::Builder::new()
        .prefix("Printed")
        .suffix(".fs")
        .tempfile()
        .expect("create tempfile");
    tmp.write_all(printed.as_bytes()).expect("write source");
    let json = fcs_ast_batch(tmp.path());
    if let Ok(FcsErrorRecord { error: Some(e) }) = serde_json::from_str(&json) {
        return Err(CheckFailure::FcsError(e));
    }
    let diagnostics = fcs_all_diagnostics(&json, printed);
    if fcs_parse_had_errors(&json) || !diagnostics.is_empty() {
        return failed(format!("FCS diagnostics: {diagnostics:?}"));
    }
    let fcs = normalise_fcs_dump(&json);
    match lower::lower_file_strict(&fcs) {
        Err(d) => {
            return failed(format!(
                "FCS's parse does not lower: {d:?}\n  parse: {fcs:?}"
            ));
        }
        Ok(back) if back != *tree => {
            return failed(format!(
                "FCS's parse lowers to a different tree\n  printed: {tree:?}\n  read:    {back:?}"
            ));
        }
        Ok(_) => {}
    }
    if hits_issue_947(printed) {
        return Ok(());
    }
    let parse = borzoi_cst::parser::parse(printed);
    if let [only] = parse.errors.as_slice()
        && only.message == "nesting is too deep; parsing stopped here"
    {
        return Ok(());
    }
    if !parse.errors.is_empty() {
        return failed(format!("our parser's diagnostics: {:?}", parse.errors));
    }
    let ours = normalise_parse(&parse);
    if ours != fcs {
        return failed(format!(
            "our parse and FCS's differ\n  ours: {ours:?}\n  fcs:  {fcs:?}"
        ));
    }
    Ok(())
}

/// Whether `printed` has a `let rec … and …` group whose `let` follows a
/// non-ASCII character on its line: the `and` aligns with the `let`'s UTF-16
/// column, which our offside rule measures in bytes (#947), so our parser
/// rejects text FCS accepts. Delete this once #947 is fixed.
fn hits_issue_947(printed: &str) -> bool {
    let lines: Vec<&str> = printed.lines().collect();
    lines.iter().enumerate().any(|(i, line)| {
        let rest = line.trim_start_matches(' ');
        let column = line.len() - rest.len();
        rest.starts_with("and ")
            && lines[..i].iter().rev().any(|earlier| {
                let mut units = 0;
                for (byte, ch) in earlier.char_indices() {
                    if units == column {
                        return !earlier.is_char_boundary(byte)
                            || (earlier[byte..].starts_with("let rec")
                                && !earlier[..byte].is_ascii());
                    }
                    units += ch.len_utf16();
                }
                false
            })
    })
}

/// A caught panic's message.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> &str {
    payload
        .downcast_ref::<&str>()
        .copied()
        .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
        .unwrap_or("(not a string)")
}

/// Print `tree` and check it, describing the failure with the printed text.
fn round_trips(tree: &ImplFile) -> Result<(), String> {
    let printed = print_impl_file(tree);
    check_printed(&printed, tree)
        .map_err(|why| format!("{why}\n--- printed ---\n{printed}--- end ---"))
}

mod generated {
    use proptest::prelude::*;

    use super::{generate, round_trips};

    /// `default` cases per run, or `BORZOI_PRINT_CASES`. The leaves filter
    /// candidate names through the names' constructors, and a run draws
    /// hundreds per case, so proptest's run-wide cap on filter rejections is
    /// lifted: a rejection costs nothing, and the leaves accept most draws.
    fn config(default: u32) -> ProptestConfig {
        ProptestConfig {
            cases: std::env::var("BORZOI_PRINT_CASES")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(default),
            max_local_rejects: u32::MAX,
            ..ProptestConfig::default()
        }
    }

    proptest! {
        #![proptest_config(config(256))]
        #[test]
        fn every_generated_file_round_trips(file in generate::impl_file()) {
            round_trips(&file).map_err(TestCaseError::fail)?;
        }
    }

    proptest! {
        #![proptest_config(config(4096))]
        #[test]
        #[ignore = "deep twin of every_generated_file_round_trips"]
        fn deep_every_generated_file_round_trips(file in generate::impl_file()) {
            round_trips(&file).map_err(TestCaseError::fail)?;
        }
    }
}
