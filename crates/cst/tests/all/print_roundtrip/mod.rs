//! The correctness oracle for `borzoi-print`'s reference printer.
//!
//! The property: for a tree `t` targeting F# version `V`, FCS at `V` parses
//! the text `print(t)` with no diagnostic at all, and its parse lowers back to
//! `t` exactly. A generated tree is checked at `preview` too, as every later
//! version must read it the same way; and each gated construct is checked
//! against the version below its gate, where FCS must reject it ([`gates`]).
//! FCS is the authority on what the text means, read in the normalised currency
//! the parser differential compares in. A printer bug that FCS reads differently from the
//! tree, or rejects, fails here; so does a value the tree's types admit that F#
//! cannot express, which is a hole in the types.
//!
//! Every printed text is also a parser differential for free: our parser must
//! parse it cleanly to the same normalised tree. One refusal of ours is
//! exempt, by design: past `MAX_TREE_HEIGHT` our parser stops rather than risk
//! its stack, and the printer's parentheses roughly double a tree's height,
//! which the corpus's stress tests (`LargeSequential-500.fs`) cross.
//!
//! The trees come from two places: a generator over the tree's whole surface
//! at every version ([`generate`]), and every corpus file, lowered with the
//! declarations the tree does not model dropped ([`lower`]) at the version a
//! project without `<LangVersion>` gets.

mod corpus;
mod fantomas;
mod gates;
mod generate;
mod lower;
mod names;
mod statements;

use std::collections::HashSet;
use std::io::Write as _;

use borzoi_cst::parser::{FileKind, ParseOptions, parse_with_options};
use borzoi_print::print_impl_file;
use borzoi_print::tree::ImplFile;
use borzoi_print::version::{LanguageVersion, Version};

use crate::common::normalised_ast::{normalise_fcs_dump, normalise_parse};
use crate::common::{fcs_all_diagnostics, fcs_ast_batch_at, fcs_parse_had_errors};

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

/// `source` in a temporary `.fs` file and FCS's `ast-batch` record of it at
/// `lang`.
fn fcs_record_at(source: &str, lang: LanguageVersion) -> String {
    // An anonymous module takes its name from the file's, which must be an
    // identifier or FCS warns.
    let mut tmp = tempfile::Builder::new()
        .prefix("Printed")
        .suffix(".fs")
        .tempfile()
        .expect("create tempfile");
    tmp.write_all(source.as_bytes()).expect("write source");
    fcs_ast_batch_at(tmp.path(), &lang.to_string())
}

/// Check `printed`, the printing of `tree`, against the property at the
/// tree's own version.
fn check_printed<V: Version>(printed: &str, tree: &ImplFile<V>) -> Result<(), CheckFailure> {
    check_printed_at(printed, tree, V::LANGUAGE)
}

/// Check `printed`, the printing of `tree`, against the property at `lang`, a
/// version no older than the tree's.
fn check_printed_at<V: Version>(
    printed: &str,
    tree: &ImplFile<V>,
    lang: LanguageVersion,
) -> Result<(), CheckFailure> {
    assert!(
        lang >= V::LANGUAGE,
        "{lang} is older than the tree's version"
    );
    let json = fcs_record_at(printed, lang);
    if let Ok(FcsErrorRecord { error: Some(e) }) = serde_json::from_str(&json) {
        return Err(CheckFailure::FcsError(e));
    }
    let diagnostics = fcs_all_diagnostics(&json, printed);
    if fcs_parse_had_errors(&json) || !diagnostics.is_empty() {
        return failed(format!("FCS diagnostics at {lang}: {diagnostics:?}"));
    }
    let fcs = normalise_fcs_dump(&json);
    match lower::lower_file_strict::<V>(&fcs) {
        Err(d) => {
            return failed(format!(
                "FCS's parse at {lang} does not lower: {d:?}\n  parse: {fcs:?}"
            ));
        }
        Ok(back) if back != *tree => {
            return failed(format!(
                "FCS's parse at {lang} lowers to a different tree\n  printed: {tree:?}\n  read:    {back:?}"
            ));
        }
        Ok(_) => {}
    }
    let parse = parse_with_options(
        printed,
        ParseOptions {
            file_kind: FileKind::Impl,
            symbols: &HashSet::new(),
            lang,
        },
    );
    if let [only] = parse.errors.as_slice()
        && only.message == "nesting is too deep; parsing stopped here"
    {
        return Ok(());
    }
    if !parse.errors.is_empty() {
        return failed(format!(
            "our parser's diagnostics at {lang}: {:?}",
            parse.errors
        ));
    }
    let ours = normalise_parse(&parse);
    if ours != fcs {
        return failed(format!(
            "our parse and FCS's differ at {lang}\n  ours: {ours:?}\n  fcs:  {fcs:?}"
        ));
    }
    Ok(())
}

/// A caught panic's message.
fn panic_message(payload: &(dyn std::any::Any + Send)) -> &str {
    payload
        .downcast_ref::<&str>()
        .copied()
        .or_else(|| payload.downcast_ref::<String>().map(String::as_str))
        .unwrap_or("(not a string)")
}

/// Print `tree` and check it at each of `langs`, describing the failure with
/// the printed text.
fn round_trips_at<V: Version>(tree: &ImplFile<V>, langs: &[LanguageVersion]) -> Result<(), String> {
    let printed = print_impl_file(tree);
    langs
        .iter()
        .try_for_each(|&lang| check_printed_at(&printed, tree, lang))
        .map_err(|why| format!("{why}\n--- printed ---\n{printed}--- end ---"))
}

/// Print `tree` and check it at its own version.
fn round_trips<V: Version>(tree: &ImplFile<V>) -> Result<(), String> {
    round_trips_at(tree, &[V::LANGUAGE])
}

mod generated {
    use borzoi_print::version::{
        LanguageVersion, Preview, V4_6, V4_7, V5_0, V6_0, V7_0, V8_0, V9_0, V10_0, V11_0, Version,
    };
    use proptest::prelude::*;

    use super::{generate, round_trips_at};

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

    /// A tree at `V`, checked at `V` and at the newest version, `preview`:
    /// every version from `V` on must read it the same way, and each gate is a
    /// threshold, so the two ends stand for the range.
    fn check<V: Version>(file: &borzoi_print::tree::ImplFile<V>) -> Result<(), TestCaseError> {
        round_trips_at(file, &[V::LANGUAGE, LanguageVersion::MAX]).map_err(TestCaseError::fail)
    }

    /// One module per version, each with the normal run and its deep twin.
    macro_rules! per_version {
        ($($module:ident: $version:ty;)*) => {$(
            mod $module {
                use super::*;

                proptest! {
                    #![proptest_config(config(32))]
                    #[test]
                    fn every_generated_file_round_trips(
                        file in generate::impl_file::<$version>()
                    ) {
                        check(&file)?;
                    }
                }

                proptest! {
                    #![proptest_config(config(512))]
                    #[test]
                    #[ignore = "deep twin of every_generated_file_round_trips"]
                    fn deep_every_generated_file_round_trips(
                        file in generate::impl_file::<$version>()
                    ) {
                        check(&file)?;
                    }
                }
            }
        )*};
    }

    per_version! {
        v4_6: V4_6;
        v4_7: V4_7;
        v5_0: V5_0;
        v6_0: V6_0;
        v7_0: V7_0;
        v8_0: V8_0;
        v9_0: V9_0;
        v10_0: V10_0;
        v11_0: V11_0;
        preview: Preview;
    }
}
