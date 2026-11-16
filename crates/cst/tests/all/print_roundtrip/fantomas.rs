//! The printer over the F# held in Fantomas's tests: odd code collected by a
//! formatter's maintainers, kept as string literals (each test's input and
//! expected output). Every string literal in `src/Fantomas.Core.Tests` that our
//! parser parses cleanly is a source; each is lowered, printed and held to the
//! round-trip property as the corpus files are ([`super::corpus`]).
//!
//! Fantomas is not a pinned input, so this reads a checkout named by
//! `BORZOI_FANTOMAS_SRC`, asserts only that every tree round-trips, and pins
//! nothing:
//!
//! ```text
//! BORZOI_FANTOMAS_SRC=~/src/fantomas nix develop -c cargo test -p borzoi-cst \
//!   --test all print_roundtrip::fantomas:: -- --ignored --nocapture
//! ```

use std::collections::BTreeSet;

use borzoi_cst::syntax::{NodeOrToken, SyntaxKind};
use borzoi_print::print_impl_file;

use super::check_printed;
use super::lower::lower_file_lossy;
use crate::common::normalised_ast::{NormalisedConst, normalise_const_lit, normalise_parse};
use crate::common::{
    catch_unwind_silent, collect_fsharp_corpus_files, par_map, read_corpus_source,
};

/// Every string literal's value in `src`.
fn string_literals(src: &str) -> Vec<String> {
    let parse = borzoi_cst::parser::parse(src);
    parse
        .root
        .descendants_with_tokens()
        .filter_map(NodeOrToken::into_token)
        .filter(|t| {
            matches!(
                t.kind(),
                SyntaxKind::STRING_LIT
                    | SyntaxKind::VERBATIM_STRING_LIT
                    | SyntaxKind::TRIPLE_STRING_LIT
            )
        })
        .filter_map(|t| match normalise_const_lit(&t) {
            NormalisedConst::String { value, .. } => String::from_utf16(&value).ok(),
            _ => None,
        })
        .collect()
}

#[test]
#[ignore = "reads a Fantomas checkout named by BORZOI_FANTOMAS_SRC"]
fn every_fantomas_test_source_round_trips() {
    let root = std::path::PathBuf::from(
        std::env::var("BORZOI_FANTOMAS_SRC")
            .expect("BORZOI_FANTOMAS_SRC names a Fantomas checkout"),
    );
    let tests = root.join("src/Fantomas.Core.Tests");
    let files = collect_fsharp_corpus_files(&tests)
        .unwrap_or_else(|err| panic!("walk {}: {err}", tests.display()));
    assert!(!files.is_empty(), "no test files under {}", tests.display());
    let sources: BTreeSet<String> = files
        .iter()
        .flat_map(|path| {
            let src = read_corpus_source(path).unwrap_or_else(|err| panic!("{err}"));
            string_literals(&src)
        })
        .collect();
    let sources: Vec<String> = sources.into_iter().collect();

    // `None` for a literal that is not clean F#, else what round-tripping its
    // tree found.
    let outcomes = par_map(sources.len(), |i| {
        let src = &sources[i];
        let parse = borzoi_cst::parser::parse(src);
        if !parse.errors.is_empty() {
            return None;
        }
        let root = catch_unwind_silent(|| normalise_parse(&parse)).ok()?;
        let (tree, tally) = lower_file_lossy(&root).ok()?;
        let printed = print_impl_file(&tree);
        let verdict = match catch_unwind_silent(|| check_printed(&printed, &tree)) {
            Ok(Ok(())) => Ok(tally.kept),
            Ok(Err(why)) => Err(format!(
                "--- source ---\n{src}\n{why}\n--- printed ---\n{printed}--- end ---"
            )),
            Err(payload) => Err(format!(
                "--- source ---\n{src}\nthe check panicked: {}",
                super::panic_message(&*payload)
            )),
        };
        Some(verdict)
    });

    let mut failures = Vec::new();
    let (mut clean, mut kept) = (0, 0);
    for outcome in outcomes.into_iter().flatten() {
        clean += 1;
        match outcome {
            Ok(k) => kept += k,
            Err(why) => failures.push(why),
        }
    }
    eprintln!(
        "{} string literals | {clean} parse as F# | {kept} declarations printed and round-tripped",
        sources.len()
    );
    assert!(clean > 1000, "too few sources parsed: {clean}");
    assert!(
        failures.is_empty(),
        "{} Fantomas sources did not round-trip:\n{}",
        failures.len(),
        failures
            .iter()
            .take(5)
            .map(String::as_str)
            .collect::<Vec<_>>()
            .join("\n\n")
    );
}
