//! The printer over the corpus: every file lowered to a tree (dropping the
//! declarations the tree does not model), printed, and held to the round-trip
//! property ([`super::check_printed`]).
//!
//! Two results:
//!
//! * **Hard invariant: every tree round-trips.** A file whose tree prints as
//!   text FCS rejects or reads back differently is a printer bug (or a hole in
//!   the tree's types), whatever else the file holds.
//! * **The manifest: how much of each file the tree models, exactly.** One keyed
//!   line per file, `kept=K dropped=D` (declarations, counting a nested module's
//!   own declarations rather than the module), or why the file has no tree
//!   (a signature file, a parse error) or no grade (`fcs-error`: fcs-dump
//!   cannot serialise the parse of a stress test this deep). Modelling more of F# moves lines, and
//!   the regenerated manifest shows which files gained; losing coverage moves
//!   them back, visibly.
//!
//! The decline census it prints (not pinned) ranks what to model next.

use std::collections::BTreeMap;

use borzoi_oracle_harness::manifest::Manifest;
use borzoi_print::print_impl_file;
use borzoi_print::version::DefaultVersion;

use super::lower::{Decline, lower_file_lossy};
use super::{CheckFailure, check_printed, panic_message};
use crate::common::corpus_manifest::{
    check_manifest, corpus_relative, regenerate_ignored, sort_by_corpus_key,
};
use crate::common::normalised_ast::normalise_parse;
use crate::common::{
    catch_unwind_silent, collect_fsharp_corpus_files, corpus_root, par_map, read_corpus_source,
};

enum Outcome {
    /// Why the file has no tree at all.
    Skipped(&'static str),
    /// The file's tree round-tripped.
    RoundTripped { kept: usize, dropped: Vec<Decline> },
    /// The file's tree did not round-trip: a printer bug.
    Failed(String),
}

fn sweep_file(path: &std::path::Path) -> Outcome {
    let src = match read_corpus_source(path) {
        Ok(src) => src,
        Err(err) if err.is_non_utf8() => return Outcome::Skipped("non-utf8"),
        Err(err) => panic!("{err}"),
    };
    if path.extension().and_then(|e| e.to_str()) == Some("fsi") {
        return Outcome::Skipped("signature file");
    }
    let parse = borzoi_cst::parser::parse(&src);
    if !parse.errors.is_empty() {
        return Outcome::Skipped("parse errors");
    }
    let Ok(root) = catch_unwind_silent(|| normalise_parse(&parse)) else {
        return Outcome::Skipped("not normalisable");
    };
    let (tree, tally) = match lower_file_lossy::<DefaultVersion>(&root) {
        Ok(lowered) => lowered,
        Err(Decline(why)) => return Outcome::Skipped(why),
    };
    let printed = print_impl_file(&tree);
    match catch_unwind_silent(|| check_printed(&printed, &tree)) {
        Ok(Ok(())) => Outcome::RoundTripped {
            kept: tally.kept,
            dropped: tally.dropped,
        },
        // fcs-dump could not grade the text; `parser_corpus_diff` buckets the
        // same files' sources the same way.
        Ok(Err(CheckFailure::FcsError(_))) => Outcome::Skipped("fcs-error"),
        Ok(Err(why)) => Outcome::Failed(format!("{why}\n--- printed ---\n{printed}--- end ---")),
        Err(payload) => {
            Outcome::Failed(format!("the check panicked: {}", panic_message(&*payload)))
        }
    }
}

#[test]
#[ignore = "full-corpus print round trip (~30 s); run with --ignored under nix develop"]
fn every_corpus_tree_round_trips() {
    let root = corpus_root();
    let mut files = collect_fsharp_corpus_files(&root)
        .unwrap_or_else(|err| panic!("walk F# corpus under {}: {err}", root.display()));
    assert!(!files.is_empty(), "no F# files under {root:?}");
    sort_by_corpus_key(&root, &mut files);

    let outcomes = par_map(files.len(), |i| sweep_file(&files[i]));

    let mut entries = Vec::new();
    let mut failures = Vec::new();
    let mut census: BTreeMap<&'static str, usize> = BTreeMap::new();
    let (mut kept_total, mut dropped_total) = (0, 0);
    for (path, outcome) in files.iter().zip(outcomes) {
        let key = corpus_relative(&root, path);
        let verdict = match outcome {
            Outcome::Skipped(why) => why.to_owned(),
            Outcome::RoundTripped { kept, dropped } => {
                kept_total += kept;
                dropped_total += dropped.len();
                for Decline(why) in &dropped {
                    *census.entry(why).or_default() += 1;
                }
                format!("kept={kept} dropped={}", dropped.len())
            }
            Outcome::Failed(why) => {
                failures.push(format!("{key}: {why}"));
                continue;
            }
        };
        entries.push((key, verdict));
    }

    let mut ranked: Vec<_> = census.into_iter().collect();
    ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
    eprintln!(
        "{} files | {kept_total} declarations printed and round-tripped | {dropped_total} dropped",
        files.len()
    );
    eprintln!("dropped declarations by reason:");
    for (why, n) in &ranked {
        eprintln!("  {n:>6}  {why}");
    }

    assert!(
        failures.is_empty(),
        "{} corpus trees did not round-trip:\n{}",
        failures.len(),
        failures
            .iter()
            .take(5)
            .map(String::as_str)
            .collect::<Vec<_>>()
            .join("\n\n")
    );
    let manifest = Manifest::from_keyed(entries).unwrap_or_else(|e| panic!("manifest entry: {e}"));
    check_manifest(
        "print_roundtrip_corpus",
        &manifest,
        &regenerate_ignored("print_roundtrip::corpus"),
    );
}
