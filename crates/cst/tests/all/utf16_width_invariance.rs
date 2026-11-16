//! Metamorphic property of the lex filter: its layout decisions see columns
//! in UTF-16 code units, FCS's scale, so they cannot move when a character is
//! respelled at the same UTF-16 width but a different UTF-8 width.
//!
//! Every identifier in a file whose last character is an ASCII lowercase
//! letter has that letter respelled `é`: one UTF-16 unit, as before, but two
//! bytes rather than one. Every column FCS would compute is unchanged, and so
//! is every token's kind. The filter reads no identifier's text, so its whole
//! output must be the same: each filtered token's kind and (mapped through the
//! respelling) span, the virtual tokens included, and each offside diagnostic,
//! whose message embeds a column. A filter that measured anything in bytes
//! would move a token that follows a respelled identifier on its line, which
//! in real code is nearly every token a context is anchored at.
//!
//! [`parser_diff_offside_utf16_grid`](crate::parser_diff_offside_utf16_grid)
//! grades the same scale against FCS on chosen shapes; this needs no oracle,
//! so it runs over the corpus at both ends of the language-version range,
//! whose offside rules differ.

use std::collections::HashSet;
use std::path::Path;

use borzoi_cst::language_version::LanguageVersion;
use borzoi_cst::lexer::TokenKind;
use borzoi_cst::lexfilter::filter_collect;
use borzoi_cst::tokens::{RawKind, lex_full_trivia_at};

use crate::common::{collect_fsharp_corpus_files, corpus_root, par_map, read_corpus_source};

const VERSIONS: [LanguageVersion; 2] = [LanguageVersion::MIN, LanguageVersion::MAX];

/// `source` with the last letter of each identifier ending in an ASCII
/// lowercase one respelled `é`, and the byte offset of each respelling's end
/// in `source`, ascending.
fn respell(source: &str, lang: LanguageVersion) -> (String, Vec<usize>) {
    let lexed = lex_full_trivia_at(source, &HashSet::new(), lang);
    let raw = &lexed.tokens;
    let mut out = String::with_capacity(source.len() + source.len() / 8);
    let mut ends = Vec::new();
    let mut copied = 0;
    for i in 0..raw.len() {
        if raw.kind(i) != RawKind::Lexed(TokenKind::Ident) {
            continue;
        }
        let span = raw.span(i);
        if !source.as_bytes()[span.end - 1].is_ascii_lowercase() {
            continue;
        }
        out.push_str(&source[copied..span.end - 1]);
        out.push('é');
        copied = span.end;
        ends.push(span.end);
    }
    out.push_str(&source[copied..]);
    (out, ends)
}

/// Where byte `offset` of the original lands in the respelling: one byte
/// further on for each respelled letter that ends at or before it.
fn shift(ends: &[usize], offset: usize) -> usize {
    offset + ends.partition_point(|&end| end <= offset)
}

/// Every way the filter's output on the respelling of `source` differs from
/// its output on `source`, at `lang`.
fn differences(source: &str, lang: LanguageVersion) -> Vec<String> {
    let (respelled, ends) = respell(source, lang);
    if ends.is_empty() {
        return Vec::new();
    }
    let symbols = HashSet::new();
    let before_lexed = lex_full_trivia_at(source, &symbols, lang);
    let after_lexed = lex_full_trivia_at(&respelled, &symbols, lang);
    let before = filter_collect(&before_lexed.tokens, lang);
    let after = filter_collect(&after_lexed.tokens, lang);
    let mut out = Vec::new();
    let tokens = |run: &borzoi_cst::lexfilter::FilterRun<'_>, map: &dyn Fn(usize) -> usize| {
        (0..run.tokens.len())
            .map(|i| {
                let span = run.tokens.span(i);
                (run.tokens.kind(i), map(span.start)..map(span.end))
            })
            .collect::<Vec<_>>()
    };
    let expected = tokens(&before, &|o| shift(&ends, o));
    let actual = tokens(&after, &|o| o);
    if let Some(i) =
        (0..expected.len().max(actual.len())).find(|&i| expected.get(i) != actual.get(i))
    {
        out.push(format!(
            "filtered token {i}: expected {:?}, got {:?}",
            expected.get(i),
            actual.get(i)
        ));
    }
    let diagnostics = |run: &borzoi_cst::lexfilter::FilterRun<'_>, map: &dyn Fn(usize) -> usize| {
        run.diagnostics
            .iter()
            .map(|d| {
                (
                    map(d.span.start)..map(d.span.end),
                    d.message.clone(),
                    d.severity,
                )
            })
            .collect::<Vec<_>>()
    };
    let expected = diagnostics(&before, &|o| shift(&ends, o));
    let actual = diagnostics(&after, &|o| o);
    if expected != actual {
        out.push(format!(
            "offside diagnostics: expected {expected:?}, got {actual:?}"
        ));
    }
    out
}

/// Every `step`th corpus file, at each of [`VERSIONS`]: no file's filter
/// output may move under the respelling, and some respelling must have been
/// made.
fn corpus_holds(step: usize) {
    let root = corpus_root();
    let files = collect_fsharp_corpus_files(&root).expect("walk the corpus");
    let picked: Vec<&Path> = files.iter().step_by(step).map(|p| p.as_path()).collect();
    let results: Vec<(usize, Vec<String>)> = par_map(picked.len(), |i| {
        let path = picked[i];
        let Ok(source) = read_corpus_source(path) else {
            return (0, Vec::new());
        };
        let mut respelled = 0;
        let mut failures = Vec::new();
        for lang in VERSIONS {
            respelled += respell(&source, lang).1.len();
            for difference in differences(&source, lang) {
                failures.push(format!("{} at {lang}: {difference}", path.display()));
            }
        }
        (respelled, failures)
    });
    let respelled: usize = results.iter().map(|(n, _)| n).sum();
    let failures: Vec<&String> = results.iter().flat_map(|(_, f)| f).collect();
    assert!(
        failures.is_empty(),
        "the filter's output moved in {} places when identifiers were respelled at \
         the same UTF-16 width:\n{}",
        failures.len(),
        failures
            .iter()
            .take(50)
            .map(|f| f.as_str())
            .collect::<Vec<_>>()
            .join("\n"),
    );
    assert!(respelled > 0, "no identifier in the corpus was respelled");
}

/// The respelling and the shift agree: the respelled text is the original
/// with each respelled letter replaced, so every unrespelled byte lands where
/// [`shift`] says.
#[test]
fn the_respelling_moves_bytes_where_the_shift_says() {
    let source = "let foo x = (bar x)\n  |> baz' 1 // qux\n";
    let (respelled, ends) = respell(source, LanguageVersion::DEFAULT);
    assert_eq!(respelled, "let foé é = (baé é)\n  |> baz' 1 // qux\n");
    for (offset, byte) in source.bytes().enumerate() {
        if !ends.contains(&(offset + 1)) {
            assert_eq!(
                respelled.as_bytes()[shift(&ends, offset)],
                byte,
                "byte {offset}"
            );
        }
    }
}

/// A sample of the corpus, in the normal suite.
#[test]
fn corpus_sample_is_width_invariant() {
    corpus_holds(20);
}

/// The whole corpus. Ignored: it lexes and filters every file four times.
#[test]
#[ignore]
fn corpus() {
    corpus_holds(1);
}
