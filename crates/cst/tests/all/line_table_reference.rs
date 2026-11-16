//! The newline table (`borzoi_cst::tokens::LineStarts`) against the byte
//! rescan it replaces (`docs/token-pipeline-soa-plan.md`, D3).
//!
//! The lex-filter needs the line and column of every token boundary it pulls.
//! It walks a forward cursor over a table of line starts computed once per
//! source. A rescan of the bytes before each boundary is the reference: for
//! every character boundary, the cursor must give the line and column the
//! rescan gives, whichever offsets the cursor visited on the way, and the
//! table must map that position back to the offset. Line breaks are FCS's: a
//! `\n` (so `\r\n` is one break and a lone `\r` none), wherever it sits, inside
//! a comment, a string or inactive code included. Columns are FCS's too: UTF-16
//! code units, so a character outside the Basic Multilingual Plane counts two.
//! A file-start BOM does not count towards line 1's columns.
//!
//! How the filter uses the cursor (where virtual tokens go, what the FS0058
//! messages say) is graded against FCS by the lex-filter differential, and
//! `filtered_table` draws on [`NEWLINE_SHAPES`] too.

use std::collections::HashSet;

use borzoi_cst::tokens::{LinePos, LineStarts, lex_full_trivia};
use proptest::prelude::*;

use crate::parser_panic_sweep::WIDE;
use crate::token_table_reference::LEXICAL;

/// Line breaks inside the tokens and regions the lexer does not split at them:
/// block comments, each string form, a `#if` region (inactive without `X`),
/// each with both break spellings and a lone `\r`, and multi-byte characters
/// beside them.
pub(crate) const NEWLINE_SHAPES: &[&str] = &[
    "(* a\nb *)",
    "(* a\r\nb *)",
    "(* a\rb *)",
    "\"a\nb\"",
    "\"a\r\nb\"",
    "@\"é\n😃\"",
    "\"\"\"a\nb\r\nc\"\"\"",
    "$\"a\n{1}\nb\"",
    "#if X\nlet y =\n  2\r\n#endif\n",
    "#if X\n(* é\n *)\n#else\n\"\n\"\n#endif\n",
    "x\r\n  y",
    "x\r  y",
    "é\n😃",
    "中𝔸 x\n 𝔸",
];

/// The reference: the position of `offset`, a character boundary, from a
/// rescan of every byte before it.
fn rescan(source: &str, offset: usize) -> LinePos {
    let before = &source.as_bytes()[..offset];
    let breaks = before.iter().filter(|&&b| b == b'\n').count();
    let line_start = match before.iter().rposition(|&b| b == b'\n') {
        Some(i) => i + 1,
        None if source.starts_with('\u{FEFF}') => '\u{FEFF}'.len_utf8(),
        None => 0,
    };
    LinePos {
        line: u32::try_from(1 + breaks).unwrap(),
        col: u32::try_from(
            source[line_start.min(offset)..offset]
                .encode_utf16()
                .count(),
        )
        .unwrap(),
    }
}

/// Advance a fresh cursor over `offsets` (ascending character boundaries),
/// checking each position against the rescan and the table's way back to the
/// offset. Offset 0 of a source with a file-start BOM shares its position
/// with the BOM's end, which is where the way back goes.
fn check_walk(source: &str, table: &LineStarts, offsets: impl IntoIterator<Item = usize>) {
    let bom_end = if source.starts_with('\u{FEFF}') {
        '\u{FEFF}'.len_utf8()
    } else {
        0
    };
    let mut cursor = table.cursor();
    for offset in offsets {
        let pos = cursor.advance_to(offset);
        assert_eq!(
            pos,
            rescan(source, offset),
            "at byte {offset} of {source:?}"
        );
        assert_eq!(
            table.byte_offset(pos),
            offset.max(bom_end),
            "{pos:?} of {source:?}"
        );
    }
}

/// The character boundaries of `source`, its end included.
fn boundaries(source: &str) -> impl Iterator<Item = usize> + '_ {
    (0..=source.len()).filter(|&i| source.is_char_boundary(i))
}

/// Hold the table of `source` to the rescan: its line starts, and a cursor
/// over every offset in turn, over every jump from one offset to the end,
/// and over the token boundaries the filter visits (each token's start and
/// end, under symbol sets that make the `#if` arms active and inactive).
fn check(source: &str) {
    let table = LineStarts::new(source);
    let breaks: Vec<usize> = source
        .bytes()
        .enumerate()
        .filter(|&(_, b)| b == b'\n')
        .map(|(i, _)| i + 1)
        .collect();
    assert_eq!(table.line_count(), 1 + breaks.len(), "{source:?}");
    for (line, &start) in (2..).zip(&breaks) {
        assert_eq!(table.line_start(line), start, "line {line} of {source:?}");
    }
    let first = if source.starts_with('\u{FEFF}') {
        '\u{FEFF}'.len_utf8()
    } else {
        0
    };
    assert_eq!(table.line_start(1), first, "line 1 of {source:?}");
    check_walk(source, &table, boundaries(source));
    for from in boundaries(source) {
        check_walk(source, &table, [from, source.len()]);
    }
    for symbols in [HashSet::new(), HashSet::from(["X".to_string()])] {
        let lexed = lex_full_trivia(source, &symbols);
        let boundaries = (0..lexed.tokens.len()).flat_map(|i| {
            let span = lexed.tokens.span(i);
            [span.start, span.end]
        });
        check_walk(source, &table, boundaries.chain([source.len()]));
    }
}

/// Every one- and two-piece source over the lexical alphabet and the line
/// break shapes.
#[test]
fn every_lexical_pair_matches_the_rescan() {
    for a in LEXICAL.iter().chain(NEWLINE_SHAPES) {
        check(a);
        for b in LEXICAL.iter().chain(NEWLINE_SHAPES) {
            check(&format!("{a}{b}"));
        }
    }
}

/// Every placement of one `\n`, and of two, in sources up to a few hundred
/// bytes, so the table's scan sees a break at every offset of a chunk, at
/// either end of one, in its tail and across two, whatever chunk width it
/// uses.
#[test]
fn every_break_placement_matches_the_rescan() {
    for len in (0..=70).chain([127, 128, 129, 255, 256, 257]) {
        for i in 0..len {
            let mut bytes = vec![b'a'; len];
            bytes[i] = b'\n';
            check(std::str::from_utf8(&bytes).unwrap());
            for j in i + 1..len.min(i + 70) {
                let mut bytes = bytes.clone();
                bytes[j] = if j % 3 == 0 { b'\r' } else { b'\n' };
                let source = std::str::from_utf8(&bytes).unwrap();
                let table = LineStarts::new(source);
                check_walk(source, &table, 0..=len);
            }
        }
    }
}

/// A non-ASCII character of each width at every offset of sources either
/// side of a chunk's width or two, alone and with a break straight after it,
/// so the scan for non-ASCII characters sees one at every offset of a chunk,
/// in its tail and straddling two.
#[test]
fn every_wide_character_placement_matches_the_rescan() {
    for len in (0..=40).chain([63, 64, 65, 95, 96, 97]) {
        for i in 0..=len {
            for wide in ["é", "中", "𝔸"] {
                for after in ["", "\n"] {
                    let source = format!("{}{wide}{after}{}", "a".repeat(i), "a".repeat(len - i));
                    check(&source);
                }
            }
        }
    }
}

#[test]
fn the_empty_source_has_one_line() {
    check("");
    assert_eq!(LineStarts::new("").line_count(), 1);
}

/// A file-start BOM moves line 1's start past it; one elsewhere is an
/// ordinary character.
#[test]
fn a_file_start_bom_starts_line_one_after_it() {
    let table = LineStarts::new("\u{FEFF}x\n\u{FEFF}y");
    assert_eq!(table.line_start(1), 3);
    assert_eq!(table.line_start(2), 5);
    let mut cursor = table.cursor();
    assert_eq!(cursor.advance_to(0), LinePos { line: 1, col: 0 });
    assert_eq!(cursor.advance_to(4), LinePos { line: 1, col: 1 });
    assert_eq!(cursor.advance_to(8), LinePos { line: 2, col: 1 });
}

/// A debug assertion: the check is off the release build's hot path.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "inside a character")]
fn the_cursor_refuses_an_offset_inside_a_character() {
    let table = LineStarts::new("é");
    table.cursor().advance_to(1);
}

#[test]
#[should_panic(expected = "past the end of its line")]
fn the_table_refuses_a_column_past_its_line() {
    LineStarts::new("ab\ncd").byte_offset(LinePos { line: 1, col: 3 });
}

#[test]
#[should_panic(expected = "inside a surrogate pair")]
fn the_table_refuses_a_column_inside_a_surrogate_pair() {
    LineStarts::new("𝔸").byte_offset(LinePos { line: 1, col: 1 });
}

#[test]
#[should_panic(expected = "the cursor only moves forward")]
fn the_cursor_refuses_to_move_back() {
    let table = LineStarts::new("a\nb\n");
    let mut cursor = table.cursor();
    cursor.advance_to(3);
    cursor.advance_to(2);
}

#[test]
#[should_panic(expected = "past the end of")]
fn the_cursor_refuses_an_offset_past_the_end() {
    let table = LineStarts::new("a\nb\n");
    table.cursor().advance_to(5);
}

#[test]
#[should_panic(expected = "has no line")]
fn the_table_refuses_a_line_past_the_last() {
    LineStarts::new("a\nb").line_start(3);
}

proptest! {
    /// Random character strings over the line-break spellings, multi-byte
    /// characters and BOMs, which the piece alphabets do not mix freely.
    #[test]
    fn random_text_matches_the_rescan(
        chars in prop::collection::vec(
            prop::sample::select(vec!['\n', '\r', 'a', ' ', 'é', '😃', '\u{FEFF}', '"', '(', '*', ')']),
            0..256,
        )
    ) {
        check(&chars.into_iter().collect::<String>());
    }

    /// Random walks over the lexical, panic-sweep and line-break alphabets, at
    /// lengths the pairs cannot reach.
    #[test]
    fn random_sources_match_the_rescan(
        pieces in prop::collection::vec(
            prop::sample::select(
                LEXICAL.iter().chain(WIDE).chain(NEWLINE_SHAPES).copied().collect::<Vec<_>>(),
            ),
            0..16,
        )
    ) {
        check(&pieces.concat());
    }
}
