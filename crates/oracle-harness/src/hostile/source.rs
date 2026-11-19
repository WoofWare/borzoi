//! Hostile F# source text ([`Kind::SourceText`]).
//!
//! Not hostile *programs*: the generators of F# shapes are each harness's
//! own. These are the lexical states of a source file that a tool around the
//! compiler gets wrong while the compiler does not: a directive that moves
//! the positions a diagnostic reports, text that only looks like one, a
//! symbol only some tools define, bytes before or between the lines.
//!
//! A [`Mutation`] is applied to a source file a harness already has, which
//! must still mean what it meant. A mutation that adds a declaration adds a
//! module at column zero, which is a declaration a namespace takes as well
//! as a module does (a `let` is not), so the file it is appended to may end
//! in either.

use std::sync::OnceLock;

use super::{Alphabet, Dimension, Entry, Kind};

/// One change to a source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutation {
    /// These bytes before the file.
    Prepend(&'static [u8]),
    /// These bytes after the file, which is first ended with a line feed.
    Append(&'static [u8]),
    /// Every line end (a line feed, a carriage return, or the two together)
    /// replaced by this.
    LineEnds(&'static str),
    /// These bytes this many times, after the file.
    AppendRepeated(&'static [u8], usize),
}

impl Mutation {
    /// The mutated file.
    pub fn apply(&self, source: &str) -> Vec<u8> {
        let mut out = Vec::new();
        match self {
            Mutation::Prepend(bytes) => {
                out.extend(*bytes);
                out.extend(source.as_bytes());
            }
            Mutation::Append(bytes) => {
                out.extend(source.as_bytes());
                if !source.ends_with('\n') {
                    out.push(b'\n');
                }
                out.extend(*bytes);
            }
            Mutation::LineEnds(end) => {
                // Each line end once, however the source spelt it.
                let unix = source.replace("\r\n", "\n").replace('\r', "\n");
                out.extend(unix.replace('\n', end).as_bytes());
            }
            Mutation::AppendRepeated(bytes, n) => {
                out.extend(source.as_bytes());
                if !source.ends_with('\n') {
                    out.push(b'\n');
                }
                for _ in 0..*n {
                    out.extend(*bytes);
                }
            }
        }
        out
    }
}

use Mutation::{Append, AppendRepeated, LineEnds, Prepend};

const TABLE: &[(Dimension, Mutation, &str)] = &[
    (
        Dimension::LineDirective,
        Append(b"#line 1 \"Other.fs\"\nmodule HostileAfterLine =\n    let x = 1\n"),
        "a line directive naming another file: diagnostics after it are reported there",
    ),
    (
        Dimension::LineDirective,
        Append(b"# 1 \"Other.fs\"\nmodule HostileAfterShortLine =\n    let x = 1\n"),
        "the short form of the directive",
    ),
    (
        Dimension::LineDirective,
        Append(b"#line 100000\nmodule HostileAfterFarLine =\n    let x = 1\n"),
        "a directive that moves the line and keeps the file",
    ),
    (
        Dimension::LineDirective,
        Append(b"(* c *) #line 1 \"Other.fs\"\nmodule HostileAfterLateLine =\n    let x = 1\n"),
        "a directive after a comment on its line, which a scan of line starts misses",
    ),
    (
        Dimension::DirectiveLookalike,
        Append(b"// C# 12+ and #line 1 \"Other.fs\" in a comment\n"),
        "directive-shaped text in a comment: a pattern matched it and refused a real project",
    ),
    (
        Dimension::DirectiveLookalike,
        Append(b"module HostileText =\n    let text = \"\n#line 1 \\\"Other.fs\\\"\n\"\n"),
        "directive-shaped text at the start of a line inside a string",
    ),
    (
        Dimension::DirectiveLookalike,
        Append(b"module HostileOperator =\n    let (+//) a b = a + b\n"),
        "an operator holding the characters that start a line comment",
    ),
    (
        Dimension::DirectiveLookalike,
        Append(b"module HostileTriple =\n    let text = \"\"\"\n#r \"Lib.dll\"\n#if EDITING\n\"\"\"\n"),
        "directives inside a triple-quoted string",
    ),
    (
        Dimension::ScriptDirective,
        Append(b"#r \"Hostile.dll\"\n"),
        "a reference directive: a script's, and an error or a no-op in a compiled source",
    ),
    (
        Dimension::ScriptDirective,
        Append(b"#load \"Hostile.fsx\"\n"),
        "a load directive",
    ),
    (
        Dimension::ScriptDirective,
        Append(b"#if EDITING\n#r \"Hostile.dll\"\n#endif\n"),
        "a reference only an editing tool sees",
    ),
    (
        Dimension::ToolDefine,
        Append(b"#if EDITING\nmodule HostileOnlyWhenEditing =\n    let x = 1\n#endif\n"),
        "a symbol FCS's editor services define and fsc does not",
    ),
    (
        Dimension::ToolDefine,
        Append(b"#if COMPILED\nmodule HostileOnlyWhenCompiled =\n    let x = 1\n#else\nmodule HostileOnlyWhenNot =\n    let x = 1\n#endif\n"),
        "a symbol fsc defines and a script host does not",
    ),
    (
        Dimension::ToolDefine,
        Append(b"#if INTERACTIVE\nmodule HostileOnlyWhenInteractive =\n    let x = 1\n#endif\n"),
        "a symbol only F# Interactive defines",
    ),
    (
        Dimension::LongRun,
        AppendRepeated(b" ", 32_768),
        "tens of thousands of blanks on one line, on which a backtracking pattern is quadratic",
    ),
    (
        Dimension::LongRun,
        AppendRepeated(b"\n", 100_000),
        "a hundred thousand empty lines",
    ),
    (
        Dimension::ByteOrderMark,
        Prepend("\u{feff}".as_bytes()),
        "a UTF-8 byte order mark, which is no part of the first token",
    ),
    (
        Dimension::LineEnds,
        LineEnds("\r\n"),
        "Windows line ends: one line end each, two characters to a position",
    ),
    (
        Dimension::LineEnds,
        LineEnds("\r"),
        "bare carriage returns, which .NET's line reader splits at",
    ),
    (
        Dimension::LineEnds,
        Append("// \u{2028} and \u{85} in a comment\n".as_bytes()),
        "Unicode line separators, which are line ends to some line counters and not to the compiler",
    ),
    (
        Dimension::NotText,
        Append(b"// \xff in a comment\n"),
        "a byte that is not UTF-8",
    ),
    (
        Dimension::NotText,
        Append(b"// \0 in a comment\n"),
        "a NUL",
    ),
];

/// The alphabet of hostile source mutations.
pub fn alphabet() -> &'static Alphabet<Mutation> {
    static ALPHABET: OnceLock<Alphabet<Mutation>> = OnceLock::new();
    ALPHABET.get_or_init(|| {
        Alphabet::new(
            Kind::SourceText,
            TABLE
                .iter()
                .map(|(dimension, value, why)| Entry {
                    dimension: *dimension,
                    value: *value,
                    why,
                })
                .collect(),
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_alphabet_covers_every_source_dimension() {
        assert_eq!(alphabet().kind(), Kind::SourceText);
    }

    #[test]
    fn every_mutation_changes_the_file_and_keeps_its_text() {
        let source = "module M\nlet x = 1";
        for entry in alphabet().entries() {
            let mutated = entry.value.apply(source);
            assert_ne!(mutated, source.as_bytes(), "{}", entry.why);
            match entry.value {
                Mutation::Prepend(_) => assert!(mutated.ends_with(source.as_bytes())),
                Mutation::Append(_) | Mutation::AppendRepeated(..) => {
                    assert!(
                        mutated.starts_with(b"module M\nlet x = 1\n"),
                        "{}",
                        entry.why
                    )
                }
                Mutation::LineEnds(end) => {
                    assert_eq!(
                        String::from_utf8(mutated).unwrap().replace(end, "\n"),
                        source
                    );
                    // A source already spelt with other line ends has each
                    // replaced once, none doubled.
                    assert_eq!(
                        entry.value.apply("a\r\nb\rc\nd"),
                        format!("a{end}b{end}c{end}d").into_bytes()
                    );
                }
            }
        }
    }
}
