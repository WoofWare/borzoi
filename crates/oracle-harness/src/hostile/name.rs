//! Hostile file and directory names ([`Kind::FileName`]).
//!
//! A name here is a *template* over the stem and extension a harness would
//! have used (`Lib` and `.fs`), so that a hostile name still has the
//! extension the subject dispatches on, and a failure names a file a reader
//! recognises. Rendering gives bytes: a name need not be UTF-8, and
//! [`Rendered`] says whether a string, or a file system, can hold it.
//!
//! The same alphabet serves wherever a name is *written*: an item spec, a
//! reference path, a property value used as a file name. A place that cannot
//! carry some byte (XML has no NUL, JSON no invalid UTF-8) filters those
//! entries out and excludes any dimension left empty, with that reason.

use std::ffi::{OsStr, OsString};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::sync::OnceLock;

use super::{Alphabet, Dimension, Entry, Kind};

/// One part of a name template.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Part {
    /// The stem the harness supplies.
    Stem,
    /// The stem, each ASCII letter in its other case.
    StemRecased,
    /// The extension the harness supplies, with its dot.
    Ext,
    /// The extension, each ASCII letter in its other case.
    ExtRecased,
    /// These bytes.
    Lit(&'static [u8]),
    /// As many `x` as bring the whole name to this many bytes: none where it
    /// is that long already.
    PadTo(usize),
}

/// A hostile name, as a template.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Name {
    /// The name.
    pub parts: &'static [Part],
    /// A second name that some comparison takes for this one (another case,
    /// another normal form, the same without an ignorable character). A
    /// fixture holding both asks which of the two a reader means.
    pub twin: Option<&'static [Part]>,
}

/// The plain name: the stem and the extension.
pub const PLAIN: &[Part] = &[Part::Stem, Part::Ext];

/// `text` with each ASCII letter in its other case.
fn recased(text: &str) -> String {
    text.chars()
        .map(|c| {
            if c.is_ascii_lowercase() {
                c.to_ascii_uppercase()
            } else {
                c.to_ascii_lowercase()
            }
        })
        .collect()
}

fn render_parts(parts: &[Part], stem: &str, ext: &str) -> Rendered {
    let fixed = |part: &Part| -> Vec<u8> {
        match part {
            Part::Stem => stem.as_bytes().to_vec(),
            Part::StemRecased => recased(stem).into_bytes(),
            Part::Ext => ext.as_bytes().to_vec(),
            Part::ExtRecased => recased(ext).into_bytes(),
            Part::Lit(bytes) => bytes.to_vec(),
            Part::PadTo(_) => Vec::new(),
        }
    };
    let fixed_len: usize = parts.iter().map(|p| fixed(p).len()).sum();
    let mut out = Vec::new();
    for part in parts {
        match part {
            // A name already that long takes no padding, and the template
            // does not vary it.
            Part::PadTo(total) => {
                out.extend(std::iter::repeat_n(b'x', total.saturating_sub(fixed_len)));
            }
            other => out.extend(fixed(other)),
        }
    }
    Rendered(out)
}

impl Name {
    /// The name for `stem` and `ext` (`ext` with its dot, or empty for a
    /// directory).
    pub fn render(&self, stem: &str, ext: &str) -> Rendered {
        render_parts(self.parts, stem, ext)
    }

    /// Whether the name is hostile for `stem` and `ext`: whether it differs
    /// from the plain name and from its twin. A template over a part that is
    /// empty or has no letter to recase renders the plain name, which is no
    /// draw of its dimension.
    pub fn varies(&self, stem: &str, ext: &str) -> bool {
        let rendered = self.render(stem, ext);
        rendered != render_parts(PLAIN, stem, ext) && self.twin(stem, ext) != Some(rendered)
    }

    /// The twin for `stem` and `ext`, if the name has one.
    pub fn twin(&self, stem: &str, ext: &str) -> Option<Rendered> {
        self.twin.map(|parts| render_parts(parts, stem, ext))
    }
}

/// A rendered name: bytes.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Rendered(Vec<u8>);

/// Why a rendered name is not one path component.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NotAComponent {
    /// It is empty.
    Empty,
    /// It holds a NUL, which ends a path.
    Nul,
    /// It holds a `/`, so it is several components.
    Separator,
    /// It is `.` or `..`, which name directories that exist already.
    Dots,
}

impl std::fmt::Display for NotAComponent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            NotAComponent::Empty => "the name is empty",
            NotAComponent::Nul => "no file name holds a NUL",
            NotAComponent::Separator => "a `/` makes the name several path components",
            NotAComponent::Dots => "`.` and `..` name directories that exist already",
        })
    }
}

impl Rendered {
    /// A name of exactly these bytes, for a harness's own name beside the
    /// alphabet's.
    pub fn from_bytes(bytes: impl Into<Vec<u8>>) -> Self {
        Rendered(bytes.into())
    }

    /// The bytes.
    pub fn bytes(&self) -> &[u8] {
        &self.0
    }

    /// The name as text, if it is UTF-8.
    pub fn to_str(&self) -> Option<&str> {
        std::str::from_utf8(&self.0).ok()
    }

    /// The name as the operating system holds one.
    pub fn to_os_string(&self) -> OsString {
        OsString::from_vec(self.0.clone())
    }

    /// The name as one path component, or why it cannot be one. A component
    /// the file system then refuses (too long, not UTF-8 on a file system
    /// that requires it) is the file system's to report:
    /// [`super::fs::HostileFs::place`].
    pub fn component(&self) -> Result<&OsStr, NotAComponent> {
        if self.0.is_empty() {
            Err(NotAComponent::Empty)
        } else if self.0.contains(&0) {
            Err(NotAComponent::Nul)
        } else if self.0.contains(&b'/') {
            Err(NotAComponent::Separator)
        } else if self.0 == b"." || self.0 == b".." {
            Err(NotAComponent::Dots)
        } else {
            Ok(OsStr::from_bytes(&self.0))
        }
    }
}

use Part::{Ext, ExtRecased, Lit, PadTo, Stem, StemRecased};

const fn name(parts: &'static [Part]) -> Name {
    Name { parts, twin: None }
}

const fn twinned(parts: &'static [Part], twin: &'static [Part]) -> Name {
    Name {
        parts,
        twin: Some(twin),
    }
}

/// The table: dimension, name, reason.
const TABLE: &[(Dimension, Name, &str)] = &[
    // Switch-shaped.
    (
        Dimension::SwitchShaped,
        name(&[Lit(b"-"), Stem, Ext]),
        "a bare leading dash, which a command line reads as the start of an option",
    ),
    (
        Dimension::SwitchShaped,
        name(&[Lit(b"--out:"), Stem, Lit(b".dll")]),
        "fsc's long output switch",
    ),
    (
        Dimension::SwitchShaped,
        name(&[Lit(b"-o:"), Stem, Lit(b".dll")]),
        "fsc's short output switch: a Compile item named so reaches fsc as the switch",
    ),
    (
        Dimension::SwitchShaped,
        name(&[Lit(b"-r:"), Stem, Lit(b".dll")]),
        "fsc's reference switch",
    ),
    (
        Dimension::SwitchShaped,
        name(&[Lit(b"@"), Stem, Lit(b".rsp")]),
        "a response file to fsc and to MSBuild",
    ),
    (
        Dimension::SwitchShaped,
        name(&[Lit(b"--")]),
        "the argument that ends options, to the parsers that have one",
    ),
    // An early colon.
    (
        Dimension::EarlyColon,
        name(&[Lit(b"r:"), Stem, Ext]),
        "a colon in second position: an option's separator after a slash, a drive letter",
    ),
    (
        Dimension::EarlyColon,
        name(&[Lit(b"C:"), Stem, Ext]),
        "a drive letter",
    ),
    (
        Dimension::EarlyColon,
        name(&[Lit(b"ab:"), Stem, Ext]),
        "a colon in third position, which MSBuild's item comparison treats as it does a wildcard",
    ),
    // Backslashes.
    (
        Dimension::Backslash,
        name(&[Stem, Lit(b"\\b"), Ext]),
        "a backslash inside a name, which MSBuild may rewrite to a separator",
    ),
    (
        Dimension::Backslash,
        name(&[Lit(b"..\\"), Stem, Ext]),
        "one file here to Unix, a file in the parent directory to MSBuild",
    ),
    (
        Dimension::Backslash,
        name(&[Lit(b"\\"), Stem, Ext]),
        "a leading backslash: rooted once rewritten, and a slash-led option once rewritten (`\\o:`)",
    ),
    (
        Dimension::Backslash,
        name(&[Stem, Ext, Lit(b"\\")]),
        "a trailing backslash: a directory once rewritten",
    ),
    // Percent escapes.
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%0A"), Ext]),
        "an escaped line feed: a line break once MSBuild decodes it",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%3B"), Ext]),
        "an escaped semicolon: data, never a list separator",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%3b"), Ext]),
        "an escape with lower-case hex digits",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%25"), Ext]),
        "an escaped percent, which must not be scanned again after decoding",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%2541"), Ext]),
        "an escape that decodes to an escape (`%41`, then `A`) if decoded twice",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%20"), Ext]),
        "an escaped space, which trimming must not remove",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%00"), Ext]),
        "an escaped NUL: a character no path holds, once decoded",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%2A"), Ext]),
        "an escaped star: a literal star, never a wildcard",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%"), Ext]),
        "a percent that starts no escape and stays itself",
    ),
    (
        Dimension::PercentEscape,
        name(&[Stem, Lit(b"%zz"), Ext]),
        "a percent before two characters that are not hex digits",
    ),
    // List separators.
    (
        Dimension::ListSeparator,
        name(&[Stem, Lit(b";b"), Ext]),
        "a semicolon, which splits an item spec and a property list",
    ),
    (
        Dimension::ListSeparator,
        name(&[Stem, Lit(b",b"), Ext]),
        "a comma, which splits the property list of a `-p:` switch and a logger's parameters",
    ),
    // Quotes.
    (
        Dimension::Quote,
        name(&[Stem, Lit(b"\""), Ext]),
        "a double quote, which opens a quoted string to a response file",
    ),
    (
        Dimension::Quote,
        name(&[Stem, Lit(b"'"), Ext]),
        "a single quote, which opens a string in a condition",
    ),
    (
        Dimension::Quote,
        name(&[Lit(b"\""), Stem, Ext, Lit(b"\"")]),
        "a name written inside quotes, which a reader that strips quotes takes for the plain name",
    ),
    // Glob characters.
    (
        Dimension::GlobChar,
        name(&[Stem, Lit(b"*"), Ext]),
        "a star: a file's name, and a pattern that matches other files",
    ),
    (
        Dimension::GlobChar,
        name(&[Stem, Lit(b"?"), Ext]),
        "a question mark: one character to a pattern",
    ),
    (
        Dimension::GlobChar,
        name(&[Stem, Lit(b"[ab]"), Ext]),
        "a bracket expression to the matchers that have them",
    ),
    (
        Dimension::GlobChar,
        name(&[Lit(b"**")]),
        "the recursive wildcard, as a name",
    ),
    // Expansions.
    (
        Dimension::Expansion,
        name(&[Stem, Lit(b"$(X)"), Ext]),
        "a property reference",
    ),
    (
        Dimension::Expansion,
        name(&[Stem, Lit(b"@(X)"), Ext]),
        "an item list reference",
    ),
    (
        Dimension::Expansion,
        name(&[Stem, Lit(b"%(X)"), Ext]),
        "a metadata reference",
    ),
    (
        Dimension::Expansion,
        name(&[Stem, Lit(b"$("), Ext]),
        "an expansion that never closes",
    ),
    (
        Dimension::Expansion,
        name(&[Lit(b"$(MSBuildProjectName)"), Ext]),
        "a reference to a property every project has",
    ),
    // XML markup.
    (
        Dimension::XmlMarkup,
        name(&[Stem, Lit(b"&#10;"), Ext]),
        "a character reference as text: a line feed if the text is read as XML once more",
    ),
    (
        Dimension::XmlMarkup,
        name(&[Stem, Lit(b"&#x3B;"), Ext]),
        "a hexadecimal character reference as text",
    ),
    (
        Dimension::XmlMarkup,
        name(&[Stem, Lit(b"&amp;"), Ext]),
        "an entity reference as text",
    ),
    (
        Dimension::XmlMarkup,
        name(&[Stem, Lit(b"&"), Ext]),
        "a bare ampersand, which is malformed XML unless escaped",
    ),
    (
        Dimension::XmlMarkup,
        name(&[Stem, Lit(b"<"), Ext]),
        "a bare angle bracket, which is malformed XML unless escaped",
    ),
    // Line breaks.
    (
        Dimension::LineBreak,
        name(&[Stem, Lit(b"\n"), Ext]),
        "a line feed",
    ),
    (
        Dimension::LineBreak,
        name(&[Stem, Lit(b"\r"), Ext]),
        "a bare carriage return",
    ),
    (
        Dimension::LineBreak,
        name(&[Stem, Lit(b"\r\n"), Ext]),
        "a carriage return and line feed",
    ),
    (
        Dimension::LineBreak,
        name(&[Stem, Lit("\u{85}".as_bytes()), Ext]),
        "NEL, a line break to .NET's line reader and to no Unix tool",
    ),
    (
        Dimension::LineBreak,
        name(&[Stem, Lit("\u{2028}".as_bytes()), Ext]),
        "the line separator, a line break to .NET and whitespace JSON does not allow raw",
    ),
    (
        Dimension::LineBreak,
        name(&[Stem, Lit("\u{2029}".as_bytes()), Ext]),
        "the paragraph separator",
    ),
    (
        Dimension::LineBreak,
        name(&[Stem, Lit(b"\n--out:Evil"), Ext]),
        "a line feed and then a switch: a response file's next line",
    ),
    // Other control characters.
    (
        Dimension::ControlChar,
        name(&[Stem, Lit(b"\t"), Ext]),
        "a tab",
    ),
    (
        Dimension::ControlChar,
        name(&[Stem, Lit(b"\x01"), Ext]),
        "a control character with no escape of its own in JSON or XML 1.0",
    ),
    (
        Dimension::ControlChar,
        name(&[Stem, Lit(b"\x1b"), Ext]),
        "an escape, which starts a terminal sequence in a log",
    ),
    (
        Dimension::ControlChar,
        name(&[Stem, Lit(b"\x7f"), Ext]),
        "a delete",
    ),
    (
        Dimension::ControlChar,
        name(&[Stem, Lit(b"\0"), Ext]),
        "a NUL: text, and no file's name",
    ),
    // Dots and spaces at the edges.
    (
        Dimension::EdgeDotOrSpace,
        name(&[Stem, Ext, Lit(b".")]),
        "a trailing dot, which Windows path handling drops",
    ),
    (
        Dimension::EdgeDotOrSpace,
        name(&[Stem, Ext, Lit(b" ")]),
        "a trailing space, which MSBuild trims from an item spec",
    ),
    (
        Dimension::EdgeDotOrSpace,
        name(&[Lit(b" "), Stem, Ext]),
        "a leading space",
    ),
    (
        Dimension::EdgeDotOrSpace,
        name(&[Stem, Lit(b" "), Ext]),
        "a space before the extension",
    ),
    (
        Dimension::EdgeDotOrSpace,
        name(&[Stem, Ext, Lit(b"..")]),
        "two trailing dots",
    ),
    // Dot names.
    (
        Dimension::DotName,
        name(&[Lit(b".")]),
        "the directory itself",
    ),
    (
        Dimension::DotName,
        name(&[Lit(b"..")]),
        "the parent directory",
    ),
    (
        Dimension::DotName,
        name(&[Lit(b"...")]),
        "three dots: an ordinary name on Unix",
    ),
    (
        Dimension::DotName,
        name(&[Lit(b"."), Stem, Ext]),
        "a hidden file, which the SDK's default globs exclude",
    ),
    (Dimension::DotName, name(&[Ext]), "an extension and no stem"),
    // Invisible characters.
    (
        Dimension::Invisible,
        twinned(&[Stem, Lit("\u{ad}".as_bytes()), Ext], PLAIN),
        "a soft hyphen, which .NET's culture-aware comparisons ignore: FCS keyed two sources as one file",
    ),
    (
        Dimension::Invisible,
        twinned(&[Stem, Lit("\u{200b}".as_bytes()), Ext], PLAIN),
        "a zero-width space",
    ),
    (
        Dimension::Invisible,
        twinned(&[Stem, Lit("\u{200d}".as_bytes()), Ext], PLAIN),
        "a zero-width joiner",
    ),
    (
        Dimension::Invisible,
        twinned(&[Lit("\u{feff}".as_bytes()), Stem, Ext], PLAIN),
        "a byte order mark at the start of the name",
    ),
    (
        Dimension::Invisible,
        name(&[Stem, Lit("\u{202e}".as_bytes()), Ext]),
        "a right-to-left override, which reorders what a log shows",
    ),
    // Case folding.
    (
        Dimension::CaseFold,
        twinned(&[StemRecased, ExtRecased], PLAIN),
        "the name in upper case",
    ),
    (
        Dimension::CaseFold,
        twinned(&[Stem, ExtRecased], PLAIN),
        "the extension in upper case, where the extension chooses how a file is read",
    ),
    (
        Dimension::CaseFold,
        twinned(
            &[Stem, Lit("\u{212a}".as_bytes()), Ext],
            &[Stem, Lit(b"k"), Ext],
        ),
        "the Kelvin sign, which folds to `k` under some case-insensitive comparisons and not others",
    ),
    (
        Dimension::CaseFold,
        twinned(
            &[Stem, Lit("\u{130}".as_bytes()), Ext],
            &[Stem, Lit(b"i"), Ext],
        ),
        "a dotted capital I, whose lower case depends on the culture",
    ),
    (
        Dimension::CaseFold,
        twinned(
            &[Stem, Lit("\u{131}".as_bytes()), Ext],
            &[Stem, Lit(b"I"), Ext],
        ),
        "a dotless small i, whose upper case is `I`",
    ),
    (
        Dimension::CaseFold,
        twinned(
            &[Stem, Lit("\u{17f}".as_bytes()), Ext],
            &[Stem, Lit(b"s"), Ext],
        ),
        "a long s, whose upper case is `S`",
    ),
    (
        Dimension::CaseFold,
        twinned(
            &[Stem, Lit("\u{df}".as_bytes()), Ext],
            &[Stem, Lit(b"ss"), Ext],
        ),
        "a sharp s, whose upper case is two letters",
    ),
    (
        Dimension::CaseFold,
        twinned(
            &[Stem, Lit("\u{e9}".as_bytes()), Ext],
            &[Stem, Lit("\u{c9}".as_bytes()), Ext],
        ),
        "a non-ASCII case pair, which an ASCII-only fold keeps apart",
    ),
    // Normal forms.
    (
        Dimension::Normalisation,
        twinned(
            &[Stem, Lit("\u{e9}".as_bytes()), Ext],
            &[Stem, Lit("e\u{301}".as_bytes()), Ext],
        ),
        "a precomposed letter, and its twin the letter with a combining accent: one name to macOS",
    ),
    (
        Dimension::Normalisation,
        twinned(
            &[Stem, Lit("\u{212b}".as_bytes()), Ext],
            &[Stem, Lit("\u{c5}".as_bytes()), Ext],
        ),
        "the Angstrom sign, which every normal form replaces with another letter",
    ),
    // Confusables.
    (
        Dimension::Confusable,
        twinned(
            &[Stem, Lit("\u{430}".as_bytes()), Ext],
            &[Stem, Lit(b"a"), Ext],
        ),
        "a Cyrillic letter that looks like a Latin one",
    ),
    (
        Dimension::Confusable,
        name(&[Stem, Lit("\u{ff0f}".as_bytes()), Ext]),
        "a full-width solidus, which a best-fit conversion turns into a separator",
    ),
    (
        Dimension::Confusable,
        name(&[Stem, Lit("\u{2215}".as_bytes()), Ext]),
        "a division slash",
    ),
    (
        Dimension::Confusable,
        name(&[Lit("\u{ff0d}o\u{ff1a}".as_bytes()), Stem, Ext]),
        "a full-width hyphen and colon: a switch after a best-fit conversion",
    ),
    // Characters two UTF-16 units wide.
    (
        Dimension::Utf16Width,
        name(&[Stem, Lit("\u{1f98b}".as_bytes()), Ext]),
        "one character to us and two UTF-16 units to MSBuild's `?` and to an LSP position",
    ),
    (
        Dimension::Utf16Width,
        name(&[Stem, Lit("\u{10000}".as_bytes()), Ext]),
        "the first character outside the Basic Multilingual Plane",
    ),
    // Bytes that are not UTF-8.
    (
        Dimension::NonUtf8,
        name(&[Stem, Lit(b"\xff"), Ext]),
        "a byte no UTF-8 text holds",
    ),
    (
        Dimension::NonUtf8,
        name(&[Stem, Lit(b"\xe9"), Ext]),
        "a Latin-1 letter: a continuation is missing",
    ),
    (
        Dimension::NonUtf8,
        name(&[Stem, Lit(b"\xc0\xaf"), Ext]),
        "an overlong encoding of `/`",
    ),
    (
        Dimension::NonUtf8,
        name(&[Stem, Lit(b"\xed\xa0\x80"), Ext]),
        "an encoded surrogate, which .NET's strings can hold and UTF-8 cannot",
    ),
    (
        Dimension::NonUtf8,
        name(&[Stem, Lit(b"\xe2\x82"), Ext]),
        "a truncated three-byte sequence",
    ),
    // Long names.
    (
        Dimension::Long,
        name(&[Stem, PadTo(255), Ext]),
        "the longest name most file systems take",
    ),
    (
        Dimension::Long,
        name(&[Stem, PadTo(256), Ext]),
        "one byte longer than that",
    ),
    // Extensions that choose how a tool reads the file.
    (
        Dimension::KindByExtension,
        name(&[Stem, Lit(b".dll")]),
        "an assembly to fsc, whatever item type named it",
    ),
    (
        Dimension::KindByExtension,
        name(&[Stem, Lit(b".exe")]),
        "an assembly to fsc",
    ),
    (
        Dimension::KindByExtension,
        name(&[Stem, Lit(b".netmodule")]),
        "a module to fsc",
    ),
    (
        Dimension::KindByExtension,
        name(&[Stem, Lit(b".resx")]),
        "a resource, which fsc refuses as a positional argument",
    ),
    (
        Dimension::KindByExtension,
        name(&[Stem, Lit(b".resources")]),
        "a compiled resource to fsc",
    ),
    (
        Dimension::KindByExtension,
        name(&[Stem, Lit(b".fsx")]),
        "a script, whose `#r` and `#load` lines a compiled source lacks",
    ),
    (
        Dimension::KindByExtension,
        name(&[Stem]),
        "no extension at all",
    ),
];

/// The alphabet of hostile names.
pub fn alphabet() -> &'static Alphabet<Name> {
    static ALPHABET: OnceLock<Alphabet<Name>> = OnceLock::new();
    ALPHABET.get_or_init(|| {
        Alphabet::new(
            Kind::FileName,
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

/// Every entry that [varies](Name::varies) rendered for `stem` and `ext` as
/// text, without the names no string holds: the alphabet for a place that carries text (an item spec, a
/// property value). [`Dimension::NonUtf8`] has no such name, so a harness
/// that draws only these excludes it, with that reason.
pub fn as_text(stem: &str, ext: &str) -> Vec<Entry<String>> {
    alphabet()
        .entries()
        .iter()
        .filter(|e| e.value.varies(stem, ext))
        .filter_map(|e| {
            Some(Entry {
                dimension: e.dimension,
                value: e.value.render(stem, ext).to_str()?.to_owned(),
                why: e.why,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    #[test]
    fn the_alphabet_covers_every_name_dimension() {
        // `Alphabet::new` panics on a dimension with no entry.
        assert_eq!(alphabet().kind(), Kind::FileName);
    }

    /// A place that carries text takes a name of any length: a template
    /// that pads to fewer bytes than the name has does not vary it, and is
    /// left out, and the others render.
    #[test]
    fn a_name_longer_than_a_padding_asks_for_is_not_padded() {
        let stem = "s".repeat(300);
        let entries = as_text(&stem, ".fs");
        assert!(!entries.is_empty());
        assert!(
            entries.iter().all(|e| e.dimension != Dimension::Long),
            "nothing is left to pad"
        );
    }

    #[test]
    fn rendered_names_are_distinct_and_differ_from_the_plain_name() {
        let plain = render_parts(PLAIN, "Lib", ".fs");
        let mut seen = BTreeSet::new();
        for e in alphabet().entries() {
            let rendered = e.value.render("Lib", ".fs");
            assert_ne!(rendered, plain, "{}: {}", e.dimension, e.why);
            // One name may sit in two dimensions (a precomposed letter is a
            // case pair and a normal form), never twice in one.
            assert!(
                seen.insert((e.dimension, rendered.clone())),
                "{rendered:?} is in {} twice",
                e.dimension
            );
            if let Some(twin) = e.value.twin("Lib", ".fs") {
                assert_ne!(twin, rendered, "a twin is another name: {}", e.why);
            }
        }
    }

    #[test]
    fn only_the_non_utf8_dimension_is_not_text() {
        for e in alphabet().entries() {
            let rendered = e.value.render("Lib", ".fs");
            assert_eq!(
                rendered.to_str().is_none(),
                e.dimension == Dimension::NonUtf8,
                "{rendered:?} ({})",
                e.dimension
            );
        }
        let text = as_text("Lib", ".fs");
        assert!(text.iter().all(|e| e.dimension != Dimension::NonUtf8));
        assert_eq!(
            text.len(),
            alphabet().entries().len() - alphabet().of(Dimension::NonUtf8).count()
        );
    }

    #[test]
    fn a_name_that_renders_the_plain_one_does_not_vary() {
        let recased_ext = alphabet()
            .of(Dimension::CaseFold)
            .find(|e| e.value.parts == [Part::Stem, Part::ExtRecased])
            .unwrap();
        // A directory has no extension to recase, and the name is the plain one.
        assert!(recased_ext.value.varies("Lib", ".fs"));
        assert!(!recased_ext.value.varies("Lib", ""));
        // An upper-case name still has another case.
        for e in alphabet().of(Dimension::CaseFold) {
            assert!(e.value.varies("LIB", ".FS"), "{}", e.why);
        }
        assert!(as_text("123", "").iter().all(|e| e.value != "123"));
    }

    #[test]
    fn a_long_name_is_as_long_as_it_says() {
        let lengths: Vec<usize> = alphabet()
            .of(Dimension::Long)
            .map(|e| e.value.render("Lib", ".fs").bytes().len())
            .collect();
        assert_eq!(lengths, [255, 256]);
    }

    #[test]
    fn a_component_is_refused_for_the_reason_it_cannot_exist() {
        let component = |bytes: &[u8]| Rendered(bytes.to_vec()).component().map(|_| ());
        assert_eq!(component(b""), Err(NotAComponent::Empty));
        assert_eq!(component(b"a\0b"), Err(NotAComponent::Nul));
        assert_eq!(component(b"a/b"), Err(NotAComponent::Separator));
        assert_eq!(component(b"."), Err(NotAComponent::Dots));
        assert_eq!(component(b".."), Err(NotAComponent::Dots));
        assert_eq!(component(b"..."), Ok(()));
        assert_eq!(component(b"\xff"), Ok(()));
    }
}
