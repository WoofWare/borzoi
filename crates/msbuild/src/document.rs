//! An XML document parsed once and held with its text, so that evaluations
//! can share it: [`crate::observed::ImportDocuments`] keeps one per imported
//! file across evaluations, and the item pass replays deferred groups
//! against the document the property pass walked. And an attribute read from
//! such a document as MSBuild reads it ([`attribute`]).

use std::borrow::Cow;

use roxmltree::{Document, Node};

use crate::observed::TextDigest;

/// `node`'s attribute `name` (in no namespace) as MSBuild reads it: the source
/// text with its entity and character references decoded, and nothing
/// normalised.
///
/// MSBuild reads a project through an `XmlTextReader` whose `Normalization` is
/// off (`XmlReaderExtension.GetXmlReader`), so a tab, line feed or carriage
/// return in an attribute reaches it as written, and a CRLF as two characters.
/// `roxmltree` applies XML's attribute-value normalisation (XML 1.0 §3.3.3,
/// after §2.11's line-end folding), which reads each as a space; inside a
/// quoted string of a condition, or in a file name, the two readings differ
/// (#750). Every attribute the walk reads by name goes through here (the
/// crate's `clippy.toml` bans `Node::attribute`). A metadatum written as an
/// attribute is read by the item pass, which MSBuild reads differently again.
pub(crate) fn attribute<'a>(node: Node<'a, '_>, name: &str) -> Option<Cow<'a, str>> {
    let attr = node
        .attributes()
        .find(|a| a.namespace().is_none() && a.name() == name)?;
    let raw = &node.document().input_text()[attr.range_value()];
    Some(read_attribute(raw, attr.value()))
}

/// MSBuild's reading of an attribute whose source text is `raw` and whose
/// XML-normalised value is `normalised`.
fn read_attribute<'a>(raw: &'a str, normalised: &'a str) -> Cow<'a, str> {
    if !raw.contains(['&', '\t', '\n', '\r']) {
        debug_assert_eq!(raw, normalised);
        return Cow::Borrowed(normalised);
    }
    let mut value = String::with_capacity(raw.len());
    // What XML normalisation makes of `raw`, built alongside as a check on this
    // reading: a reference is never normalised, literal whitespace always is.
    let mut folded = String::with_capacity(raw.len());
    let mut rest = raw;
    while let Some(c) = rest.chars().next() {
        if c == '&' {
            // `roxmltree` parsed the document, which it does only without a
            // DTD (`ParsingOptions::allow_dtd` is off), so every reference in
            // it is one of XML's five entities or a well-formed character
            // reference to a legal character.
            let end = rest.find(';').expect("a parsed reference ends in `;`");
            let decoded = match &rest[1..end] {
                "lt" => '<',
                "gt" => '>',
                "amp" => '&',
                "quot" => '"',
                "apos" => '\'',
                reference => {
                    let code = match reference.strip_prefix("#x") {
                        Some(hex) => u32::from_str_radix(hex, 16),
                        None => reference
                            .strip_prefix('#')
                            .expect("a parsed reference is an entity or a character")
                            .parse(),
                    };
                    code.ok()
                        .and_then(char::from_u32)
                        .expect("a parsed character reference names a character")
                }
            };
            value.push(decoded);
            folded.push(decoded);
            rest = &rest[end + 1..];
        } else if rest.starts_with("\r\n") {
            value.push_str("\r\n");
            folded.push(' ');
            rest = &rest[2..];
        } else {
            value.push(c);
            folded.push(if matches!(c, '\t' | '\n' | '\r') {
                ' '
            } else {
                c
            });
            rest = &rest[c.len_utf8()..];
        }
    }
    debug_assert_eq!(folded, normalised, "XML normalisation of {raw:?}");
    Cow::Owned(value)
}

self_cell::self_cell!(
    /// A text and the document `roxmltree` parsed from it, which borrows it.
    struct Cell {
        owner: String,
        #[covariant]
        dependent: Document,
    }
);

/// A text and the document `roxmltree` parsed from it.
///
/// `roxmltree` documents borrow the text they were parsed from; this type owns
/// both. The self-reference is `self_cell`'s, whose macro checks at compile
/// time that the document is covariant in the borrow and fixes the drop
/// order, so this crate holds no `unsafe` of its own.
pub struct ParsedDocument {
    cell: Cell,
    digest: TextDigest,
}

impl ParsedDocument {
    /// Parse `text`, whose digest is `digest`.
    pub fn parse(text: String, digest: TextDigest) -> Result<Self, roxmltree::Error> {
        debug_assert_eq!(digest, TextDigest::of(&text));
        let cell = Cell::try_new(text, |text| Document::parse(text))?;
        Ok(Self { cell, digest })
    }

    /// The document, for as long as `self` is borrowed.
    pub fn document(&self) -> &Document<'_> {
        self.cell.borrow_dependent()
    }

    /// The text the document was parsed from.
    pub fn text(&self) -> &str {
        self.cell.borrow_owner()
    }

    /// [`Self::text`]'s digest.
    pub fn digest(&self) -> TextDigest {
        self.digest
    }
}

impl std::fmt::Debug for ParsedDocument {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ParsedDocument")
            .field("digest", &self.digest)
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    #[test]
    fn a_parsed_document_outlives_the_string_it_was_made_from() {
        let source = String::from("<Project><PropertyGroup><A>x</A></PropertyGroup></Project>");
        let digest = TextDigest::of(&source);
        let parsed = ParsedDocument::parse(source, digest).expect("well-formed");
        let moved = Arc::new(parsed);
        let shared = Arc::clone(&moved);
        drop(moved);
        let a = shared
            .document()
            .descendants()
            .find(|n| n.has_tag_name("A"))
            .and_then(|n| n.text());
        assert_eq!(a, Some("x"));
        assert_eq!(shared.digest(), digest);
    }

    /// Each attribute's reading, and roxmltree's normalised one beside it.
    #[test]
    fn an_attribute_reads_as_written() {
        let source = "<A \
             a=\"x\ty\" b=\"x\r\ny\" c=\"x\ry\" d=\"x\ny\" e=\"&apos;&#10;&#x9;&#13;&lt;\" \
             f=\"plain\" g=\"caf\u{e9}&#x1D11E;\" h=\"&amp;#10;\" />";
        let doc = Document::parse(source).unwrap();
        let root = doc.root_element();
        for (name, msbuild, normalised) in [
            ("a", "x\ty", "x y"),
            ("b", "x\r\ny", "x y"),
            ("c", "x\ry", "x y"),
            ("d", "x\ny", "x y"),
            ("e", "'\n\t\r<", "'\n\t\r<"),
            ("f", "plain", "plain"),
            ("g", "caf\u{e9}\u{1d11e}", "caf\u{e9}\u{1d11e}"),
            ("h", "&#10;", "&#10;"),
        ] {
            assert_eq!(attribute(root, name).as_deref(), Some(msbuild), "{name}");
            #[allow(clippy::disallowed_methods)] // the normalised reading, for contrast
            let theirs = root.attribute(name);
            assert_eq!(theirs, Some(normalised), "{name}");
        }
        assert_eq!(attribute(root, "missing"), None);
    }

    /// One way to spell `c` in a double-quoted attribute: as itself where XML
    /// allows that, or as an entity or a decimal or hex character reference.
    fn spell(c: char, how: u8) -> String {
        let entity = match c {
            '<' => Some("&lt;"),
            '>' => Some("&gt;"),
            '&' => Some("&amp;"),
            '"' => Some("&quot;"),
            '\'' => Some("&apos;"),
            _ => None,
        };
        match how % 3 {
            0 if !matches!(c, '<' | '&' | '"') => c.to_string(),
            0 | 1 => entity.map_or_else(|| format!("&#{};", u32::from(c)), str::to_owned),
            _ => format!("&#x{:x};", u32::from(c)),
        }
    }

    proptest::proptest! {
        /// Any value, each character spelt any legal way, reads back as
        /// itself; and [`read_attribute`]'s check that its folding is
        /// roxmltree's normalisation holds throughout (a `debug_assert`).
        #[test]
        fn every_spelling_of_a_value_reads_back_as_it(
            chars in proptest::collection::vec(
                (
                    proptest::sample::select(vec![
                        'a', ' ', '\t', '\n', '\r', '<', '>', '&', '"', '\'', '%', ';',
                        '$', '\u{e9}', '\u{a0}', '\u{1d11e}',
                    ]),
                    0u8..3,
                ),
                0..24,
            )
        ) {
            let value: String = chars.iter().map(|(c, _)| *c).collect();
            let spelt: String = chars.iter().map(|(c, how)| spell(*c, *how)).collect();
            let source = format!("<A v=\"{spelt}\" />");
            let doc = Document::parse(&source).unwrap();
            let read = attribute(doc.root_element(), "v");
            proptest::prop_assert_eq!(read.as_deref(), Some(&*value));
        }
    }

    /// [`attribute`] relies on roxmltree refusing a DTD, so that no reference
    /// it decodes can be an entity a document declared.
    #[test]
    fn a_document_with_a_dtd_does_not_parse() {
        let source = "<!DOCTYPE A [<!ENTITY e \"x\">]><A a=\"&e;\" />";
        assert!(Document::parse(source).is_err());
    }

    #[test]
    fn malformed_text_fails_as_roxmltree_does() {
        let source = String::from("<Project>");
        let ours =
            ParsedDocument::parse(source.clone(), TextDigest::of(&source)).expect_err("malformed");
        let theirs = Document::parse(&source).expect_err("malformed");
        assert_eq!(ours, theirs);
    }
}
