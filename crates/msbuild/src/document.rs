//! An XML document parsed once and held with its text, so that evaluations
//! can share it: [`crate::observed::ImportDocuments`] keeps one per imported
//! file across evaluations, and the item pass replays deferred groups
//! against the document the property pass walked. Every document the crate
//! reads is parsed through [`parse`], and its attributes read through
//! [`attribute`], as MSBuild reads them.

use std::borrow::Cow;

use roxmltree::{Attribute, Document, Node};

use crate::observed::TextDigest;

/// Parse project text, refusing a document `roxmltree` reads apart from
/// MSBuild in a way no reader here can recover.
///
/// `roxmltree` reads a character reference to a code point that is not a
/// Unicode scalar value (a surrogate, `&#xD800;`, or one past `U+10FFFF`) as
/// `U+FFFD`, which no reading of MSBuild's can be, and which a Rust string
/// cannot spell otherwise; a document holding one is refused here. The scan
/// covers the whole text, comments and CDATA sections included, where such a
/// reference is only text: refusing those too costs a decline, never a wrong
/// value. Without a DTD (which `roxmltree` refuses by default) every other
/// reference it accepts is one of XML's five entities or names a character.
/// The crate's `clippy.toml` bans `Document::parse` in favour of this.
pub fn parse(text: &str) -> Result<Document<'_>, roxmltree::Error> {
    #[allow(clippy::disallowed_methods)] // the one parse, held to the rule above
    let document = Document::parse(text)?;
    let mut rest = text;
    while let Some(at) = rest.find("&#") {
        let reference = &rest[at + 2..];
        let (digits, radix) = match reference.strip_prefix('x') {
            Some(hex) => (hex, 16),
            None => (reference, 10),
        };
        // Only the run of digits is read, so the scan stays linear in the text.
        let run = digits
            .bytes()
            .take_while(|b| char::from(*b).is_digit(radix))
            .count();
        // A run not closed by `;`, or that is no `u32`, fails `roxmltree`'s
        // parse wherever it would form a reference, so here it is text.
        let names_no_character = digits[run..].starts_with(';')
            && u32::from_str_radix(&digits[..run], radix)
                .is_ok_and(|code| char::from_u32(code).is_none());
        if names_no_character {
            let offset = text.len() - rest.len() + at;
            return Err(roxmltree::Error::MalformedEntityReference(
                document.text_pos_at(offset),
            ));
        }
        rest = reference;
    }
    Ok(document)
}

/// `attr`'s value as it stands in the source text of `node`'s document,
/// between its quotes. `Attribute::range_value` is not that: `roxmltree` keeps
/// the run of whitespace around `=` in a byte, so past 255 characters of it
/// the range starts early. The full range is exact, and an attribute's name,
/// `=` and whitespace hold no quote, so the value starts after the first.
pub(crate) fn attribute_source<'input>(
    node: Node<'_, 'input>,
    attr: &Attribute<'_, 'input>,
) -> &'input str {
    let full = &node.document().input_text()[attr.range()];
    let open = full
        .find(['"', '\''])
        .expect("a parsed attribute's value is quoted");
    &full[open + 1..full.len() - 1]
}

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
pub fn attribute<'a>(node: Node<'a, '_>, name: &str) -> Option<Cow<'a, str>> {
    let attr = node
        .attributes()
        .find(|a| a.namespace().is_none() && a.name() == name)?;
    Some(read_attribute(attribute_source(node, &attr), attr.value()))
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
            // [`parse`] parsed the document, so every reference in it is one
            // of XML's five entities or a well-formed character reference to
            // a Unicode scalar value.
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
        let cell = Cell::try_new(text, |text| parse(text))?;
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

    use proptest::strategy::Strategy;

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
        let doc = parse(source).unwrap();
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

    /// One way to spell `c` in an attribute quoted with `quote`: as itself
    /// where XML allows that, or as an entity or a decimal or hex character
    /// reference.
    fn spell(c: char, how: u8, quote: char) -> String {
        let entity = match c {
            '<' => Some("&lt;"),
            '>' => Some("&gt;"),
            '&' => Some("&amp;"),
            '"' => Some("&quot;"),
            '\'' => Some("&apos;"),
            _ => None,
        };
        match how % 3 {
            0 if !matches!(c, '<' | '&') && c != quote => c.to_string(),
            0 | 1 => entity.map_or_else(|| format!("&#{};", u32::from(c)), str::to_owned),
            _ => format!("&#x{:x};", u32::from(c)),
        }
    }

    /// Whitespace XML allows around an attribute's `=`.
    fn separator() -> impl proptest::strategy::Strategy<Value = String> {
        proptest::prop_oneof![
            proptest::collection::vec(proptest::sample::select(vec![' ', '\t', '\n', '\r']), 0..4)
                .prop_map(|cs| cs.into_iter().collect()),
            // Past the byte `roxmltree` keeps the run's length in.
            (250usize..600).prop_map(|n| " ".repeat(n)),
        ]
    }

    proptest::proptest! {
        /// Any value, each character spelt any legal way, in either quote and
        /// with any whitespace around `=`, after another attribute, reads back
        /// as itself; and [`read_attribute`]'s check that its folding is
        /// roxmltree's normalisation holds throughout (a `debug_assert`).
        #[test]
        fn every_spelling_of_a_value_reads_back_as_it(
            chars in proptest::collection::vec(
                (
                    proptest::sample::select(vec![
                        'a', ' ', '\t', '\n', '\r', '<', '>', '&', '"', '\'', '%', ';',
                        '$', '=', '\u{e9}', '\u{a0}', '\u{1d11e}',
                    ]),
                    0u8..3,
                ),
                0..24,
            ),
            quote in proptest::sample::select(vec!['"', '\'']),
            before in separator(),
            after in separator(),
        ) {
            let value: String = chars.iter().map(|(c, _)| *c).collect();
            let spelt: String = chars.iter().map(|(c, how)| spell(*c, *how, quote)).collect();
            let source = format!("<A w=\"=\" v{before}={after}{quote}{spelt}{quote} />");
            let doc = parse(&source).unwrap();
            let read = attribute(doc.root_element(), "v");
            proptest::prop_assert_eq!(read.as_deref(), Some(&*value));
        }
    }

    /// A piece of a double-quoted attribute value: legal text, and character
    /// references whether or not they name a character XML allows.
    const VALUE_PIECES: [&str; 17] = [
        "a",
        " ",
        "\t",
        "\n",
        "\r",
        "\r\n",
        ">",
        "'",
        "&amp;",
        "&lt;",
        "&#10;",
        "&#x9;",
        "&#xD800;",
        "&#x110000;",
        "&#0;",
        "&#xFFFD;",
        "&#1114111;",
    ];

    proptest::proptest! {
        /// Whatever document [`parse`] admits, every attribute of it reads
        /// without a panic, and folding its reading gives roxmltree's value
        /// (the `debug_assert` in [`read_attribute`]); and a document holding
        /// a reference to no character is never admitted.
        #[test]
        fn every_admitted_attribute_reads(
            attributes in proptest::collection::vec(
                (separator(), proptest::collection::vec(proptest::sample::select(VALUE_PIECES.to_vec()), 0..8)),
                1..4,
            )
        ) {
            let mut source = String::from("<A");
            for (i, (sep, pieces)) in attributes.iter().enumerate() {
                source.push_str(&format!(" a{i}{sep}=\"{}\"", pieces.concat()));
            }
            source.push_str(" />");
            let refers_to_no_character = source.contains("&#xD800;") || source.contains("&#x110000;");
            match parse(&source) {
                Ok(doc) => {
                    proptest::prop_assert!(!refers_to_no_character, "{source:?}");
                    let root = doc.root_element();
                    for attr in root.attributes() {
                        proptest::prop_assert!(attribute(root, attr.name()).is_some());
                    }
                }
                Err(_) => proptest::prop_assert!(refers_to_no_character || source.contains("&#0;"), "{source:?}"),
            }
        }
    }

    /// A character reference to a code point that is no Unicode scalar value,
    /// which `roxmltree` reads as `U+FFFD`, refuses the document wherever it
    /// stands; one that names a character, `U+FFFD` itself included, does not.
    #[test]
    fn a_reference_to_no_character_refuses_the_document() {
        for refused in [
            "<A v=\"&#xD800;\" />",
            "<A v=\"&#55296;\" />",
            "<A v=\"&#x110000;\" />",
            "<A v=\"&#4294967295;\" />",
            "<A>&#xDFFF;</A>",
            // Only text inside a comment, but refused all the same: a decline.
            "<A><!-- &#xD800; --></A>",
        ] {
            #[allow(clippy::disallowed_methods)] // what roxmltree alone admits
            let admitted = Document::parse(refused).is_ok();
            assert!(admitted, "{refused}");
            assert!(parse(refused).is_err(), "{refused}");
        }
        for admitted in [
            "<A v=\"&#xFFFD;&#x10FFFF;&#9;\" />",
            "<A><!-- &#xyz; &#99999999999; --></A>",
        ] {
            assert!(parse(admitted).is_ok(), "{admitted}");
        }
    }

    /// [`parse`]'s scan reads each byte a bounded number of times: comment
    /// text holding a reference's opening again and again, never closed,
    /// parses in what a linear scan takes, where one reading to the next `;`
    /// each time took 18 s on 200,000 of them.
    #[test]
    fn the_reference_scan_is_linear() {
        for opening in ["&#", "&#1", "&#x"] {
            let source = format!("<A><!-- {} --></A>", opening.repeat(200_000));
            let started = std::time::Instant::now();
            assert!(parse(&source).is_ok());
            let took = started.elapsed();
            assert!(took.as_secs() < 3, "{opening}: {took:?}");
        }
    }

    /// [`attribute`] relies on roxmltree refusing a DTD, so that no reference
    /// it decodes can be an entity a document declared.
    #[test]
    fn a_document_with_a_dtd_does_not_parse() {
        let source = "<!DOCTYPE A [<!ENTITY e \"x\">]><A a=\"&e;\" />";
        assert!(parse(source).is_err());
    }

    #[test]
    fn malformed_text_fails_as_roxmltree_does() {
        let source = String::from("<Project>");
        let ours =
            ParsedDocument::parse(source.clone(), TextDigest::of(&source)).expect_err("malformed");
        #[allow(clippy::disallowed_methods)] // the error roxmltree gives
        let theirs = Document::parse(&source).expect_err("malformed");
        assert_eq!(ours, theirs);
    }
}
