//! An XML document parsed once and held with its text, so that evaluations
//! can share it: [`crate::observed::ImportDocuments`] keeps one per imported
//! file across evaluations, and the item pass replays deferred groups
//! against the document the property pass walked. Every document the crate
//! reads is parsed through [`parse`], and its attributes and text read through
//! [`attribute`] and [`text`], as MSBuild reads them.

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
            let (decoded, after) = reference(rest);
            value.push(decoded);
            folded.push(decoded);
            rest = after;
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

/// The text node `node` as MSBuild reads it: its source text with entity and
/// character references decoded, and line ends as written.
///
/// MSBuild's `XmlTextReader` has `Normalization` off, so a carriage return in
/// element content reaches it as written and a CRLF is two characters; the
/// project's own reader then takes an element's text as `InnerText`, the
/// concatenation of its text nodes (`Utilities.GetXmlNodeInnerContents`).
/// `roxmltree` applies XML's line-end folding (XML 1.0 §2.11), mostly: it
/// reads a CRLF, and a lone CR before anything but a reference, as a line
/// feed, and keeps a lone CR before a reference or ending the text.
///
/// `None` for a node that is not text, and for one holding a CDATA section,
/// which `roxmltree` merges into the adjacent text while keeping only the
/// first piece's range (`element_content` reads such an element from its
/// source). The reading is checked against `roxmltree`'s with every line
/// end taken out of both, so anything else it reads apart declines too.
pub fn text<'a>(node: Node<'a, '_>) -> Option<Cow<'a, str>> {
    if !node.is_text() {
        return None;
    }
    #[allow(clippy::disallowed_methods)] // roxmltree's folded reading, to check ours by
    let folded_by_roxmltree = node.text()?;
    let source = node.document().input_text();
    let raw = source.get(node.range())?;
    // A CDATA section first in the node is in its range; one after the first
    // piece starts where the range ends.
    if raw.contains("<![CDATA[") || source[node.range().end..].starts_with("<![CDATA[") {
        return None;
    }
    if !raw.contains(['&', '\r']) {
        return (raw == folded_by_roxmltree).then_some(Cow::Borrowed(folded_by_roxmltree));
    }
    let value = decode(raw);
    // Which line ends `roxmltree` folds turns on what follows them, a
    // reference's character included, so the check leaves them out.
    (without_line_ends(&value) == without_line_ends(folded_by_roxmltree)).then_some(value)
}

/// `text` with every line end taken out.
fn without_line_ends(text: &str) -> String {
    text.replace(['\r', '\n'], "")
}

/// Text from a document [`parse`] admitted, its references decoded.
fn decode(raw: &str) -> Cow<'_, str> {
    if !raw.contains('&') {
        return Cow::Borrowed(raw);
    }
    let mut value = String::with_capacity(raw.len());
    let mut rest = raw;
    while let Some(c) = rest.chars().next() {
        if c == '&' {
            let (decoded, after) = reference(rest);
            value.push(decoded);
            rest = after;
        } else {
            value.push(c);
            rest = &rest[c.len_utf8()..];
        }
    }
    Cow::Owned(value)
}

/// One child of an element as MSBuild's XML reader reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Content<'a> {
    /// Text, its references decoded and its line ends as written. It is
    /// `whitespace` when it is nothing but XML whitespace, which the reader
    /// reports as a whitespace node.
    Text {
        value: Cow<'a, str>,
        whitespace: bool,
    },
    /// A CDATA section's content, verbatim.
    CData(&'a str),
    /// A comment's content, verbatim.
    Comment(&'a str),
}

/// Whether `text` is nothing but XML whitespace: space, tab, CR and LF (a
/// non-breaking space is content).
fn is_xml_whitespace(text: &str) -> bool {
    text.bytes()
        .all(|b| matches!(b, b' ' | b'\t' | b'\r' | b'\n'))
}

/// A piece of content markup as it stands in the source: text, or a CDATA
/// section's or a comment's content.
enum Piece<'a> {
    Text(&'a str),
    CData(&'a str),
    Comment(&'a str),
}

/// `inner`, content holding no element or processing instruction, cut into
/// its pieces. `None` for any other markup, for a section that is not
/// closed, and for a comment holding `--` (which XML forbids): an element's
/// content in a document [`parse`] admitted has none of them, and a fragment
/// holding one is not well formed.
fn pieces(inner: &str) -> Option<Vec<Piece<'_>>> {
    let mut out = Vec::new();
    let mut rest = inner;
    while !rest.is_empty() {
        if let Some(after) = rest.strip_prefix("<!--") {
            // A comment ends at its first `--`, which must be followed by `>`.
            let end = after.find("--")?;
            if !after[end + 2..].starts_with('>') {
                return None;
            }
            out.push(Piece::Comment(&after[..end]));
            rest = &after[end + 3..];
        } else if let Some(after) = rest.strip_prefix("<![CDATA[") {
            let end = after.find("]]>")?;
            out.push(Piece::CData(&after[..end]));
            rest = &after[end + 3..];
        } else if rest.starts_with('<') {
            return None;
        } else {
            let end = rest.find('<').unwrap_or(rest.len());
            out.push(Piece::Text(&rest[..end]));
            rest = &rest[end..];
        }
    }
    Some(out)
}

/// Whether a run of element text spelt `raw`, reading `value`, is a whitespace
/// node to MSBuild's XML reader: its value is XML whitespace, and no decimal
/// character reference spells any of it. Literal whitespace and hexadecimal
/// references make a whitespace node, which MSBuild drops; one decimal
/// reference makes the whole run text, which it keeps. Pinned against
/// `dotnet msbuild` 10.0 in `fsproj_property_table_diff`: `&#32;`, ` &#32; `
/// and `&#x20;&#32;` are kept whole, `&#x20;`, `&#xA;&#xD;` and
/// `<TAB>&#x9;<TAB>` dropped.
fn run_is_whitespace_node(raw: &str, value: &str) -> bool {
    let decimal_reference = raw
        .match_indices("&#")
        .any(|(at, _)| raw[at + 2..].starts_with(|c: char| c.is_ascii_digit()));
    is_xml_whitespace(value) && !decimal_reference
}

/// The children of `element` as MSBuild's XML reader reports them, in order:
/// text, CDATA sections and comments. A run of text that is nothing but XML
/// whitespace is a whitespace node, which MSBuild, loading a project without
/// preserving whitespace, drops ([`run_is_whitespace_node`]).
///
/// `roxmltree` merges a CDATA section into the text beside it and keeps only
/// the first piece's range, so this reads the element's source. The reading
/// is checked against `roxmltree`'s with every line end taken out of both
/// (`roxmltree` folds them, where MSBuild reads them as written; see
/// [`text`]).
///
/// `None` for an element holding an element or a processing instruction.
pub(crate) fn element_content<'input>(element: Node<'_, 'input>) -> Option<Vec<Content<'input>>> {
    if element
        .children()
        .any(|child| child.is_element() || child.is_pi())
    {
        return None;
    }
    if !element.has_children() {
        return Some(Vec::new());
    }
    let source: &'input str = element.document().input_text();
    let whole = &source[element.range()];
    // The start tag ends at the first `>` outside an attribute's quotes; the
    // end tag starts at the last `</`, as nothing follows it but its name.
    let mut quote = None;
    let mut start = None;
    for (at, byte) in whole.bytes().enumerate() {
        match quote {
            Some(open) if byte == open => quote = None,
            Some(_) => {}
            None if matches!(byte, b'"' | b'\'') => quote = Some(byte),
            None if byte == b'>' => {
                start = Some(at + 1);
                break;
            }
            None => {}
        }
    }
    let end = whole.rfind("</")?;
    let inner = whole.get(start?..end)?;
    let mut content = Vec::new();
    // Every text and CDATA section as read here, to check against roxmltree.
    let mut ours = String::new();
    for piece in pieces(inner)? {
        match piece {
            Piece::Text(raw) => {
                let value = decode(raw);
                ours.push_str(&value);
                if run_is_whitespace_node(raw, &value) {
                    continue;
                }
                content.push(Content::Text {
                    value,
                    whitespace: false,
                });
            }
            Piece::CData(text) => {
                ours.push_str(text);
                content.push(Content::CData(text));
            }
            Piece::Comment(text) => content.push(Content::Comment(text)),
        }
    }
    #[allow(clippy::disallowed_methods)] // roxmltree's folded reading, to check ours by
    let theirs: String = element
        .children()
        .filter(Node::is_text)
        .filter_map(|n| n.text())
        .collect();
    (without_line_ends(&ours) == without_line_ends(&theirs)).then_some(content)
}

/// The children MSBuild reads from `fragment`, a value it stores as an
/// element's content: `Utilities.SetXmlNodeInnerContents` parses a value
/// holding a `<` as XML, keeping its whitespace, and stores it as text where
/// that fails.
///
/// `None` unless the fragment certainly parses and holds only text, CDATA
/// sections and comments, so for a fragment holding an element, a processing
/// instruction, a `&` (whose reading turns on whether it starts a reference,
/// and to what), `]]>` in text, or a malformed comment or section.
pub(crate) fn fragment_content(fragment: &str) -> Option<Vec<Content<'_>>> {
    pieces(fragment)?
        .into_iter()
        .map(|piece| match piece {
            Piece::Text(text) if text.contains('&') || text.contains("]]>") => None,
            Piece::Text(text) => Some(Content::Text {
                value: Cow::Borrowed(text),
                whitespace: is_xml_whitespace(text),
            }),
            Piece::CData(text) => Some(Content::CData(text)),
            Piece::Comment(text) => Some(Content::Comment(text)),
        })
        .collect()
}

/// What MSBuild reads from an element whose children are `children`
/// (`Utilities.GetXmlNodeInnerContents`): its inner text or its inner XML.
///
/// - No children, or one whitespace node, read as `""`; one text or CDATA
///   section reads as its value.
/// - Otherwise the inner text (every text and CDATA section, concatenated)
///   where the inner XML holds no markup but comments, or starts with a CDATA
///   section after any leading whitespace (.NET's `char.IsWhiteSpace`, the
///   set [`char::is_whitespace`] tests).
/// - Otherwise the inner XML: each text with `&`, `<` and `>` spelt as
///   entities and each CDATA section and comment re-spelt around its content,
///   everything else as it is (`XmlTextWriter`).
///
/// Pinned against `dotnet msbuild` 10.0 in `fsproj_property_table_diff`.
/// `None` where the inner XML would spell a character as a reference
/// (`XmlTextWriter` writes U+0001 as `&#x1;`); no document [`parse`] admits
/// holds one.
pub(crate) fn inner_contents(children: &[Content<'_>]) -> Option<String> {
    let inner_text = || {
        children
            .iter()
            .filter_map(|child| match child {
                Content::Text { value, .. } => Some(&**value),
                Content::CData(text) => Some(*text),
                Content::Comment(_) => None,
            })
            .collect::<String>()
    };
    match children {
        []
        | [
            Content::Text {
                whitespace: true, ..
            },
        ] => return Some(String::new()),
        [Content::Text { value, .. }] => return Some(value.to_string()),
        [Content::CData(text)] => return Some((*text).to_owned()),
        _ => {}
    }
    // The inner XML's markup is its comments and CDATA sections, and only a
    // CDATA section is markup other than a comment.
    if !children.iter().any(|c| matches!(c, Content::CData(_))) {
        return Some(inner_text());
    }
    let starts_with_cdata = children
        .iter()
        .find(|child| {
            !matches!(child, Content::Text { value, .. } if value.chars().all(char::is_whitespace))
        })
        .is_some_and(|child| matches!(child, Content::CData(_)));
    if starts_with_cdata {
        return Some(inner_text());
    }
    let mut xml = String::new();
    for child in children {
        match child {
            Content::Text { value, .. } => {
                for c in value.chars() {
                    match c {
                        '&' => xml.push_str("&amp;"),
                        '<' => xml.push_str("&lt;"),
                        '>' => xml.push_str("&gt;"),
                        '\t' | '\n' | '\r' => xml.push(c),
                        c if c < ' ' || matches!(c, '\u{fffe}' | '\u{ffff}') => return None,
                        c => xml.push(c),
                    }
                }
            }
            Content::CData(text) => {
                xml.push_str("<![CDATA[");
                xml.push_str(text);
                xml.push_str("]]>");
            }
            Content::Comment(text) => {
                xml.push_str("<!--");
                xml.push_str(text);
                xml.push_str("-->");
            }
        }
    }
    Some(xml)
}

/// The reference that `rest` starts with, decoded, and the text after it.
fn reference(rest: &str) -> (char, &str) {
    // [`parse`] parsed the document, so every reference in it is one of XML's
    // five entities or a well-formed character reference to a Unicode scalar
    // value.
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
    (decoded, &rest[end + 1..])
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
    /// Parse `text`, whose digest is `digest`. A text that does not parse is
    /// handed back with `roxmltree`'s error.
    pub fn parse(text: String, digest: TextDigest) -> Result<Self, (String, roxmltree::Error)> {
        debug_assert_eq!(digest, TextDigest::of(&text));
        let cell = Cell::try_new_or_recover(text, |text| parse(text))?;
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
            .and_then(|n| n.first_child())
            .and_then(text);
        assert_eq!(a.as_deref(), Some("x"));
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

    /// The text of each of `element`'s text children as [`text`] reads it,
    /// concatenated, or `None` if it declines any.
    fn element_text(element: Node<'_, '_>) -> Option<String> {
        element
            .children()
            .filter(Node::is_text)
            .map(|child| text(child).map(Cow::into_owned))
            .collect()
    }

    /// Each body's reading, and roxmltree's folded one beside it.
    #[test]
    fn element_text_reads_its_line_ends_as_written() {
        for (body, msbuild, folded) in [
            ("a\r\nb", "a\r\nb", "a\nb"),
            ("a\rb", "a\rb", "a\nb"),
            ("a\r\r\nb", "a\r\r\nb", "a\n\nb"),
            ("a\n\rb", "a\n\rb", "a\n\nb"),
            ("\r\n  x\r\n", "\r\n  x\r\n", "\n  x\n"),
            ("a&#13;&#10;b", "a\r\nb", "a\r\nb"),
            ("a&#xD;\nb", "a\r\nb", "a\r\nb"),
            ("a&amp;\r\nb&lt;", "a&\r\nb<", "a&\nb<"),
            (
                "caf\u{e9}\r\u{85}\u{2028}",
                "caf\u{e9}\r\u{85}\u{2028}",
                "caf\u{e9}\n\u{85}\u{2028}",
            ),
            ("plain", "plain", "plain"),
            // roxmltree keeps a lone CR before a reference or ending the text.
            ("a\r&#97;", "a\ra", "a\ra"),
            ("a&amp;\r", "a&\r", "a&\r"),
            ("a\r&#10;", "a\r\n", "a\r\n"),
        ] {
            let source = format!("<A>{body}</A>");
            let doc = parse(&source).unwrap();
            let child = doc.root_element().first_child().unwrap();
            assert_eq!(text(child).as_deref(), Some(msbuild), "{body:?}");
            #[allow(clippy::disallowed_methods)] // the folded reading, for contrast
            let theirs = child.text();
            assert_eq!(theirs, Some(folded), "{body:?}");
        }
        // Text split by a comment: each piece keeps its own line ends.
        let doc = parse("<A>a\r<!-- c\r\n -->\nb</A>").unwrap();
        assert_eq!(element_text(doc.root_element()).as_deref(), Some("a\r\nb"));
        // A node that is not text has no text to read.
        assert_eq!(text(doc.root_element()), None);
    }

    /// A CDATA section holding text declines every text node it touches:
    /// `roxmltree` merges it with the text beside it and keeps the first
    /// piece's range.
    #[test]
    fn element_text_declines_cdata() {
        for body in [
            "<![CDATA[a\r\nb]]>",
            "x<![CDATA[y]]>",
            "<![CDATA[y]]>x",
            "x\r\n<![CDATA[y]]>z",
            // Content the check alone would not see: only a line end, or nothing.
            "x<![CDATA[\r\n]]>",
            "x<![CDATA[]]>",
            "<![CDATA[]]>x",
        ] {
            let source = format!("<A>{body}</A>");
            let doc = parse(&source).unwrap();
            let root = doc.root_element();
            assert!(root.children().any(|c| c.is_text()), "{body:?}");
            for child in root.children() {
                assert_eq!(text(child), None, "{body:?}");
            }
        }
    }

    proptest::proptest! {
        /// Any text, each character spelt any legal way (a line end as
        /// itself or as a reference), split into pieces by comments, reads
        /// back as itself, so [`text`]'s check that its folding is
        /// roxmltree's holds throughout.
        #[test]
        fn every_spelling_of_element_text_reads_back_as_it(
            pieces in proptest::collection::vec(
                proptest::collection::vec(
                    (
                        proptest::sample::select(vec![
                            'a', ' ', '\t', '\n', '\r', '<', '>', '&', '"', '\'', '%', ';',
                            '$', '=', '\u{e9}', '\u{a0}', '\u{85}', '\u{2028}', '\u{1d11e}',
                        ]),
                        0u8..3,
                    ),
                    0..12,
                ),
                1..4,
            ),
        ) {
            let value: String = pieces.iter().flatten().map(|(c, _)| *c).collect();
            let spelt: Vec<String> = pieces
                .iter()
                .map(|piece| piece.iter().map(|(c, how)| spell(*c, *how, '\0')).collect())
                .collect();
            let source = format!("<A>{}</A>", spelt.join("<!-- c\r\n -->"));
            let doc = parse(&source).unwrap();
            proptest::prop_assert_eq!(element_text(doc.root_element()), Some(value));
        }
    }

    /// A piece of element content the generator below writes.
    #[derive(Clone, Debug)]
    enum Written {
        /// Characters, each with how [`spell`] spells it.
        Text(Vec<(char, u8)>),
        Comment(String),
        CData(String),
    }

    fn written() -> impl proptest::strategy::Strategy<Value = Written> {
        let text_chars = vec![
            'a',
            ' ',
            '\t',
            '\n',
            '\r',
            '<',
            '>',
            '&',
            '"',
            ']',
            '\u{a0}',
            '\u{85}',
            '\u{1d11e}',
        ];
        let markup_chars = vec![
            'a', ' ', '\r', '\n', '<', '>', '&', '!', '-', '[', ']', '/', '?', '\u{e9}',
        ];
        proptest::prop_oneof![
            proptest::collection::vec((proptest::sample::select(text_chars), 0u8..3), 0..6)
                .prop_map(Written::Text),
            proptest::collection::vec(proptest::sample::select(markup_chars.clone()), 0..6)
                .prop_map(|cs| cs.into_iter().collect::<String>())
                .prop_filter("a comment holds no `--` and ends in no `-`", |c| {
                    !c.contains("--") && !c.ends_with('-')
                })
                .prop_map(Written::Comment),
            proptest::collection::vec(proptest::sample::select(markup_chars), 0..6)
                .prop_map(|cs| cs.into_iter().collect::<String>())
                .prop_filter("a CDATA section holds no `]]>`", |c| !c.contains("]]>"))
                .prop_map(Written::CData),
        ]
    }

    proptest::proptest! {
        /// Any content of text (each character spelt any legal way), comments
        /// and CDATA sections, written into an element, reads back as the
        /// pieces written: adjacent text as one run, and a run of XML
        /// whitespace dropped unless a decimal reference spells some of it.
        /// So the reading of the element's source agrees with roxmltree's
        /// throughout.
        #[test]
        fn element_content_reads_back_what_was_written(
            written in proptest::collection::vec(written(), 0..6),
            attribute in proptest::sample::select(vec!["", " a='>'", " b=\"'>\" c='\"'"]),
        ) {
            let mut source = format!("<A{attribute}>");
            // Each piece expected, as its kind and its text.
            let mut expected = Some(Vec::new());
            // The run of text being written: its value and its spelling.
            let mut run = (String::new(), String::new());
            let mut spelt_text = String::new();
            let end_run = |run: &mut (String, String), expected: &mut Option<Vec<(&str, String)>>| {
                let (value, spelt) = std::mem::take(run);
                // A run of whitespace is dropped unless a decimal reference
                // spells some of it ([`spell`] writes a hexadecimal one as
                // `&#x…;`, and `&` never as itself).
                let decimal = spelt.split("&#").skip(1).any(|r| !r.starts_with('x'));
                if spelt.is_empty() || (is_xml_whitespace(&value) && !decimal) {
                    return;
                }
                if let Some(expected) = expected {
                    expected.push(("text", value));
                }
            };
            for piece in &written {
                match piece {
                    Written::Text(chars) => {
                        for (c, how) in chars {
                            let spelt = spell(*c, *how, '\0');
                            source.push_str(&spelt);
                            run.0.push(*c);
                            run.1.push_str(&spelt);
                        }
                    }
                    Written::Comment(text) | Written::CData(text) => {
                        spelt_text.push_str(&run.1);
                        end_run(&mut run, &mut expected);
                        let (kind, open, close) = match piece {
                            Written::Comment(_) => ("comment", "<!--", "-->"),
                            _ => ("cdata", "<![CDATA[", "]]>"),
                        };
                        source.push_str(&format!("{open}{text}{close}"));
                        if let Some(expected) = &mut expected {
                            expected.push((kind, text.clone()));
                        }
                    }
                }
            }
            spelt_text.push_str(&run.1);
            end_run(&mut run, &mut expected);
            source.push_str("</A>");
            let Ok(doc) = parse(&source) else {
                // Text may not hold `]]>`.
                proptest::prop_assert!(spelt_text.contains("]]>"), "{:?}", source);
                return Ok(());
            };
            let read = element_content(doc.root_element()).map(|content| {
                content
                    .into_iter()
                    .map(|piece| match piece {
                        Content::Text { value, whitespace } => {
                            assert!(!whitespace);
                            ("text", value.into_owned())
                        }
                        Content::Comment(text) => ("comment", text.to_owned()),
                        Content::CData(text) => ("cdata", text.to_owned()),
                    })
                    .collect::<Vec<_>>()
            });
            proptest::prop_assert_eq!(read, expected, "{:?}", source);
        }
    }

    /// The fragments an attribute may hold: each reads as the pieces MSBuild
    /// parses from it, its whitespace kept; and each the parse may refuse, or
    /// whose reading turns on a reference, declines.
    #[test]
    fn fragment_content_reads_only_what_certainly_parses() {
        let text = |value: &'static str| Content::Text {
            value: Cow::Borrowed(value),
            whitespace: is_xml_whitespace(value),
        };
        for (fragment, expected) in [
            ("<![CDATA[a]]>", vec![Content::CData("a")]),
            (
                " <!--c--> y",
                vec![text(" "), Content::Comment("c"), text(" y")],
            ),
            (
                "x>y<![CDATA[<!--]]>",
                vec![text("x>y"), Content::CData("<!--")],
            ),
            ("<!---->", vec![Content::Comment("")]),
        ] {
            assert_eq!(fragment_content(fragment), Some(expected), "{fragment:?}");
        }
        for fragment in [
            "a<b",
            "<x/>",
            "<?p q?>",
            "<!--a--b-->",
            "<!--a--->",
            "<!--",
            "<![CDATA[",
            "a&b<!--c-->",
            "a&amp;<!--c-->",
            "a]]><!--c-->",
        ] {
            assert_eq!(fragment_content(fragment), None, "{fragment:?}");
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
        let (text, ours) =
            ParsedDocument::parse(source.clone(), TextDigest::of(&source)).expect_err("malformed");
        #[allow(clippy::disallowed_methods)] // the error roxmltree gives
        let theirs = Document::parse(&source).expect_err("malformed");
        assert_eq!(ours, theirs);
        assert_eq!(text, source, "the text is handed back");
    }
}
