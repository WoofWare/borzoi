//! Hostile ways to write a value in an XML document
//! ([`Kind::XmlSpelling`]).
//!
//! A hostile value has to be written into a project file before any reader
//! meets it, and XML offers several spellings of one text. [`spell`] writes
//! `text` each way; the plain way is [`escape`]. What a conforming XML reader
//! makes of a spelling and what MSBuild makes of it differ (MSBuild
//! normalises neither attribute values nor line ends), which is the reason
//! the spellings are a kind of their own: the same value must be read the
//! same however it was written.
//!
//! XML 1.0 has no spelling at all for some characters (a NUL, most control
//! characters). [`escape`] refuses them; a hostile spelling writes them
//! anyway and says the document is malformed ([`Spelt::well_formed`]), which
//! both readers must then refuse.

use std::sync::OnceLock;

use super::{Alphabet, Dimension, Entry, Kind};

/// Where the text goes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Place {
    /// The content of an element.
    Element,
    /// The value of an attribute written between double quotes.
    Attribute,
}

/// One way to write a text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum How {
    /// Every character as a decimal reference.
    DecimalRefs,
    /// Every character as a hexadecimal reference.
    HexRefs,
    /// Every character as a hexadecimal reference with upper-case digits and
    /// leading zeros.
    PaddedHexRefs,
    /// One CDATA section (elements only).
    Cdata,
    /// Escaped text with an empty comment between each two characters
    /// (elements only).
    CommentSplit,
    /// Escaped text with tabs and line breaks written as themselves.
    LiteralWhitespace,
}

/// A text as XML source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spelt {
    /// The source text: an element's content, or an attribute's value without
    /// its quotes.
    pub xml: String,
    /// Whether the source is well-formed XML 1.0. It is not when the text
    /// holds a character XML 1.0 has no spelling for.
    pub well_formed: bool,
}

/// Whether XML 1.0 can hold `c` at all (its `Char` production).
pub fn representable(c: char) -> bool {
    matches!(c, '\t' | '\n' | '\r' | '\u{20}'..='\u{d7ff}' | '\u{e000}'..='\u{fffd}' | '\u{10000}'..)
}

fn escaped_char(c: char, place: Place, literal_whitespace: bool, out: &mut String) {
    match c {
        '&' => out.push_str("&amp;"),
        '<' => out.push_str("&lt;"),
        '>' => out.push_str("&gt;"),
        '"' if place == Place::Attribute => out.push_str("&quot;"),
        '\t' | '\n' | '\r' if !literal_whitespace => {
            out.push_str(&format!("&#{};", c as u32));
        }
        c => out.push(c),
    }
}

/// The plain spelling of `text`: markup escaped, and tabs and line breaks as
/// character references, so that every reader reads `text` back.
///
/// # Errors
///
/// The first character XML 1.0 cannot hold, if `text` has one.
pub fn escape(text: &str, place: Place) -> Result<String, char> {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        if !representable(c) {
            return Err(c);
        }
        escaped_char(c, place, false, &mut out);
    }
    Ok(out)
}

/// `text` written `how` in `place`, or `None` where the place has no such
/// spelling (an attribute holds no CDATA section and no comment).
pub fn spell(text: &str, how: How, place: Place) -> Option<Spelt> {
    let well_formed = text.chars().all(representable);
    let xml = match how {
        How::DecimalRefs => text.chars().map(|c| format!("&#{};", c as u32)).collect(),
        How::HexRefs => text
            .chars()
            .map(|c| format!("&#x{:x};", c as u32))
            .collect(),
        How::PaddedHexRefs => text
            .chars()
            .map(|c| format!("&#x{:06X};", c as u32))
            .collect(),
        How::Cdata => {
            if place == Place::Attribute {
                return None;
            }
            // `]]>` cannot sit inside a section: end one between the
            // brackets and start another.
            format!("<![CDATA[{}]]>", text.replace("]]>", "]]]]><![CDATA[>"))
        }
        How::CommentSplit => {
            if place == Place::Attribute {
                return None;
            }
            let mut out = String::new();
            for (i, c) in text.chars().enumerate() {
                if i > 0 {
                    out.push_str("<!---->");
                }
                escaped_char(c, place, false, &mut out);
            }
            out
        }
        How::LiteralWhitespace => {
            let mut out = String::new();
            for c in text.chars() {
                escaped_char(c, place, true, &mut out);
            }
            out
        }
    };
    Some(Spelt { xml, well_formed })
}

const TABLE: &[(Dimension, How, &str)] = &[
    (
        Dimension::CharRef,
        How::DecimalRefs,
        "decimal references: `&#10;` is a line feed that no line-based scan of the file sees",
    ),
    (Dimension::CharRef, How::HexRefs, "hexadecimal references"),
    (
        Dimension::CharRef,
        How::PaddedHexRefs,
        "hexadecimal references with upper-case digits and leading zeros",
    ),
    (
        Dimension::Cdata,
        How::Cdata,
        "a CDATA section: `&#10;` inside one is seven characters, not a line feed",
    ),
    (
        Dimension::CommentSplit,
        How::CommentSplit,
        "comments inside the text, which MSBuild reads around",
    ),
    (
        Dimension::LiteralWhitespace,
        How::LiteralWhitespace,
        "tabs and line breaks as themselves, which XML normalises in an attribute and at a line end and MSBuild does not",
    ),
];

/// The alphabet of hostile spellings.
pub fn alphabet() -> &'static Alphabet<How> {
    static ALPHABET: OnceLock<Alphabet<How>> = OnceLock::new();
    ALPHABET.get_or_init(|| {
        Alphabet::new(
            Kind::XmlSpelling,
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
    use proptest::prelude::*;

    /// What `roxmltree` reads back from `spelt`, written in `place`.
    fn read_back(spelt: &str, place: Place) -> Result<String, roxmltree::Error> {
        let document = match place {
            Place::Element => format!("<p>{spelt}</p>"),
            Place::Attribute => format!("<p a=\"{spelt}\"/>"),
        };
        let parsed = roxmltree::Document::parse(&document)?;
        let root = parsed.root_element();
        Ok(match place {
            Place::Element => root.children().filter_map(|n| n.text()).collect::<String>(),
            Place::Attribute => root.attribute("a").unwrap_or_default().to_owned(),
        })
    }

    /// `text` with its line ends and tabs made spaces: what is left to
    /// compare once a reader has normalised literal whitespace its own way
    /// (XML says how, and readers differ on a bare carriage return).
    fn whitespace_folded(text: &str) -> String {
        text.replace("\r\n", " ").replace(['\r', '\n', '\t'], " ")
    }

    #[test]
    fn the_alphabet_covers_every_spelling_dimension() {
        assert_eq!(alphabet().kind(), Kind::XmlSpelling);
    }

    proptest! {
        /// The plain spelling reads back as the text; each hostile spelling
        /// of a representable text is well-formed and reads back as the text
        /// (but for the normalisation XML applies to literal whitespace).
        #[test]
        fn every_spelling_reads_back(
            text in "[a-c<>&\"' \t\r\n;%$()\\]\\[!-]{0,12}",
            place in prop_oneof![Just(Place::Element), Just(Place::Attribute)],
        ) {
            let plain = escape(&text, place).expect("representable");
            prop_assert_eq!(read_back(&plain, place).unwrap(), text.clone());
            for entry in alphabet().entries() {
                let Some(spelt) = spell(&text, entry.value, place) else {
                    prop_assert_eq!(place, Place::Attribute);
                    prop_assert!(matches!(entry.value, How::Cdata | How::CommentSplit));
                    continue;
                };
                prop_assert!(spelt.well_formed);
                let read = read_back(&spelt.xml, place)
                    .unwrap_or_else(|e| panic!("{:?} of {text:?}: {e}", entry.value));
                match entry.value {
                    // Written raw, whitespace is the reader's to normalise;
                    // nothing else may move.
                    How::LiteralWhitespace | How::Cdata => prop_assert_eq!(
                        whitespace_folded(&read),
                        whitespace_folded(&text),
                        "{:?}",
                        entry.value
                    ),
                    _ => prop_assert_eq!(read, text.clone(), "{:?}", entry.value),
                }
            }
        }
    }

    #[test]
    fn a_character_xml_cannot_hold_is_refused_plainly_and_flagged_when_spelt() {
        assert_eq!(escape("a\u{1}b", Place::Element), Err('\u{1}'));
        assert_eq!(escape("a\0b", Place::Attribute), Err('\0'));
        for entry in alphabet().entries() {
            if let Some(spelt) = spell("a\u{1}b", entry.value, Place::Element) {
                assert!(!spelt.well_formed);
                assert!(
                    read_back(&spelt.xml, Place::Element).is_err(),
                    "{:?} wrote a forbidden character a conforming reader accepts",
                    entry.value
                );
            }
        }
    }
}
