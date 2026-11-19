//! Hostile requests on the wire to our own oracles ([`Kind::Wire`]).
//!
//! The oracles speak JSON lines: one request object on one line, one answer
//! line back, matched by position. A request that is blank, spans lines, or
//! is read differently by the two ends does more than fail: it shifts every
//! later answer onto the wrong request. So both ends are subjects here: the
//! Rust driver must refuse to send what the oracle would misread, and the
//! oracle must refuse what it is sent wrongly, with an error on that
//! request's own line.
//!
//! [`mutations`] derives the hostile requests from a real one.

use serde_json::Value;

use super::{Alphabet, Dimension, Entry, Kind};

/// The compact one-line JSON of `value`.
fn line(value: &Value) -> Vec<u8> {
    serde_json::to_vec(value).expect("a JSON value serialises")
}

/// An object written by hand from `fields`, so that a key can occur twice.
fn object_of(fields: &[(&str, &Value)]) -> Vec<u8> {
    let mut out = vec![b'{'];
    for (i, (key, value)) in fields.iter().enumerate() {
        if i > 0 {
            out.push(b',');
        }
        out.extend(line(&Value::String((*key).to_owned())));
        out.push(b':');
        out.extend(line(value));
    }
    out.push(b'}');
    out
}

/// A value of another JSON type than `value`'s, as close to it as that
/// allows: the text of a boolean or a number, a string wrapped in an array.
fn of_another_type(value: &Value) -> Value {
    match value {
        Value::Null => Value::Bool(false),
        Value::Bool(b) => Value::String(b.to_string()),
        Value::Number(n) => Value::String(n.to_string()),
        Value::String(s) => Value::Array(vec![Value::String(s.clone())]),
        Value::Array(_) => Value::Object(serde_json::Map::new()),
        Value::Object(_) => Value::Array(Vec::new()),
    }
}

/// The hostile requests derived from `request`, each the bytes of what is
/// sent in place of its one line (with no line terminator of its own).
///
/// # Panics
///
/// If `request` is not an object with at least one field: there is then no
/// field to mistype, drop or repeat.
pub fn mutations(request: &Value) -> Alphabet<Vec<u8>> {
    let object = request
        .as_object()
        .filter(|o| !o.is_empty())
        .expect("a request is a JSON object with at least one field");
    let fields: Vec<(&str, &Value)> = object.iter().map(|(k, v)| (k.as_str(), v)).collect();
    let good = line(request);
    let with = |suffix: &[u8]| [good.as_slice(), suffix].concat();
    let mut entries = Vec::new();
    let mut add = |dimension, value: Vec<u8>, why| {
        entries.push(Entry {
            dimension,
            value,
            why,
        });
    };

    add(Dimension::BlankLine, Vec::new(), "an empty line");
    add(
        Dimension::BlankLine,
        b"  \t".to_vec(),
        "a line of spaces and a tab",
    );

    add(
        Dimension::MultiLine,
        serde_json::to_vec_pretty(request).expect("a JSON value serialises"),
        "the request pretty-printed over several lines",
    );
    add(
        Dimension::MultiLine,
        [good.as_slice(), b"\n", good.as_slice()].concat(),
        "two requests where one is expected",
    );
    add(
        Dimension::MultiLine,
        {
            // A bare carriage return after the opening brace: whitespace to
            // JSON, and a line end to .NET's `ReadLine`.
            let mut out = good.clone();
            out.insert(1, b'\r');
            out
        },
        "a bare carriage return between tokens: whitespace to JSON, a line end to .NET's line reader",
    );

    for (space, why) in [
        (
            "\u{a0}",
            "a trailing no-break space, which .NET trims and JSON does not allow",
        ),
        ("\u{2028}", "a trailing line separator"),
        ("\u{3000}", "a trailing ideographic space"),
        ("\u{85}", "a trailing NEL"),
        ("\u{b}", "a trailing vertical tab"),
    ] {
        add(
            Dimension::TrailingUnicodeWhitespace,
            with(space.as_bytes()),
            why,
        );
    }
    add(
        Dimension::TrailingUnicodeWhitespace,
        ["\u{feff}".as_bytes(), good.as_slice()].concat(),
        "a leading byte order mark",
    );

    for (i, (key, value)) in fields.iter().enumerate() {
        let replaced = |new: &Value| {
            let mut all = fields.clone();
            all[i] = (key, new);
            object_of(&all)
        };
        add(
            Dimension::WrongType,
            replaced(&of_another_type(value)),
            "a field of another JSON type",
        );
        if !value.is_null() {
            add(
                Dimension::WrongType,
                replaced(&Value::Null),
                "a field that is null",
            );
        }

        let mut without = fields.clone();
        without.remove(i);
        add(
            Dimension::MissingField,
            object_of(&without),
            "a field left out",
        );

        let other = of_another_type(value);
        let mut first = vec![(*key, &other)];
        first.extend(fields.iter().copied());
        add(
            Dimension::DuplicateKey,
            object_of(&first),
            "a key twice, the real value last",
        );
        let mut last = fields.clone();
        last.push((key, &other));
        add(
            Dimension::DuplicateKey,
            object_of(&last),
            "a key twice, the real value first",
        );

        let recased: String = key
            .chars()
            .map(|c| {
                if c.is_ascii_lowercase() {
                    c.to_ascii_uppercase()
                } else {
                    c.to_ascii_lowercase()
                }
            })
            .collect();
        if recased != *key && !object.contains_key(&recased) {
            let mut all = fields.clone();
            all[i] = (recased.as_str(), value);
            add(
                Dimension::UnknownField,
                object_of(&all),
                "a known field's name in another case, which a case-insensitive reader takes for it",
            );
        }
    }
    let extra = Value::Bool(true);
    let mut unknown = fields.clone();
    unknown.push(("borzoiUnknownField", &extra));
    add(
        Dimension::UnknownField,
        object_of(&unknown),
        "a field no oracle knows",
    );

    add(
        Dimension::NotAnObject,
        line(&Value::Array(vec![request.clone()])),
        "the request inside an array",
    );
    add(
        Dimension::NotAnObject,
        line(&Value::String(String::from_utf8_lossy(&good).into_owned())),
        "the request as a JSON string",
    );
    add(Dimension::NotAnObject, b"null".to_vec(), "null");
    add(Dimension::NotAnObject, b"0".to_vec(), "a number");

    add(
        Dimension::NotJson,
        good[..good.len() - 1].to_vec(),
        "the request without its closing brace",
    );
    add(
        Dimension::NotJson,
        with(b"x"),
        "the request and a trailing word",
    );
    add(
        Dimension::NotJson,
        {
            let mut out = good.clone();
            let end = out.len() - 1;
            out.insert(end, b',');
            out
        },
        "a trailing comma",
    );
    add(Dimension::NotJson, with(b"\0"), "a trailing NUL");
    add(
        Dimension::NotJson,
        with(b"\xff"),
        "a byte that is not UTF-8",
    );
    add(
        Dimension::NotJson,
        String::from_utf8_lossy(&good)
            .replace('"', "'")
            .into_bytes(),
        "single quotes",
    );
    add(
        Dimension::NotJson,
        [b"/* c */".as_slice(), good.as_slice()].concat(),
        "a comment, which lenient readers skip",
    );

    Alphabet::new(Kind::Wire, entries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn request() -> Value {
        json!({"op": "check", "file": "/tmp/a.fs", "strict": true, "version": 8, "defines": ["A"]})
    }

    #[test]
    fn the_mutations_cover_every_wire_dimension() {
        assert_eq!(mutations(&request()).kind(), Kind::Wire);
        // A request of one field has every dimension too.
        mutations(&json!({"op": "x"}));
    }

    /// Each mutation is what its dimension says, by a strict reader's lights.
    #[test]
    fn each_mutation_is_what_its_dimension_says() {
        let request = request();
        let object = request.as_object().unwrap();
        for entry in mutations(&request).entries() {
            let parsed: Result<Value, _> = serde_json::from_slice(&entry.value);
            let text = String::from_utf8_lossy(&entry.value);
            match entry.dimension {
                Dimension::BlankLine => assert!(text.trim().is_empty()),
                Dimension::MultiLine => {
                    assert!(text.contains(['\n', '\r']), "{text:?}")
                }
                Dimension::TrailingUnicodeWhitespace => {
                    assert!(parsed.is_err(), "serde_json must refuse {text:?}");
                    // .NET's `Trim` removes all but the byte order mark.
                    let trimmed = text.trim().trim_start_matches('\u{feff}');
                    assert_eq!(
                        serde_json::from_str::<Value>(trimmed).unwrap(),
                        request,
                        "{}",
                        entry.why
                    );
                }
                Dimension::WrongType => {
                    let got = parsed.unwrap();
                    let got = got.as_object().unwrap();
                    assert_eq!(got.len(), object.len());
                    let differing: Vec<_> = object.iter().filter(|(k, v)| got[*k] != **v).collect();
                    assert_eq!(differing.len(), 1, "{text}");
                    let (key, real) = differing[0];
                    assert_ne!(
                        std::mem::discriminant(&got[key]),
                        std::mem::discriminant(real)
                    );
                }
                Dimension::MissingField => {
                    let got = parsed.unwrap();
                    let got = got.as_object().unwrap();
                    assert_eq!(got.len(), object.len() - 1);
                    assert!(got.iter().all(|(k, v)| object[k] == *v));
                }
                Dimension::UnknownField => {
                    let got = parsed.unwrap();
                    let got = got.as_object().unwrap();
                    // A known field renamed, or a field added.
                    assert!(got.len() == object.len() || got.len() == object.len() + 1);
                    assert_eq!(got.keys().filter(|k| !object.contains_key(*k)).count(), 1);
                }
                Dimension::DuplicateKey => {
                    // serde_json keeps the last of two keys.
                    let got = parsed.unwrap();
                    assert_eq!(got.as_object().unwrap().len(), object.len());
                    let keys = object
                        .keys()
                        .filter(|k| text.matches(&format!("{:?}:", k.as_str())).count() == 2)
                        .count();
                    assert_eq!(keys, 1, "{text}");
                }
                Dimension::NotAnObject => assert!(!parsed.unwrap().is_object()),
                Dimension::NotJson => assert!(parsed.is_err(), "{text:?}"),
                other => panic!("{other} is no wire dimension"),
            }
            if entry.dimension != Dimension::MultiLine {
                assert!(
                    !entry.value.contains(&b'\n') && !entry.value.contains(&b'\r'),
                    "only a multi-line mutation holds a line break: {text:?}"
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "a JSON object with at least one field")]
    fn a_request_that_is_no_object_is_refused() {
        mutations(&json!([1]));
    }
}
