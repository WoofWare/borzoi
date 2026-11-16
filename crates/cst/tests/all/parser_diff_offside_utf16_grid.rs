//! Differential test (`parser::parse` vs FCS): offside alignment after
//! non-ASCII text.
//!
//! FCS's lexbuf counts a column in UTF-16 code units, so `é` (two UTF-8 bytes)
//! advances it by one and `𝔸` (four bytes, a surrogate pair) by two. Every
//! offside comparison is made in that scale, so a context anchored after a
//! non-ASCII character on its line, or a token that follows one on its own
//! line, is aligned where its UTF-16 column says, not where its byte column
//! does.
//!
//! The grid puts a [`PREFIX`] before the anchor token of each layout-sensitive
//! [`CONSTRUCT`] (placement A), or a [`COMMENT`] before the first token aligned
//! with it on a later line (placement B), and sets every continuation line at
//! the anchor's UTF-16 column shifted by each of [`DELTAS`]: one column left
//! of the construct's own alignment, on it, and one right. Each prefix with a
//! non-ASCII character has an ASCII control of the same UTF-16 width, so a cell
//! that diverges only with the non-ASCII spelling is this defect.
//!
//! Each cell is held to FCS three ways: the parse verdict, the normalised tree
//! when both accept, and the set of offside FS0058 diagnostics, whose message
//! embeds the limiting context's position in FCS's columns. Nothing here
//! hard-codes which cells FCS accepts.

use std::collections::BTreeSet;
use std::io::Write;

use borzoi_cst::parser::parse;
use tempfile::NamedTempFile;

use crate::common::{fcs_ast_batch, fcs_diagnostics, fcs_parse_had_errors, normalised_ast};

/// Text that may precede an anchor on its line, in an expression, a pattern
/// or a declaration name.
struct Prefix {
    text: &'static str,
    /// Whether it spells a name, so it may stand where a module or type name
    /// does.
    is_name: bool,
}

/// Placement A's prefixes: ASCII controls and non-ASCII text in each position
/// FCS's lexer can hold it, a quoted identifier, a bare identifier, a string
/// and a comment, with characters of one and two UTF-16 units and of two,
/// three and four UTF-8 bytes.
const PREFIX: &[Prefix] = &[
    Prefix {
        text: "``e``",
        is_name: true,
    },
    Prefix {
        text: "``ee``",
        is_name: true,
    },
    Prefix {
        text: "``é``",
        is_name: true,
    },
    Prefix {
        text: "``中``",
        is_name: true,
    },
    Prefix {
        text: "``𝔸``",
        is_name: true,
    },
    Prefix {
        text: "aé",
        is_name: true,
    },
    Prefix {
        text: "\"é𝔸\"",
        is_name: false,
    },
    Prefix {
        text: "(*𝔸*)a",
        is_name: true,
    },
];

/// Placement B's comments, each followed by a space, before the first
/// continuation line's token: an ASCII control and the two non-ASCII widths.
const COMMENT: &[&str] = &["(*e*)", "(*é*)", "(*𝔸*)"];

/// Shifts of every continuation line from the construct's own alignment.
const DELTAS: [i32; 3] = [-1, 0, 1];

/// A layout-sensitive construct: the text that opens it on the anchor's line,
/// whose first token is the anchor, and each later line with its column
/// relative to the anchor's.
struct Construct {
    name: &'static str,
    first: &'static str,
    rest: &'static [(i32, &'static str)],
}

/// Expression constructs, spanning the offside contexts whose alignment a
/// continuation line is measured against: `let rec … and`, match and function
/// clauses, `then`/`elif`/`else`, record fields and list elements, sequential
/// expressions, a `let` body, `try … with`/`finally`, a `match` whose `with`
/// is on its own line, an infix operator's undentation grace, and the bodies
/// of `fun` and `while`.
///
/// A lambda's body may undent as far as the enclosing context allows, so that
/// construct opens with a `let` whose column is the boundary its body
/// straddles.
const CONSTRUCT: &[Construct] = &[
    Construct {
        name: "let rec … and",
        first: "let rec f = (1)",
        rest: &[(0, "and g = (2) in (3)")],
    },
    Construct {
        name: "match clauses",
        first: "match 1 with",
        rest: &[(0, "| 1 -> 2"), (0, "| _ -> 3")],
    },
    Construct {
        name: "function clauses",
        first: "function",
        rest: &[(0, "| 1 -> 2"), (0, "| _ -> 3")],
    },
    Construct {
        name: "then/else",
        first: "if true",
        rest: &[(0, "then 1"), (0, "else 2")],
    },
    Construct {
        name: "else",
        first: "if true then 1",
        rest: &[(0, "else 2")],
    },
    Construct {
        name: "elif",
        first: "if true then 1",
        rest: &[(0, "elif false then 2"), (0, "else 3")],
    },
    Construct {
        name: "record fields",
        first: "{ X = 1",
        rest: &[(2, "Y = 2 }")],
    },
    Construct {
        name: "list elements",
        first: "[ 1",
        rest: &[(2, "2 ]")],
    },
    Construct {
        name: "sequential",
        first: "id 1",
        rest: &[(0, "id 2")],
    },
    Construct {
        name: "let body",
        first: "let x = 1",
        rest: &[(0, "x")],
    },
    Construct {
        name: "try/with",
        first: "try 1",
        rest: &[(0, "with _ -> 2")],
    },
    Construct {
        name: "try/finally",
        first: "try 1",
        rest: &[(0, "finally ()")],
    },
    Construct {
        name: "match/with",
        first: "match 1",
        rest: &[(0, "with _ -> 2")],
    },
    Construct {
        name: "infix grace",
        first: "1",
        rest: &[(-2, "+ 2")],
    },
    Construct {
        name: "fun body",
        first: "let g = fun x ->",
        rest: &[(1, "x in g")],
    },
    Construct {
        name: "while body",
        first: "while false do",
        rest: &[(1, "()")],
    },
];

/// Module-body constructs, for the declaration wrapper.
const DECL_CONSTRUCT: &[Construct] = &[
    Construct {
        name: "let/let",
        first: "let x = 1",
        rest: &[(0, "let y = 2")],
    },
    Construct {
        name: "type/type",
        first: "type U = A",
        rest: &[(0, "type V = B")],
    },
];

/// Type-body constructs, for the type wrapper.
const TYPE_CONSTRUCT: &[Construct] = &[
    Construct {
        name: "record type fields",
        first: "{ X: int",
        rest: &[(2, "Y: int }")],
    },
    Construct {
        name: "union cases",
        first: "| A",
        rest: &[(0, "| B")],
    },
];

/// Where a construct sits: the text before its anchor on the anchor's line,
/// with `@` for the prefix, the text closing it after its last line, and the
/// constructs it takes.
struct Wrapper {
    head: &'static str,
    tail: &'static str,
    constructs: &'static [Construct],
    /// Whether the prefix stands as a name, so only [`Prefix::is_name`] ones
    /// fit.
    names_only: bool,
}

const WRAPPER: &[Wrapper] = &[
    Wrapper {
        head: "let a = (f (@) (",
        tail: "))",
        constructs: CONSTRUCT,
        names_only: false,
    },
    Wrapper {
        head: "let @ = ",
        tail: "",
        constructs: CONSTRUCT,
        names_only: false,
    },
    Wrapper {
        head: "let a = @, ",
        tail: "",
        constructs: CONSTRUCT,
        names_only: false,
    },
    Wrapper {
        head: "module @ = ",
        tail: "",
        constructs: DECL_CONSTRUCT,
        names_only: true,
    },
    Wrapper {
        head: "type @ = ",
        tail: "",
        constructs: TYPE_CONSTRUCT,
        names_only: true,
    },
];

/// Cells that diverge from FCS for reasons outside this grid's subject: their
/// ASCII controls diverge too. Each is `(wrapper head, construct name, delta,
/// issue)`, and every cell it names must still diverge, so an entry cannot
/// outlive its defect.
const KNOWN: &[(&str, &str, i32, u32)] = &[
    ("let a = (f (@) (", "let body", 1, 951),
    ("let @ = ", "let body", 1, 951),
    ("let a = @, ", "let body", -1, 951),
    ("let a = @, ", "let body", 0, 951),
    ("let a = @, ", "let body", 1, 951),
    ("module @ = ", "let/let", -1, 558),
    ("module @ = ", "type/type", -1, 558),
];

/// The column of the end of `text`, in UTF-16 code units: FCS's scale.
fn utf16_width(text: &str) -> usize {
    text.encode_utf16().count()
}

/// One grid source: `construct` in `wrapper` with `prefix` before its anchor,
/// its continuation lines shifted by `delta`, and `comment` (if any) before
/// the first continuation line's token. `None` when a shift would put a line
/// left of column 0.
fn cell(
    wrapper: &Wrapper,
    prefix: &str,
    construct: &Construct,
    delta: i32,
    comment: Option<&str>,
) -> Option<String> {
    let head = wrapper.head.replace('@', prefix);
    let anchor = utf16_width(&head) as i32;
    let mut source = format!("{head}{}", construct.first);
    for (i, (rel, text)) in construct.rest.iter().enumerate() {
        let col = anchor + rel + delta;
        let lead = match comment.filter(|_| i == 0) {
            Some(comment) => format!("{comment} "),
            None => String::new(),
        };
        let spaces = usize::try_from(col - utf16_width(&lead) as i32).ok()?;
        source.push('\n');
        source.push_str(&" ".repeat(spaces));
        source.push_str(&lead);
        source.push_str(text);
    }
    source.push_str(wrapper.tail);
    source.push('\n');
    Some(source)
}

/// One grid source, with the construct it shifts (the liveness group) and the
/// whole cell's description.
struct Cell {
    construct: &'static str,
    /// The [`KNOWN`] entry's issue, if the cell is one.
    known: Option<u32>,
    what: String,
    source: String,
}

/// Every grid cell.
fn cells() -> Vec<Cell> {
    let mut out = Vec::new();
    for wrapper in WRAPPER {
        for construct in wrapper.constructs {
            let group = format!("{:?} / {}", wrapper.head, construct.name);
            let mut push = |what: String, delta: i32, source: Option<String>| {
                let known = KNOWN
                    .iter()
                    .find(|k| (k.0, k.1, k.2) == (wrapper.head, construct.name, delta))
                    .map(|k| k.3);
                out.extend(source.map(|source| Cell {
                    construct: construct.name,
                    known,
                    what,
                    source,
                }));
            };
            for delta in DELTAS {
                for prefix in PREFIX.iter().filter(|p| p.is_name || !wrapper.names_only) {
                    push(
                        format!("A {group} / prefix {} / delta {delta}", prefix.text),
                        delta,
                        cell(wrapper, prefix.text, construct, delta, None),
                    );
                }
                for comment in COMMENT {
                    push(
                        format!("B {group} / comment {comment} / delta {delta}"),
                        delta,
                        cell(wrapper, "a", construct, delta, Some(comment)),
                    );
                }
            }
        }
    }
    out
}

/// What FCS says of a source that this grid grades: whether it accepts it,
/// its normalised tree if it does (as text), and its offside FS0058s as
/// `(byte span, message)`.
#[derive(PartialEq, Eq)]
struct FcsView {
    accepts: bool,
    tree: Option<String>,
    offside: BTreeSet<(usize, usize, String)>,
}

/// FS0058 has other flavours ("Nested type definitions are not allowed"),
/// which carry no column; only the offside one is this grid's subject.
fn is_offside(message: &str) -> bool {
    message.contains("offside of context started at position")
}

/// FCS's [`FcsView`] of `source`, with its `ast` record.
fn fcs_view(source: &str) -> (FcsView, String) {
    let mut tmp = NamedTempFile::with_suffix(".fs").expect("create tempfile");
    tmp.write_all(source.as_bytes()).expect("write source");
    let json = fcs_ast_batch(tmp.path());
    let offside = fcs_diagnostics(&json, source, 58)
        .into_iter()
        .filter(|(_, message)| is_offside(message))
        .map(|(span, message)| (span.start, span.end, message))
        .collect();
    let accepts = !fcs_parse_had_errors(&json);
    let view = FcsView {
        accepts,
        tree: accepts.then(|| format!("{:?}", normalised_ast::normalise_fcs_dump(&json))),
        offside,
    };
    (view, json)
}

/// `source` with every non-ASCII character respelled as as many `e`s as it
/// has UTF-8 bytes: the same bytes in the same places, every column now
/// counted the same in bytes and in UTF-16 units. FCS reads this twin as a
/// filter counting bytes reads `source`.
fn byte_twin(source: &str) -> String {
    source
        .chars()
        .flat_map(|c| {
            let n = if c.is_ascii() { 0 } else { c.len_utf8() };
            std::iter::once(c)
                .filter(char::is_ascii)
                .chain(std::iter::repeat_n('e', n))
        })
        .collect()
}

/// Every way `source` diverges from FCS, and whether the cell discriminates
/// a filter that counts columns in bytes: FCS's view of the [`byte_twin`]
/// differs from its view of `source` with the tree's names respelled the same
/// way.
fn check(source: &str) -> (bool, Vec<String>) {
    let (fcs, json) = fcs_view(source);
    let discriminates = !source.is_ascii() && {
        let respelled = FcsView {
            accepts: fcs.accepts,
            tree: fcs.tree.as_deref().map(byte_twin),
            offside: fcs.offside.clone(),
        };
        fcs_view(&byte_twin(source)).0 != respelled
    };
    let ours = parse(source);
    let we_accept = ours.errors.is_empty();
    let mut failures = Vec::new();
    if we_accept != fcs.accepts {
        failures.push(format!(
            "verdict: we {}, FCS {}; our errors: {:?}",
            if we_accept { "accept" } else { "reject" },
            if fcs.accepts { "accepts" } else { "rejects" },
            ours.errors,
        ));
    } else if fcs.accepts {
        let fcs = normalised_ast::normalise_fcs_dump(&json);
        let rust = normalised_ast::normalise_parse(&ours);
        if rust != fcs {
            failures.push(format!("tree:\n  ours: {rust:?}\n  fcs:  {fcs:?}"));
        }
    }
    let our_offside: BTreeSet<(usize, usize, String)> = ours
        .errors
        .iter()
        .chain(ours.warnings.iter())
        .filter(|e| is_offside(&e.message))
        .map(|e| (e.span.start, e.span.end, e.message.clone()))
        .collect();
    if our_offside != fcs.offside {
        failures.push(format!(
            "FS0058:\n  ours: {our_offside:?}\n  fcs:  {:?}",
            fcs.offside
        ));
    }
    (discriminates, failures)
}

/// Run every cell, collecting every divergence rather than stopping at the
/// first, and assert the grid is live: each construct, in some wrapper, has a
/// cell that discriminates a filter counting columns in bytes, so its shifts
/// straddle a boundary that column scale moves.
#[test]
fn offside_alignment_after_non_ascii_text_matches_fcs() {
    let cells = cells();
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get().min(8));
    let chunk = cells.len().div_ceil(threads);
    let results: Vec<(bool, Vec<String>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = cells
            .chunks(chunk)
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter()
                        .map(|cell| check(&cell.source))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("grid worker"))
            .collect()
    });

    let mut failures = Vec::new();
    let mut known_agreeing = Vec::new();
    let mut discriminating: std::collections::BTreeMap<&str, usize> = Default::default();
    for (cell, (discriminates, cell_failures)) in cells.iter().zip(&results) {
        *discriminating.entry(cell.construct).or_default() += usize::from(*discriminates);
        match cell.known {
            Some(issue) if cell_failures.is_empty() => {
                known_agreeing.push(format!("#{issue}: {}", cell.what));
            }
            Some(_) => {}
            None => {
                for failure in cell_failures {
                    failures.push(format!("{}\n{}{failure}\n", cell.what, cell.source));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} divergences from FCS over {} cells:\n\n{}",
        failures.len(),
        cells.len(),
        failures.join("\n"),
    );
    assert!(
        known_agreeing.is_empty(),
        "these cells are listed in KNOWN but now agree with FCS; remove their entries:\n{}",
        known_agreeing.join("\n"),
    );
    let blind: Vec<&str> = discriminating
        .iter()
        .filter(|&(_, &n)| n == 0)
        .map(|(&construct, _)| construct)
        .collect();
    assert!(
        blind.is_empty(),
        "no cell of these constructs, in any wrapper, reads differently to FCS when its columns are \
         counted in bytes, so they grade nothing about the column scale:\n{}\n\
         discriminating cells per construct: {discriminating:#?}",
        blind.join("\n"),
    );
}
