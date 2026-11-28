//! The exhaustive child views (`tools/astgen/src/views.rs`): each yields every
//! non-trivia child of its node, in order, as a variant of a closed enum, and
//! refuses a child its table does not declare where the filtering accessors
//! would skip it. The parse-time `view-reference` check holds the table to
//! every parse this suite makes; these cases pin what a view yields.

use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{
    AstNode, LongIdent, LongIdentChild, LongIdentPat, LongIdentPatChild, LongIdentPatToken,
    LongIdentToken, SyntaxKind,
};

fn first<N: AstNode>(src: &str) -> (N, bool) {
    let parsed = parse(src);
    let node = parsed
        .root
        .descendants()
        .find_map(N::cast)
        .unwrap_or_else(|| panic!("{src:?} holds no such node"));
    (node, parsed.errors.is_empty())
}

/// What a view yields, spelled: a node child by its variant, a token by its
/// variant and text.
fn spell_pat(children: &[LongIdentPatChild]) -> Vec<String> {
    children
        .iter()
        .map(|c| match c {
            LongIdentPatChild::LongIdent(_) => "LongIdent".to_string(),
            LongIdentPatChild::ActivePatName(_) => "ActivePatName".to_string(),
            LongIdentPatChild::TyparDecls(_) => "TyparDecls".to_string(),
            LongIdentPatChild::NamePatPairs(_) => "NamePatPairs".to_string(),
            LongIdentPatChild::Arg(_) => "Arg".to_string(),
            LongIdentPatChild::Token(LongIdentPatToken::Error, t) => {
                format!("Error {:?}", t.text())
            }
        })
        .collect()
}

fn spell_ident(children: &[LongIdentChild]) -> Vec<String> {
    children
        .iter()
        .map(|c| match c {
            LongIdentChild::ActivePatName(_) => "ActivePatName".to_string(),
            LongIdentChild::Token(kind, t) => format!("{kind:?} {:?}", t.text()),
        })
        .collect()
}

#[test]
fn a_member_head_s_children_are_yielded_in_order() {
    let (head, clean) = first::<LongIdentPat>("type T() =\n    member x.M<'a> (y: 'a) = 1\n");
    assert!(clean);
    assert_eq!(
        spell_pat(&head.view().unwrap()),
        ["LongIdent", "TyparDecls", "Arg"]
    );
}

/// An active pattern's name beside the head, which `LongIdentPat::head` does
/// not report and `LongIdentPat::args` skips, is a child of its own.
#[test]
fn an_active_pattern_name_beside_the_head_is_a_child() {
    let (head, clean) =
        first::<LongIdentPat>("type System.String with\n    member x.(|A|_|) y = None\n");
    assert!(clean);
    assert_eq!(
        spell_pat(&head.view().unwrap()),
        ["LongIdent", "ActivePatName", "Arg"]
    );
}

/// The lex filter's zero-width layout virtual before an adjacent argument is
/// a token child, declared and yielded like any other.
#[test]
fn a_zero_width_layout_token_is_a_child() {
    let (head, clean) = first::<LongIdentPat>("type T =\n  member this.M(x) = x\n");
    assert!(clean);
    assert_eq!(
        spell_pat(&head.view().unwrap()),
        ["LongIdent", "Error \"\"", "Arg"]
    );
}

#[test]
fn a_long_identifier_s_tokens_and_active_pattern_are_yielded_without_trivia() {
    let (li, clean) = first::<LongIdent>("let f = A . (* c *) B.(|C|_|)\n");
    assert!(clean);
    assert_eq!(
        spell_ident(&li.view().unwrap()),
        [
            "Ident \"A\"",
            "Dot \".\"",
            "Ident \"B\"",
            "Dot \".\"",
            "ActivePatName"
        ]
    );
    let (head, clean) =
        first::<LongIdentPat>("type System.String with\n    member x.``A``.(+) y = 1\n");
    assert!(clean);
    let kinds: Vec<LongIdentToken> = head
        .head()
        .expect("a head")
        .view()
        .unwrap()
        .into_iter()
        .map(|c| match c {
            LongIdentChild::Token(kind, _) => kind,
            LongIdentChild::ActivePatName(_) => panic!("no active pattern here"),
        })
        .collect();
    use LongIdentToken::{Dot, Ident, LParen, RParen};
    assert_eq!(kinds, [Ident, Dot, Ident, Dot, LParen, Ident, RParen]);
}

/// Recovery can leave debris inside a long identifier, which `idents()` skips
/// (reading `t.t.Name` off `t.) t.Name`). The view refuses it, naming it.
#[test]
fn debris_the_accessors_skip_is_refused() {
    let src = "let g = f (Some t.) t.Name\n";
    let (li, clean) = first::<LongIdent>(src);
    assert!(!clean);
    let idents: Vec<String> = li.idents().map(|t| t.text().to_string()).collect();
    assert_eq!(idents, ["t", "t", "Name"], "the accessor skips the debris");
    let refused = li.view().expect_err("the view refuses it");
    assert_eq!(refused.parent, SyntaxKind::LONG_IDENT);
    assert_eq!(refused.kind, SyntaxKind::ERROR);
    assert!(refused.is_token);
    let (start, end) = (
        usize::from(refused.range.start()),
        usize::from(refused.range.end()),
    );
    assert_eq!(&src[start..end], ")");
}
