//! FCS's range for an identifier token.
//!
//! The tree spells every parenthesised operator name the same way: `(+)`,
//! `( + )`, `( * )` and the glued `(*)` are each `LPAREN_TOK`, an `IDENT_TOK`
//! holding the operator, and `RPAREN_TOK`, so a name accessor returns the bare
//! operator for all of them. FCS ranges all but one of those names over the
//! operator alone. The exception is the glued `(*)`: both lexers read it as
//! one token (`(*` would otherwise open a block comment; FCS's
//! `LPAREN_STAR_RPAREN`), and FCS's `opName` production ranges the identifier
//! over that whole token (`pars.fsy`, `opName: LPAREN_STAR_RPAREN`), giving
//! its parentheses zero-width trivia ranges at either end.
//!
//! The parser emits the glued token as the same three tokens as the spaced
//! spelling, with nothing between them. Nothing else can produce a `(`, `*`
//! and `)` with no trivia between them, since any other `(*` opens a comment;
//! with the `walk-reference` feature every parse checks that against the raw
//! token table. So [`fcs_ident_range`] reads the glued spelling off adjacency.
//!
//! This is a reading of the tree for consumers that must report what FCS
//! reports (definition and use ranges); it changes nothing in the tree, and the
//! token keeps its text `*`.

use super::{NodeOrToken, SyntaxElement, SyntaxKind, SyntaxToken, TextRange};

/// The range FCS gives the identifier `token` names: the token's own range,
/// except for the `*` of a glued `(*)`, which FCS ranges over all three
/// characters.
///
/// The glued spelling is an `IDENT_TOK` reading `*` whose previous sibling is
/// an `LPAREN_TOK` ending where it starts and whose next sibling is an
/// `RPAREN_TOK` starting where it ends. An operator name written with any
/// space, comment or line break inside its parentheses keeps the operator's
/// own range, as FCS's does.
pub fn fcs_ident_range(token: &SyntaxToken) -> TextRange {
    let own = token.text_range();
    match glued_star_parens(token) {
        Some((open, close)) => TextRange::new(open.text_range().start(), close.text_range().end()),
        None => own,
    }
}

/// The parentheses of a glued `(*)` around `token`, if it is that `*`.
fn glued_star_parens(token: &SyntaxToken) -> Option<(SyntaxToken, SyntaxToken)> {
    if token.kind() != SyntaxKind::IDENT_TOK || token.text() != "*" {
        return None;
    }
    let open = sibling_token(token.prev_sibling_or_token()?)?;
    let close = sibling_token(token.next_sibling_or_token()?)?;
    let own = token.text_range();
    (open.kind() == SyntaxKind::LPAREN_TOK
        && open.text_range().end() == own.start()
        && open.text_range().len() == 1.into()
        && close.kind() == SyntaxKind::RPAREN_TOK
        && close.text_range().start() == own.end()
        && close.text_range().len() == 1.into())
    .then_some((open, close))
}

fn sibling_token(element: SyntaxElement) -> Option<SyntaxToken> {
    match element {
        NodeOrToken::Token(t) => Some(t),
        NodeOrToken::Node(_) => None,
    }
}
