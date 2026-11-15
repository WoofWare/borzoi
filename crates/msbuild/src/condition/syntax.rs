//! MSBuild's condition *parser*, as a recogniser: whether MSBuild's own
//! `Scanner` and `Parser` (`src/Build/Evaluation/Conditionals/` in
//! dotnet/msbuild) throw on a condition's text.
//!
//! MSBuild parses a whole condition before it evaluates any of it, and the
//! parse reads text, not values: a parse error makes the condition illegal
//! whatever the properties hold and however `And`/`Or` would have
//! short-circuited (`false And (tr ue)` and `true Or 'abc` are both rejected;
//! `tests/condition_diff.rs` pins them). That is what makes this half of
//! [`super::Outcome::Illegal`] independent of values.
//!
//! This is a port of the syntax alone, token for token and production for
//! production, with nothing evaluated. Its answer is [`Syntax::Unknown`] where
//! the scan depends on more than the text, or on what this port cannot know
//! for certain:
//!
//! - an item list (`@(`) or metadata (`%(`) reference, whose legality depends
//!   on where the condition sits (`'@(I)' == ''` is legal on an item and
//!   illegal on a property, even behind a false `And`);
//! - a character outside ASCII where the scanner classifies characters
//!   (`char.IsLetter`, `char.IsDigit` and `char.IsWhiteSpace` are Unicode
//!   predicates); inside a quoted string the scanner looks only for ASCII
//!   delimiters, so any character may sit there;
//! - nesting past [`MAX_CONDITION_NESTING`](super::MAX_CONDITION_NESTING), or
//!   more than [`MAX_TOKENS`] tokens. The port recurses per nesting level, and
//!   MSBuild's parser recurses per `And`/`Or` operand as well, so a long
//!   enough chain overflows MSBuild's stack rather than making it throw.
//!
//! Like MSBuild, the scanner reads one token ahead of the parser, so a parse
//! error stops the scan before it reaches whatever follows: `tr ue @(x)` is
//! rejected without the item list being looked at.

/// MSBuild's verdict on a condition's syntax, where the port can tell.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Syntax {
    /// MSBuild's parser accepts the text.
    Parses,
    /// MSBuild's scanner or parser throws on the text.
    Rejects,
    /// The port cannot tell (see the module docs).
    Unknown,
}

/// Most tokens the port scans before it stops with [`Syntax::Unknown`].
/// MSBuild evaluates 10,000 nested parentheses without overflowing
/// (`tests/deep_nesting.rs`), some 40,000 frames of its parser; this many
/// tokens is far fewer frames than that whatever their shape.
const MAX_TOKENS: usize = 4096;

/// Run MSBuild's parser over `source`.
pub(super) fn msbuild_parse(source: &str) -> Syntax {
    let mut recogniser = Recogniser {
        s: source.as_bytes(),
        p: 0,
        look: Tok::Start,
        tokens: 0,
        depth: 0,
    };
    match recogniser.parse() {
        Ok(()) => Syntax::Parses,
        Err(Stop::Rejects) => Syntax::Rejects,
        Err(Stop::Unknown) => Syntax::Unknown,
    }
}

/// Why the port stopped before the end of the text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Stop {
    Rejects,
    Unknown,
}

type Scan<T> = Result<T, Stop>;

/// `Token.TokenType`, less the item-list and metadata kinds, which stop the
/// port before they are made.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tok {
    /// Before the first `advance` (MSBuild's null lookahead).
    Start,
    Comma,
    LParen,
    RParen,
    Property,
    String,
    Numeric,
    Function,
    Not,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
    And,
    Or,
    Eof,
}

struct Recogniser<'a> {
    s: &'a [u8],
    /// `Scanner._parsePoint`.
    p: usize,
    /// `Scanner._lookahead`.
    look: Tok,
    tokens: usize,
    /// Parentheses and `!`s enclosing the factor being parsed.
    depth: usize,
}

/// `char.IsWhiteSpace` on ASCII.
fn is_white(b: u8) -> bool {
    matches!(b, 0x09..=0x0d | b' ')
}

/// `XmlUtilities.IsValidSubsequentElementNameCharacter` on ASCII.
fn is_name_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || matches!(b, b'_' | b'-')
}

impl Recogniser<'_> {
    // -- Parser.cs -------------------------------------------------------

    /// `Parser.Parse`.
    fn parse(&mut self) -> Scan<()> {
        self.advance()?;
        self.expr()?;
        if self.look != Tok::Eof {
            return Err(Stop::Rejects);
        }
        Ok(())
    }

    /// `Parser.Expr` with `ExprPrime`, whose recursion is a loop here.
    fn expr(&mut self) -> Scan<()> {
        self.boolean_term()?;
        if self.look != Tok::Eof {
            while !self.same(Tok::Eof)? && self.same(Tok::Or)? {
                self.boolean_term()?;
            }
        }
        Ok(())
    }

    /// `Parser.BooleanTerm` with `BooleanTermPrime`, likewise a loop.
    fn boolean_term(&mut self) -> Scan<()> {
        self.relational_expr()?;
        if self.look != Tok::Eof {
            while self.look != Tok::Eof && self.same(Tok::And)? {
                self.relational_expr()?;
            }
        }
        Ok(())
    }

    /// `Parser.RelationalExpr`: a factor, optionally compared with another.
    fn relational_expr(&mut self) -> Scan<()> {
        self.factor()?;
        let relational = [Tok::Lt, Tok::Gt, Tok::Lte, Tok::Gte, Tok::Eq, Tok::Neq];
        if relational.contains(&self.look) {
            self.advance()?;
            self.factor()?;
        }
        Ok(())
    }

    /// `Parser.Factor`. Every path that does not return a node throws, so
    /// this either succeeds or stops.
    fn factor(&mut self) -> Scan<()> {
        if self.arg()? {
            return Ok(());
        }
        if self.same(Tok::Function)? {
            if !self.same(Tok::LParen)? {
                return Err(Stop::Rejects);
            }
            // `Arglist` and `Args`: an argument may be absent (`f(,)` parses).
            if self.look != Tok::RParen {
                loop {
                    self.arg()?;
                    if !self.same(Tok::Comma)? {
                        break;
                    }
                }
            }
            return if self.same(Tok::RParen)? {
                Ok(())
            } else {
                Err(Stop::Rejects)
            };
        }
        if self.same(Tok::LParen)? {
            self.nested(Self::expr)?;
            return if self.same(Tok::RParen)? {
                Ok(())
            } else {
                Err(Stop::Rejects)
            };
        }
        if self.same(Tok::Not)? {
            return self.nested(Self::factor);
        }
        Err(Stop::Rejects)
    }

    /// `Parser.Arg`: whether the lookahead is an operand, consuming it if so.
    fn arg(&mut self) -> Scan<bool> {
        if matches!(self.look, Tok::String | Tok::Numeric | Tok::Property) {
            self.advance()?;
            return Ok(true);
        }
        Ok(false)
    }

    /// `Parser.Same`: consume the lookahead if it is `token`.
    fn same(&mut self, token: Tok) -> Scan<bool> {
        if self.look == token {
            self.advance()?;
            return Ok(true);
        }
        Ok(false)
    }

    /// Run `parse` one nesting level down.
    fn nested(&mut self, parse: fn(&mut Self) -> Scan<()>) -> Scan<()> {
        if self.depth >= super::MAX_CONDITION_NESTING {
            return Err(Stop::Unknown);
        }
        self.depth += 1;
        let parsed = parse(self);
        self.depth -= 1;
        parsed
    }

    // -- Scanner.cs ------------------------------------------------------

    /// `Scanner.Advance`: scan the next token into the lookahead.
    fn advance(&mut self) -> Scan<()> {
        if self.look == Tok::Eof {
            return Ok(());
        }
        self.tokens += 1;
        if self.tokens > MAX_TOKENS {
            return Err(Stop::Unknown);
        }
        self.skip_white()?;
        let s = self.s;
        let Some(&c) = s.get(self.p) else {
            self.look = Tok::Eof;
            return Ok(());
        };
        let next = s.get(self.p + 1).copied();
        let (token, width) = match c {
            b',' => (Tok::Comma, 1),
            b'(' => (Tok::LParen, 1),
            b')' => (Tok::RParen, 1),
            b'$' => return self.property(),
            // `%(` is metadata and `@(` an item list, each legal in some
            // contexts and not others. Any other `%` or `@` fails to open one,
            // which is an error in every context.
            b'%' | b'@' if next == Some(b'(') => return Err(Stop::Unknown),
            b'%' | b'@' => return Err(Stop::Rejects),
            b'!' if next == Some(b'=') => (Tok::Neq, 2),
            b'!' => (Tok::Not, 1),
            b'>' if next == Some(b'=') => (Tok::Gte, 2),
            b'>' => (Tok::Gt, 1),
            b'<' if next == Some(b'=') => (Tok::Lte, 2),
            b'<' => (Tok::Lt, 1),
            b'=' if next == Some(b'=') => (Tok::Eq, 2),
            b'=' => return Err(Stop::Rejects),
            b'\'' => return self.quoted_string(),
            _ => return self.remaining(),
        };
        self.look = token;
        self.p += width;
        Ok(())
    }

    /// `Scanner.SkipWhiteSpace`. A character outside ASCII may be Unicode
    /// whitespace, so it stops the port.
    fn skip_white(&mut self) -> Scan<()> {
        while let Some(&b) = self.s.get(self.p) {
            if is_white(b) {
                self.p += 1;
            } else if b.is_ascii() {
                break;
            } else {
                return Err(Stop::Unknown);
            }
        }
        Ok(())
    }

    /// `Scanner.ParseProperty` over `ParsePropertyOrItemMetadata`, from the
    /// `$`.
    fn property(&mut self) -> Scan<()> {
        self.p += 1;
        if self.s.get(self.p).is_some_and(|&b| b != b'(') {
            return Err(Stop::Rejects);
        }
        let (well_formed, end) = self.scan_property_end(self.p, 0)?;
        if !well_formed || end >= self.s.len() {
            return Err(Stop::Rejects);
        }
        self.p = end + 1;
        self.look = Tok::Property;
        Ok(())
    }

    /// `Scanner.ScanForPropertyExpressionEnd` from `index`, the reference's
    /// `(`: whether it is well formed, and where it closes (the text's length,
    /// or past it, when it does not). Parentheses count without regard to
    /// quotes, and a level holding whitespace but no character outside an XML
    /// name is ill formed.
    fn scan_property_end(&self, mut index: usize, nesting: usize) -> Scan<(bool, usize)> {
        if nesting >= super::MAX_CONDITION_NESTING {
            return Err(Stop::Unknown);
        }
        let s = self.s;
        let mut level = 0usize;
        let mut whitespace = None;
        let mut punctuation = false;
        while let Some(&c) = s.get(index) {
            if !c.is_ascii() {
                return Err(Stop::Unknown);
            }
            match c {
                b'(' => level += 1,
                b')' => level -= 1,
                c if is_white(c) => whitespace = Some(index),
                c if !is_name_char(c) => punctuation = true,
                _ => {}
            }
            if c == b'$' && s.get(index + 1) == Some(&b'(') {
                let (well_formed, end) = self.scan_property_end(index + 1, nesting + 1)?;
                if !well_formed {
                    return Ok((false, end));
                }
                index = end;
            }
            if level == 0 {
                return Ok(match whitespace {
                    Some(at) if !punctuation => (false, at),
                    _ => (true, index),
                });
            }
            index += 1;
        }
        Ok((true, index))
    }

    /// `Scanner.ParseQuotedString`, from the opening quote.
    fn quoted_string(&mut self) -> Scan<()> {
        let s = self.s;
        self.p += 1;
        while let Some(&c) = s.get(self.p) {
            if c == b'\'' {
                self.p += 1;
                self.look = Tok::String;
                return Ok(());
            }
            // Metadata and item lists are scanned inside a string too, by
            // rules that depend on the context (an item list's `'` separators
            // do not end the string).
            if matches!(c, b'%' | b'@') && s.get(self.p + 1) == Some(&b'(') {
                return Err(Stop::Unknown);
            }
            self.p += 1;
        }
        Err(Stop::Rejects)
    }

    /// `Scanner.ParseRemaining`: a number, a simple string or function name,
    /// `and`/`or`, or an unexpected character.
    fn remaining(&mut self) -> Scan<()> {
        let s = self.s;
        let c = s[self.p];
        if !c.is_ascii() {
            return Err(Stop::Unknown);
        }
        if matches!(c, b'+' | b'-' | b'.') || c.is_ascii_digit() {
            self.numeric()
        } else if c == b'_' || c.is_ascii_alphabetic() {
            self.simple_string_or_function()
        } else {
            Err(Stop::Rejects)
        }
    }

    /// `Scanner.ParseNumeric`: hex, or a sign then digits and dots in any
    /// arrangement.
    fn numeric(&mut self) -> Scan<()> {
        let s = self.s;
        if s.len() - self.p > 2 && s[self.p] == b'0' && matches!(s[self.p + 1], b'x' | b'X') {
            self.p += 2;
            self.skip(|b| b.is_ascii_hexdigit())?;
        } else {
            if matches!(s[self.p], b'+' | b'-') {
                self.p += 1;
            }
            loop {
                self.skip(|b| b.is_ascii_digit())?;
                if s.get(self.p) == Some(&b'.') {
                    self.p += 1;
                }
                self.skip(|b| b.is_ascii_digit())?;
                if s.get(self.p) != Some(&b'.') {
                    break;
                }
            }
        }
        self.look = Tok::Numeric;
        Ok(())
    }

    /// `Scanner.ParseSimpleStringOrFunction`.
    fn simple_string_or_function(&mut self) -> Scan<()> {
        let start = self.p;
        self.skip(|b| b == b'_' || b.is_ascii_alphanumeric())?;
        let word = &self.s[start..self.p];
        self.look = if word.eq_ignore_ascii_case(b"and") {
            Tok::And
        } else if word.eq_ignore_ascii_case(b"or") {
            Tok::Or
        } else {
            self.skip_white()?;
            if self.s.get(self.p) == Some(&b'(') {
                Tok::Function
            } else {
                Tok::String
            }
        };
        Ok(())
    }

    /// Skip the ASCII characters `class` accepts. A character outside ASCII
    /// may be in the class (MSBuild's digit and letter tests are Unicode), so
    /// it stops the port.
    fn skip(&mut self, class: fn(u8) -> bool) -> Scan<()> {
        while let Some(&b) = self.s.get(self.p) {
            if !b.is_ascii() {
                return Err(Stop::Unknown);
            }
            if !class(b) {
                break;
            }
            self.p += 1;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::{Syntax, msbuild_parse};

    /// Each verdict pinned against `msbuild-condition-oracle` (SDK 10.0.401):
    /// `Rejects` is `{"ok":false}` there whatever the properties hold, and
    /// `Parses` is evaluated (to a value, or to a type error at evaluation).
    #[test]
    fn verdicts_match_msbuild() {
        for (source, expected) in [
            ("tr ue", Syntax::Rejects),
            ("$(A) == ", Syntax::Rejects),
            ("(true", Syntax::Rejects),
            ("true)", Syntax::Rejects),
            ("'abc", Syntax::Rejects),
            ("false And (tr ue)", Syntax::Rejects),
            ("true Or 'abc", Syntax::Rejects),
            ("'a' = 'a'", Syntax::Rejects),
            ("a.b == 'a.b'", Syntax::Rejects),
            ("true == true == true", Syntax::Rejects),
            ("trueand true", Syntax::Rejects),
            ("false and $", Syntax::Rejects),
            ("false and $x", Syntax::Rejects),
            ("false and @", Syntax::Rejects),
            ("false and %", Syntax::Rejects),
            ("$(A B)", Syntax::Rejects),
            ("false and $(A.B('x)", Syntax::Rejects),
            ("'a' == 'b' 'c'", Syntax::Rejects),
            ("()", Syntax::Rejects),
            ("!", Syntax::Rejects),
            ("true And", Syntax::Rejects),
            ("Or true", Syntax::Rejects),
            // Parsed, then legal or illegal only once evaluated.
            ("(true) == true", Syntax::Parses),
            ("!true == false", Syntax::Parses),
            ("1 < abc", Syntax::Parses),
            ("foo", Syntax::Parses),
            ("f(,)", Syntax::Parses),
            ("true and(true)", Syntax::Parses),
            ("'x'and'y'", Syntax::Parses),
            ("'a'=='a'", Syntax::Parses),
            ("false and foo('x')", Syntax::Parses),
            // Context-dependent, or outside ASCII where it is classified.
            ("'@(I)' == ''", Syntax::Unknown),
            ("%(I.M) == ''", Syntax::Unknown),
            ("é == 'é'", Syntax::Unknown),
            // Unknown only once the scan reaches it.
            ("tr ue @(I)", Syntax::Rejects),
            ("'é' == 'é'", Syntax::Parses),
        ] {
            assert_eq!(msbuild_parse(source), expected, "{source:?}");
        }
    }

    #[test]
    fn nesting_past_the_bound_is_unknown() {
        let bound = crate::condition::MAX_CONDITION_NESTING;
        assert_eq!(msbuild_parse(&"(".repeat(bound)), Syntax::Rejects);
        assert_eq!(msbuild_parse(&"(".repeat(bound + 1)), Syntax::Unknown);
        let property = format!("{}{}", "$(".repeat(bound + 1), ")".repeat(bound + 1));
        assert_eq!(msbuild_parse(&property), Syntax::Unknown);
    }

    #[test]
    fn too_many_tokens_is_unknown() {
        let chain = vec!["true"; super::MAX_TOKENS].join(" and ");
        assert_eq!(msbuild_parse(&format!("{chain} )")), Syntax::Unknown);
    }
}
