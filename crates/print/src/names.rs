//! Names, each a type whose every value the printer can spell.
//!
//! The rules here are what makes the printer total: a name that cannot be
//! written down is refused when it is made, not when it is printed.

use crate::vec::Vec1;

/// Words that are a keyword, or that F# reserves, so an identifier spelled with
/// one must be quoted (``` ``type`` ```). The reserved words (`params`,
/// `virtual`, …) lex as identifiers with warning FS0046, so they are quoted too.
///
/// FCS's keyword table also spells some of its internal tokens as words
/// (`__token_OEND`), which lex as those tokens. `borzoi-cst`'s tests hold this
/// list to that table, read from the pinned compiler source, and to our own
/// lexer's keywords, by printing each in every position a name takes.
pub(crate) const QUOTED_WORDS: &[&str] = &[
    "__LINE__",
    "__SOURCE_DIRECTORY__",
    "__SOURCE_FILE__",
    "__token_OBLOCKSEP",
    "__token_ODECLEND",
    "__token_ODO",
    "__token_OELSE",
    "__token_OEND",
    "__token_OLET",
    "__token_OTHEN",
    "__token_OWITH",
    "__token_constraint",
    "abstract",
    "and",
    "as",
    "asr",
    "assert",
    "base",
    "begin",
    "break",
    "checked",
    "class",
    "component",
    "const",
    "constraint",
    "continue",
    "default",
    "delegate",
    "do",
    "done",
    "downcast",
    "downto",
    "elif",
    "else",
    "end",
    "exception",
    "extern",
    "false",
    "finally",
    "fixed",
    "for",
    "fori",
    "fun",
    "function",
    "global",
    "if",
    "in",
    "include",
    "inherit",
    "inline",
    "interface",
    "internal",
    "land",
    "lazy",
    "let",
    "lor",
    "lsl",
    "lsr",
    "lxor",
    "match",
    "member",
    "mixin",
    "mod",
    "module",
    "mutable",
    "namespace",
    "new",
    "null",
    "of",
    "open",
    "or",
    "override",
    "parallel",
    "params",
    "private",
    "process",
    "protected",
    "public",
    "pure",
    "rec",
    "return",
    "sealed",
    "sig",
    "static",
    "struct",
    "tailcall",
    "then",
    "to",
    "trait",
    "true",
    "try",
    "type",
    "upcast",
    "use",
    "val",
    "virtual",
    "void",
    "when",
    "while",
    "with",
    "yield",
];

/// The characters an operator name is built from, `:` aside (only `:=` uses it).
const OPERATOR_CHARS: &str = "!$%&*+-./<=>@^|~";

/// An identifier: a value, type, module, field or case name.
///
/// Any text F# can spell between double backticks, except:
///
/// * empty text, and `_`, which is a wildcard rather than a name;
/// * a backtick, tab or line break, which double backticks cannot hold;
/// * an `@`, which F# reserves for the names it generates (warning FS1104);
/// * text made only of operator characters (`+`, `>>=`), which F# also spells
///   as an operator name, so a reader could not tell ``` ``+`` ``` from
///   `( + )` where both bind a pattern. Name an operator with [`Operator`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Ident(String);

/// Why text is not an [`Ident`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IdentError {
    /// The text is empty.
    Empty,
    /// The text is `_`.
    Wildcard,
    /// The text holds a character double backticks cannot.
    Unspellable(char),
    /// The text holds an `@`, which marks a compiler-generated name.
    CompilerGenerated,
    /// The text is made only of operator characters.
    OperatorLike,
}

impl Ident {
    /// `text` as an identifier.
    pub fn new(text: &str) -> Result<Self, IdentError> {
        if text.is_empty() {
            return Err(IdentError::Empty);
        }
        if text == "_" {
            return Err(IdentError::Wildcard);
        }
        if let Some(c) = text.chars().find(|c| matches!(c, '`' | '\t' | '\n' | '\r')) {
            return Err(IdentError::Unspellable(c));
        }
        if text.contains('@') {
            return Err(IdentError::CompilerGenerated);
        }
        if text.chars().all(|c| OPERATOR_CHARS.contains(c) || c == ':') {
            return Err(IdentError::OperatorLike);
        }
        Ok(Ident(text.to_owned()))
    }

    /// The identifier's text, unquoted.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Whether the identifier can be written without double backticks.
    pub(crate) fn is_plain(&self) -> bool {
        is_plain_word(&self.0) && !QUOTED_WORDS.contains(&self.0.as_str())
    }
}

/// `[A-Za-z_][A-Za-z0-9_']*`, the ASCII shape of an identifier token.
fn is_plain_word(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'')
}

/// The characters F#'s checker refuses in the name of a type, module,
/// namespace, union case or exception (FCS's
/// `IllegalCharactersInTypeAndNamespaceNames`, FS0883). A backtick is one too,
/// but no [`Ident`] holds one.
const ENTITY_NAME_REFUSED: &[char] = &['.', '+', '$', '&', '[', ']', '/', '\\', '*', '"'];

/// The name of a type, nested module, union case or exception: an [`Ident`]
/// without the characters F#'s checker refuses there (FS0883).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EntityName(Ident);

impl EntityName {
    /// `ident` as an entity's name, or `ident` back if it holds a character
    /// F# refuses there.
    pub fn new(ident: Ident) -> Result<Self, Ident> {
        if ident.as_str().contains(ENTITY_NAME_REFUSED) {
            Err(ident)
        } else {
            Ok(EntityName(ident))
        }
    }

    pub fn ident(&self) -> &Ident {
        &self.0
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

/// A dotted path of entity names, `A.B`: what a file's `module` or
/// `namespace` declares.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EntityPath(pub Vec1<EntityName>);

impl EntityPath {
    /// The segments, in order.
    pub fn segments(&self) -> &[EntityName] {
        self.0.as_slice()
    }
}

/// The name of a union case: an [`EntityName`] that F# reads as starting with
/// an upper-case letter, by `borzoi-cst`'s mirror of FCS's rule
/// ([`borzoi_cst::parser::ident_leads_uppercase`]), or one of the names FCS
/// gives `[]` and `::` (FS0053). F# 7 also admits a lower-case case in a type
/// with the `RequireQualifiedAccess` attribute, which takes resolving the
/// attribute's name to see, so the name refuses it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnionCaseName(EntityName);

impl UnionCaseName {
    /// `ident` as a union case's name, or `ident` back if F# refuses it as
    /// one.
    pub fn new(ident: Ident) -> Result<Self, Ident> {
        let name = EntityName::new(ident)?;
        if leads_uppercase(&name) || matches!(name.as_str(), "op_Nil" | "op_ColonColon") {
            Ok(UnionCaseName(name))
        } else {
            Err(name.0)
        }
    }

    pub fn ident(&self) -> &Ident {
        self.0.ident()
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }

    /// The name of the property F# 9 generates to test for the case:
    /// `IsA` for `A`, and `IsEmpty` and `IsCons` for `[]` and `::`.
    pub fn tester(&self) -> String {
        match self.as_str() {
            "op_Nil" => "IsEmpty".to_owned(),
            "op_ColonColon" => "IsCons".to_owned(),
            name => format!("Is{name}"),
        }
    }
}

/// The name of an exception: an [`EntityName`] that F# reads as starting with
/// an upper-case letter (FS0053), with no exception for `[]` and `::`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ExceptionName(EntityName);

impl ExceptionName {
    /// `ident` as an exception's name, or `ident` back if F# refuses it as
    /// one.
    pub fn new(ident: Ident) -> Result<Self, Ident> {
        let name = EntityName::new(ident)?;
        if leads_uppercase(&name) {
            Ok(ExceptionName(name))
        } else {
            Err(name.0)
        }
    }

    pub fn ident(&self) -> &Ident {
        self.0.ident()
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

fn leads_uppercase(name: &EntityName) -> bool {
    borzoi_cst::parser::ident_leads_uppercase(name.as_str())
}

/// A name F# reads as a variable where a pattern may also name a constructor:
/// an [`Ident`] that does not start with an upper-case letter, by
/// `borzoi-cst`'s mirror of FCS's rule
/// ([`borzoi_cst::parser::ident_leads_uppercase`]). FCS reads an upper-case
/// name there as a constructor's, or as a variable only if none resolves.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarName(Ident);

impl VarName {
    /// `ident` as a variable's name, or `ident` back if F# could read it as a
    /// constructor's.
    pub fn new(ident: Ident) -> Result<Self, Ident> {
        if borzoi_cst::parser::ident_leads_uppercase(ident.as_str()) {
            Err(ident)
        } else {
            Ok(VarName(ident))
        }
    }

    pub fn ident(&self) -> &Ident {
        &self.0
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

/// A dotted path of identifiers, `A.B.c`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LongIdent(pub Vec1<Ident>);

impl LongIdent {
    /// The single-segment path `ident`.
    pub fn single(ident: Ident) -> Self {
        LongIdent(Vec1::new(ident, Vec::new()))
    }

    /// The segments, in order.
    pub fn segments(&self) -> &[Ident] {
        self.0.as_slice()
    }
}

/// A type variable's name: `a` in `'a`.
///
/// Type variables have no quoted form, so the name is an ASCII letter followed
/// by ASCII letters, digits and underscores, and is not a keyword. A `'` is
/// refused because `'a'` would lex as a character literal.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyparName(String);

/// Why text is not a [`TyparName`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TyparNameError {
    /// The text is not `[A-Za-z][A-Za-z0-9_]*`.
    NotPlain,
    /// The text is a keyword or reserved word.
    Keyword,
}

impl TyparName {
    /// `text` as a type variable's name.
    pub fn new(text: &str) -> Result<Self, TyparNameError> {
        let mut chars = text.chars();
        let plain = chars.next().is_some_and(|c| c.is_ascii_alphabetic())
            && chars.all(|c| c.is_ascii_alphanumeric() || c == '_');
        if !plain {
            return Err(TyparNameError::NotPlain);
        }
        if QUOTED_WORDS.contains(&text) {
            return Err(TyparNameError::Keyword);
        }
        Ok(TyparName(text.to_owned()))
    }

    /// The name, without its leading `'`.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// A symbolic operator's name: `+`, `>>=`, `~-`.
///
/// An infix operator (see [`Operator::is_infix`]) can sit between two operands.
/// A name starting with `~`, or with `!` but not `!=`, is a prefix operator's; F# names the prefix forms of `-`, `+`, `-.` and `+.` `~-`, `~+`,
/// `~-.` and `~+.`, so `(~-) x` negates and `(-) x` subtracts from `x`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Operator(String);

/// Why text is not an [`Operator`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OperatorError {
    /// The text is empty.
    Empty,
    /// The text holds a character no operator name holds.
    NotOperatorChar(char),
    /// The text is a symbol F# reserves (`|`, `->`, `..`, …) or would lex as
    /// something else (a comment, a quotation bracket).
    Reserved,
    /// The text starts with `~` but is not a prefix operator name F# accepts.
    InvalidPrefix,
}

/// Symbols spelled with operator characters that are punctuation, not operators.
const RESERVED_SYMBOLS: &[&str] = &[".", "..", "|", "&", "->", "<-", "~"];

/// The `~` names F# accepts besides runs of `~`: the prefix forms of the
/// operators that are also infix (FCS's `IsValidPrefixOperatorDefinitionName`,
/// less the `~?+`/`~?-` this type's `?`-free alphabet cannot spell).
const TILDE_OPERATORS: &[&str] = &["~+", "~-", "~+.", "~-.", "~%", "~%%", "~&", "~&&"];

/// Substrings that lex as something other than part of an operator.
const RESERVED_SUBSTRINGS: &[&str] = &["//", "<@", "@>"];

impl Operator {
    /// `text` as an operator name.
    pub fn new(text: &str) -> Result<Self, OperatorError> {
        if text.is_empty() {
            return Err(OperatorError::Empty);
        }
        if text != ":=" {
            if let Some(c) = text.chars().find(|c| !OPERATOR_CHARS.contains(*c)) {
                return Err(OperatorError::NotOperatorChar(c));
            }
            if text.starts_with('.')
                || RESERVED_SYMBOLS.contains(&text)
                || RESERVED_SUBSTRINGS.iter().any(|s| text.contains(s))
            {
                return Err(OperatorError::Reserved);
            }
            // FCS reserves `$` in operator names; `$` alone is the one operator.
            if text.contains('$') && text != "$" {
                return Err(OperatorError::Reserved);
            }
            if text.starts_with('~')
                && !text.chars().all(|c| c == '~')
                && !TILDE_OPERATORS.contains(&text)
            {
                return Err(OperatorError::InvalidPrefix);
            }
        }
        Ok(Operator(text.to_owned()))
    }

    /// The operator's spelling.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// Whether the operator can be applied infix, `a op b`.
    pub fn is_infix(&self) -> bool {
        !(self.0.starts_with('~') || self.0.starts_with('!') && !self.0.starts_with("!="))
    }
}

/// An operator that can be applied infix: an [`Operator`] for which
/// [`Operator::is_infix`] holds.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InfixOperator(Operator);

impl InfixOperator {
    /// `op`, or `None` if it is a prefix operator.
    pub fn new(op: Operator) -> Option<Self> {
        op.is_infix().then_some(InfixOperator(op))
    }

    /// The operator.
    pub fn operator(&self) -> &Operator {
        &self.0
    }
}

/// The name a binding gives a value: an identifier or an operator.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueName {
    /// `let x = …`
    Ident(Ident),
    /// `let ( +++ ) = …`
    Operator(Operator),
}
