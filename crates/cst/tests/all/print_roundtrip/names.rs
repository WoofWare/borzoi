//! Exhaustive checks of the names the printer spells, beside the generator's
//! random ones: every keyword in every position a name can take, and every
//! short operator spelling in every position an operator can take.

use borzoi_print::names::{Ident, InfixOperator, LongIdent, Operator, TyparName, ValueName};
use borzoi_print::tree::{
    Attribute, Binding, BindingHead, Const, Expr, ForDirection, ImplFile, LetBindings, ModuleDecl,
    NamedModule, NestedModule, Pat, RecordField, Type, TypeDefn, TypeRepr, UnionCase, UnionField,
};
use borzoi_print::vec::Vec1;

use super::round_trips;
use crate::common::par_map;

/// FCS's keyword table (`LexHelpers.fs`, `keywordList`), the reserved words
/// included, less its internal `__token_*` entries.
const FCS_KEYWORDS: &[&str] = &[
    "abstract",
    "and",
    "as",
    "assert",
    "base",
    "begin",
    "class",
    "const",
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
    "fun",
    "function",
    "global",
    "if",
    "in",
    "inherit",
    "inline",
    "interface",
    "internal",
    "lazy",
    "let",
    "match",
    "member",
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
    "private",
    "public",
    "rec",
    "return",
    "sig",
    "static",
    "struct",
    "then",
    "to",
    "true",
    "try",
    "type",
    "upcast",
    "use",
    "val",
    "void",
    "when",
    "while",
    "with",
    "yield",
    "_",
    "break",
    "checked",
    "component",
    "constraint",
    "continue",
    "fori",
    "include",
    "mixin",
    "parallel",
    "params",
    "process",
    "protected",
    "pure",
    "sealed",
    "trait",
    "tailcall",
    "virtual",
    "__SOURCE_DIRECTORY__",
    "__SOURCE_FILE__",
    "__LINE__",
];

/// Words F# once reserved and later released, which lex as identifiers.
const RELEASED_WORDS: &[&str] = &[
    "atomic",
    "constructor",
    "eager",
    "functor",
    "measure",
    "method",
    "object",
    "recursive",
    "volatile",
    "land",
    "lor",
    "lxor",
    "lsl",
    "lsr",
    "asr",
];

/// Every word our lexer has a token for, read off its `#[token("…")]`
/// attributes, so a keyword the lexer gains is checked without a list here
/// changing.
fn lexer_words() -> Vec<String> {
    let src = include_str!("../../../src/lexer/mod.rs");
    src.split("#[token(\"")
        .skip(1)
        .filter_map(|rest| rest.split('"').next())
        .filter(|w| {
            w.chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
        })
        .map(str::to_owned)
        .collect()
}

fn single(id: &Ident) -> LongIdent {
    LongIdent::single(id.clone())
}

fn name(id: &Ident) -> Expr {
    Expr::Name(single(id))
}

fn let_decl(head: BindingHead, body: Expr) -> ModuleDecl {
    ModuleDecl::Let(LetBindings::NonRec(Box::new(Binding {
        attributes: Vec::new(),
        is_inline: false,
        head,
        body,
    })))
}

/// A file using `id` in every position a name takes.
fn name_positions(id: &Ident) -> ImplFile {
    let path = LongIdent(Vec1::new(id.clone(), vec![id.clone()]));
    let ty = Type::App {
        head: single(id),
        args: Vec1::new(Type::Name(path.clone()), Vec::new()),
    };
    let decls = vec![
        ModuleDecl::Open(path.clone()),
        ModuleDecl::ModuleAbbrev {
            name: id.clone(),
            target: path.clone(),
        },
        let_decl(
            BindingHead::Name {
                is_mutable: false,
                access: None,
                name: ValueName::Ident(id.clone()),
            },
            Expr::Name(path.clone()),
        ),
        ModuleDecl::Let(LetBindings::NonRec(Box::new(Binding {
            attributes: vec![Attribute {
                name: path.clone(),
                arg: name(id),
            }],
            is_inline: false,
            head: BindingHead::Function {
                access: None,
                name: ValueName::Ident(id.clone()),
                params: Vec1::new(
                    Pat::Name(single(id)),
                    vec![
                        Pat::Ctor {
                            name: path.clone(),
                            args: Vec1::new(Pat::Name(single(id)), Vec::new()),
                        },
                        Pat::Record(Vec1::new((path.clone(), Pat::Wildcard), Vec::new())),
                    ],
                ),
            },
            body: Expr::Sequential(
                Box::new(Expr::FieldGet {
                    expr: Box::new(name(id)),
                    field: id.clone(),
                }),
                Box::new(Expr::Sequential(
                    Box::new(Expr::Set {
                        target: path.clone(),
                        value: Box::new(Expr::Record {
                            copy: None,
                            fields: Vec1::new((path.clone(), name(id)), Vec::new()),
                        }),
                    }),
                    Box::new(Expr::For {
                        var: id.clone(),
                        from: Box::new(name(id)),
                        direction: ForDirection::To,
                        to: Box::new(Expr::Typed {
                            expr: Box::new(name(id)),
                            ty: ty.clone(),
                        }),
                        body: Box::new(Expr::Const(Const::Unit)),
                    }),
                )),
            ),
        }))),
        ModuleDecl::Types(Vec1::new(
            TypeDefn {
                attributes: Vec::new(),
                access: None,
                name: id.clone(),
                typars: Vec::new(),
                repr: TypeRepr::Record(Vec1::new(
                    RecordField {
                        is_mutable: false,
                        name: id.clone(),
                        ty: ty.clone(),
                    },
                    Vec::new(),
                )),
            },
            vec![TypeDefn {
                attributes: Vec::new(),
                access: None,
                name: id.clone(),
                typars: Vec::new(),
                repr: TypeRepr::Union(Vec1::new(
                    UnionCase {
                        name: id.clone(),
                        fields: vec![UnionField {
                            name: Some(id.clone()),
                            ty,
                        }],
                    },
                    Vec::new(),
                )),
            }],
        )),
        ModuleDecl::Exception(UnionCase {
            name: id.clone(),
            fields: Vec::new(),
        }),
    ];
    ImplFile::NamedModule(NamedModule {
        attributes: Vec::new(),
        access: None,
        is_rec: false,
        name: path,
        decls: vec![ModuleDecl::NestedModule(NestedModule {
            attributes: Vec::new(),
            access: None,
            is_rec: false,
            name: id.clone(),
            decls,
        })],
    })
}

/// A file using `t` as a type parameter and a type variable.
fn typar_positions(t: &TyparName) -> ImplFile {
    let id = Ident::new("T").expect("an identifier");
    ImplFile::AnonModule(vec![ModuleDecl::Types(Vec1::new(
        TypeDefn {
            attributes: Vec::new(),
            access: None,
            name: id,
            typars: vec![t.clone()],
            repr: TypeRepr::Abbrev(Type::Fun {
                arg: Box::new(Type::Var(t.clone())),
                ret: Box::new(Type::Var(t.clone())),
            }),
        },
        Vec::new(),
    ))])
}

fn report(failures: Vec<String>) {
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}

#[test]
fn every_keyword_round_trips_in_every_name_position() {
    let mut words: Vec<String> = FCS_KEYWORDS
        .iter()
        .chain(RELEASED_WORDS)
        .map(|w| (*w).to_owned())
        .chain(lexer_words())
        .collect();
    words.sort();
    words.dedup();
    assert!(
        words.iter().any(|w| w == "__SOURCE_FILE__") && words.len() > 90,
        "the word list has lost its keywords: {words:?}"
    );
    let failures = par_map(words.len(), |i| {
        let w = &words[i];
        let mut why = Vec::new();
        if let Ok(id) = Ident::new(w)
            && let Err(e) = round_trips(&name_positions(&id))
        {
            why.push(format!("{w:?} as a name: {e}"));
        }
        if let Ok(t) = TyparName::new(w)
            && let Err(e) = round_trips(&typar_positions(&t))
        {
            why.push(format!("{w:?} as a type variable: {e}"));
        }
        why
    });
    report(failures.into_iter().flatten().collect());
}

/// Every spelling over the operator characters (and `:`, `?`) up to
/// `max_len`, the ones [`Operator::new`] accepts checked as a definition, a
/// value, and, if infix, between two operands.
fn every_operator_round_trips(max_len: usize) {
    const ALPHABET: &[char] = &[
        '!', '$', '%', '&', '*', '+', '-', '.', '/', '<', '=', '>', '@', '^', '|', '~', ':', '?',
    ];
    let mut spellings = vec![String::new()];
    let mut all = Vec::new();
    for _ in 0..max_len {
        spellings = spellings
            .iter()
            .flat_map(|s| ALPHABET.iter().map(move |c| format!("{s}{c}")))
            .collect();
        all.extend(spellings.iter().cloned());
    }
    let ops: Vec<Operator> = all.iter().filter_map(|s| Operator::new(s).ok()).collect();
    assert!(ops.len() > 100, "too few operators accepted: {}", ops.len());
    let a = || Expr::Name(LongIdent::single(Ident::new("a").expect("an identifier")));
    let failures = par_map(ops.len(), |i| {
        let op = &ops[i];
        let mut decls = vec![
            ModuleDecl::Let(LetBindings::NonRec(Box::new(Binding {
                attributes: Vec::new(),
                is_inline: false,
                head: BindingHead::Function {
                    access: None,
                    name: ValueName::Operator(op.clone()),
                    params: Vec1::new(Pat::Wildcard, vec![Pat::Wildcard]),
                },
                body: a(),
            }))),
            let_decl(
                BindingHead::Pattern(Pat::Wildcard),
                Expr::OpValue(op.clone()),
            ),
        ];
        if let Some(infix) = InfixOperator::new(op.clone()) {
            decls.push(ModuleDecl::Expr(Expr::Infix {
                op: infix,
                lhs: Box::new(a()),
                rhs: Box::new(a()),
            }));
        }
        round_trips(&ImplFile::AnonModule(decls))
            .err()
            .map(|e| format!("{:?}: {e}", op.as_str()))
    });
    report(failures.into_iter().flatten().collect());
}

#[test]
fn every_operator_of_up_to_two_characters_round_trips() {
    every_operator_round_trips(2);
}

#[test]
#[ignore = "deep twin of every_operator_of_up_to_two_characters_round_trips (~4,000 FCS parses)"]
fn deep_every_operator_of_up_to_three_characters_round_trips() {
    every_operator_round_trips(3);
}
