//! Exhaustive checks of the names the printer spells, beside the generator's
//! random ones: every keyword in every position a name can take, and every
//! short operator spelling in every position an operator can take.

use borzoi_print::names::{
    EntityName, EntityPath, ExceptionName, Ident, InfixOperator, LongIdent, Operator, TyparName,
    UnionCaseName, ValueName,
};
use borzoi_print::tree::{
    Const, ExceptionDefn, ForDirection, ModuleBody, RecordField, Type, TypeRepr, UnionCase,
    UnionField,
};
use borzoi_print::vec::Vec1;
use borzoi_print::version::DefaultVersion;

type Expr = borzoi_print::tree::Expr<DefaultVersion>;
type ImplFile = borzoi_print::tree::ImplFile<DefaultVersion>;
type ModuleDecl = borzoi_print::tree::ModuleDecl<DefaultVersion>;
type Binding = borzoi_print::tree::Binding<DefaultVersion>;
type LetBindings = borzoi_print::tree::LetBindings<DefaultVersion>;
type NestedModule = borzoi_print::tree::NestedModule<DefaultVersion>;
type NamedModule = borzoi_print::tree::NamedModule<DefaultVersion>;
type Args = borzoi_print::tree::Args<DefaultVersion>;
type Attribute = borzoi_print::tree::Attribute<DefaultVersion>;
type AttributeArgs = borzoi_print::tree::AttributeArgs<DefaultVersion>;
type TypeDefn = borzoi_print::tree::TypeDefn<DefaultVersion>;
type Pat = borzoi_print::tree::Pat<DefaultVersion>;
type BindingHead = borzoi_print::tree::BindingHead<DefaultVersion>;
type ModuleBindings = borzoi_print::tree::ModuleBindings<DefaultVersion>;

/// `group` as a module's `let`.
fn module_let(group: LetBindings) -> ModuleDecl {
    ModuleDecl::Let(ModuleBindings::new(group).expect("a module's group"))
}

use super::round_trips;
use crate::common::{corpus_root, par_map};

/// Every word FCS's lexer treats as other than a plain identifier, read from
/// the pinned compiler source's `LexHelpers.fs`: each string literal from its
/// keyword table (`keywordList`, the reserved words and the internal
/// `__token_*` spellings included) through `KeywordOrIdentifierToken` (the
/// `__SOURCE_FILE__` family). Reading it rather than copying it keeps the
/// list from drifting when the corpus moves.
fn fcs_keywords() -> Vec<String> {
    let path = corpus_root().join("src/Compiler/SyntaxTree/LexHelpers.fs");
    let src =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let start = src
        .find("let private keywordList")
        .expect("LexHelpers.fs defines keywordList");
    let function = src[start..]
        .find("let KeywordOrIdentifierToken")
        .expect("LexHelpers.fs defines KeywordOrIdentifierToken")
        + start;
    let end = src[function + 1..]
        .find("\n    let ")
        .map_or(src.len(), |i| i + function + 1);
    src[start..end]
        .split('"')
        .skip(1)
        .step_by(2)
        .map(str::to_owned)
        .collect()
}

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
    module_let(LetBindings::NonRec(Box::new(Binding {
        attributes: Vec::new(),
        is_inline: false,
        head,
        body,
    })))
}

/// A file using `id` in every position a name takes. A union case's or an
/// exception's name takes `id` only where F# admits it there; `C` stands in
/// elsewhere, with `id` its field's name.
fn name_positions(id: &Ident) -> ImplFile {
    let entity = EntityName::new(id.clone()).expect("an entity's name");
    let c = || Ident::new("C").expect("an identifier");
    let case =
        UnionCaseName::new(id.clone()).unwrap_or_else(|_| UnionCaseName::new(c()).expect("a case"));
    let exn = ExceptionName::new(id.clone())
        .unwrap_or_else(|_| ExceptionName::new(c()).expect("an exception"));
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
        module_let(LetBindings::NonRec(Box::new(Binding {
            attributes: vec![Attribute {
                name: path.clone(),
                args: AttributeArgs::List(Args::Named {
                    positional: vec![name(id)],
                    named: Vec1::new((id.clone(), name(id)), Vec::new()),
                }),
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
                Box::new(Expr::MethodApp {
                    func: Box::new(Expr::FieldGet {
                        expr: Box::new(name(id)),
                        field: id.clone(),
                    }),
                    args: Args::Named {
                        positional: Vec::new(),
                        named: Vec1::new((id.clone(), name(id)), Vec::new()),
                    },
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
            TypeDefn::new(
                Vec::new(),
                None,
                entity.clone(),
                Vec::new(),
                TypeRepr::Record(Vec1::new(
                    RecordField {
                        is_mutable: false,
                        name: id.clone(),
                        ty: ty.clone(),
                    },
                    Vec::new(),
                )),
            )
            .expect("a definition"),
            vec![
                TypeDefn::new(
                    Vec::new(),
                    None,
                    entity.clone(),
                    Vec::new(),
                    TypeRepr::Union(Vec1::new(
                        UnionCase::new(
                            case.clone(),
                            vec![UnionField {
                                name: Some(id.clone()),
                                ty: ty.clone(),
                            }],
                        )
                        .expect("a case"),
                        Vec::new(),
                    )),
                )
                .expect("a definition"),
            ],
        )),
        ModuleDecl::Exception(
            ExceptionDefn::new(
                exn,
                vec![UnionField {
                    name: Some(id.clone()),
                    ty,
                }],
            )
            .expect("an exception"),
        ),
    ];
    ImplFile::NamedModule(NamedModule {
        attributes: Vec::new(),
        access: None,
        name: EntityPath(Vec1::new(entity.clone(), vec![entity.clone()])),
        body: ModuleBody::NonRec(vec![ModuleDecl::NestedModule(NestedModule {
            attributes: Vec::new(),
            access: None,
            name: entity,
            body: ModuleBody::NonRec(decls),
        })]),
    })
}

/// A file using `t` as a type parameter and a type variable.
fn typar_positions(t: &TyparName) -> ImplFile {
    let id = Ident::new("T").expect("an identifier");
    ImplFile::AnonModule(vec![ModuleDecl::Types(Vec1::new(
        TypeDefn::new(
            Vec::new(),
            None,
            EntityName::new(id).expect("an entity's name"),
            vec![t.clone()],
            TypeRepr::Abbrev(Type::Fun {
                arg: Box::new(Type::Var(t.clone())),
                ret: Box::new(Type::Var(t.clone())),
            }),
        )
        .expect("a definition"),
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
    let fcs = fcs_keywords();
    for expected in ["type", "params", "__token_OEND", "__SOURCE_FILE__"] {
        assert!(
            fcs.iter().any(|w| w == expected),
            "the keyword list read from LexHelpers.fs has lost {expected:?}: {fcs:?}"
        );
    }
    let mut words: Vec<String> = fcs
        .into_iter()
        .chain(RELEASED_WORDS.iter().map(|w| (*w).to_owned()))
        .chain(lexer_words())
        .collect();
    words.sort();
    words.dedup();
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
            module_let(LetBindings::NonRec(Box::new(Binding {
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
