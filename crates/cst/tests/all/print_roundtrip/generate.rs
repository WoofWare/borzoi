//! Generating arbitrary `borzoi_print` trees.
//!
//! Every value the tree's types allow is fair game: if some value prints as text
//! FCS rejects or reads as something else, either the printer is wrong or the
//! types let through a value F# cannot express, and both are bugs. So the leaves
//! lean on the edges: keywords and reserved words as names, names that need
//! quoting, every operator character, literal extremes, NaNs, lone surrogates.

use borzoi_print::names::{Ident, InfixOperator, LongIdent, Operator, TyparName, ValueName};
use borzoi_print::tree::{
    Access, ArrayRank, Attribute, Binding, BindingHead, Const, Expr, Float32, Float64,
    ForDirection, ImplFile, LetBindings, MatchClause, ModuleDecl, NamedModule, Namespace,
    NamespaceName, NestedModule, Pat, RecordField, Type, TypeDefn, TypeRepr, UnionCase, UnionField,
};
use borzoi_print::vec::{Vec1, Vec2};
use proptest::prelude::*;
use proptest::strategy::BoxedStrategy;

/// Names worth trying: plain, keyword, reserved, unreserved-but-once-reserved,
/// non-ASCII, and text only double backticks can hold.
const WORDS: &[&str] = &[
    "x",
    "y",
    "f",
    "foo",
    "Some",
    "None",
    "A",
    "B",
    "T",
    "x'",
    "_x",
    "__",
    "a1",
    "É",
    "über",
    "λ",
    "a b",
    "1a",
    " a",
    "a ",
    "a.b",
    "a:b",
    "a,b",
    "a;b",
    "x\u{0}",
    "\u{feff}a",
    "a\u{2028}b",
    "op_Addition",
    "a''",
    "type",
    "let",
    "params",
    "process",
    "virtual",
    "object",
    "method",
    "atomic",
    "constructor",
    "measure",
    "__LINE__",
    "__SOURCE_FILE__",
    "global",
    "base",
    "elif",
    "sig",
    "fixed",
    "const",
    "default",
    "land",
    "mod",
    "asr",
    "or",
    "fori",
    "yield",
    "_",
    "Item",
    "get_X",
    "``",
    "a`b",
    "a\tb",
    "+",
    "+a",
    "a+",
];

const OPERATORS: &[&str] = &[
    "+", "-", "*", "/", "%", "**", "=", "<>", "<", ">", "<=", ">=", "|>", "<|", ">>", "<<", "&&",
    "||", "&", "@", "^", ":=", "!=", "==", ">>=", "<*>", "|||", "&&&", "^^^", "<<<", ">>>", "~~~",
    "~-", "~+", "~-.", "!", "!!", "$", "+.", "-.", "*.", "/.", "..", "?", "?<-", "|", "->", "<-",
    "::", ":>", "<@", "@>", "//", "/*", "*)", ".+",
];

fn ident() -> BoxedStrategy<Ident> {
    prop_oneof![
        4 => prop::sample::select(WORDS).prop_map(str::to_owned),
        3 => "[a-zA-Z_][a-zA-Z0-9_']{0,5}",
        1 => ".{1,4}",
    ]
    .prop_filter_map("not an identifier", |s| Ident::new(&s).ok())
    .boxed()
}

fn long_ident() -> BoxedStrategy<LongIdent> {
    prop::collection::vec(ident(), 1..=3)
        .prop_map(|ids| LongIdent(Vec1::from_vec(ids).expect("non-empty")))
        .boxed()
}

fn operator() -> BoxedStrategy<Operator> {
    prop_oneof![
        3 => prop::sample::select(OPERATORS).prop_map(str::to_owned),
        2 => "[!$%&*+\\-./<=>@^|~:?]{1,4}",
    ]
    .prop_filter_map("not an operator", |s| Operator::new(&s).ok())
    .boxed()
}

fn infix_operator() -> BoxedStrategy<InfixOperator> {
    operator()
        .prop_filter_map("not infix", InfixOperator::new)
        .boxed()
}

fn value_name() -> BoxedStrategy<ValueName> {
    prop_oneof![
        4 => ident().prop_map(ValueName::Ident),
        1 => operator().prop_map(ValueName::Operator),
    ]
    .boxed()
}

fn typar() -> BoxedStrategy<TyparName> {
    prop_oneof![
        3 => "[a-zA-Z][a-zA-Z0-9_]{0,3}",
        1 => prop::sample::select(WORDS).prop_map(str::to_owned),
    ]
    .prop_filter_map("not a type variable", |s| TyparName::new(&s).ok())
    .boxed()
}

fn access() -> BoxedStrategy<Option<Access>> {
    prop_oneof![
        3 => Just(None),
        1 => Just(Some(Access::Public)),
        1 => Just(Some(Access::Internal)),
        1 => Just(Some(Access::Private)),
    ]
    .boxed()
}

fn f32_bits() -> BoxedStrategy<u32> {
    prop_oneof![
        2 => any::<u32>(),
        1 => prop::sample::select(vec![
            0.0f32, -0.0, 1.0, -1.0, 0.1, 1e-7, 1e7, 16777217.0, f32::MIN_POSITIVE, f32::MAX,
            f32::MIN, f32::EPSILON, 1e-45, f32::INFINITY, f32::NEG_INFINITY, f32::NAN,
        ])
        .prop_map(f32::to_bits),
    ]
    .boxed()
}

fn f64_bits() -> BoxedStrategy<u64> {
    prop_oneof![
        2 => any::<u64>(),
        1 => prop::sample::select(vec![
            0.0f64, -0.0, 1.0, -1.0, 0.1, 1e-7, 1e16, 1e300, 5e-324, f64::MIN_POSITIVE, f64::MAX,
            f64::MIN, 9007199254740993.0, f64::INFINITY, f64::NEG_INFINITY, f64::NAN,
        ])
        .prop_map(f64::to_bits),
    ]
    .boxed()
}

fn constant() -> BoxedStrategy<Const> {
    prop_oneof![
        Just(Const::Unit),
        any::<bool>().prop_map(Const::Bool),
        prop_oneof![Just(i8::MIN), Just(i8::MAX), any::<i8>()].prop_map(Const::SByte),
        any::<u8>().prop_map(Const::Byte),
        prop_oneof![Just(i16::MIN), any::<i16>()].prop_map(Const::Int16),
        any::<u16>().prop_map(Const::UInt16),
        prop_oneof![
            Just(i32::MIN),
            Just(i32::MAX),
            Just(-1),
            Just(0),
            any::<i32>()
        ]
        .prop_map(Const::Int32),
        prop_oneof![Just(u32::MAX), any::<u32>()].prop_map(Const::UInt32),
        prop_oneof![Just(i64::MIN), any::<i64>()].prop_map(Const::Int64),
        prop_oneof![Just(u64::MAX), any::<u64>()].prop_map(Const::UInt64),
        prop_oneof![Just(i64::MIN), any::<i64>()].prop_map(Const::NativeInt),
        any::<u64>().prop_map(Const::UNativeInt),
        f32_bits().prop_map(|b| Const::Single(Float32(b))),
        f64_bits().prop_map(|b| Const::Double(Float64(b))),
        prop_oneof![
            Just(0xD800u16),
            Just(0xFFFF),
            Just(u16::from(b'\'')),
            any::<u16>()
        ]
        .prop_map(Const::Char),
        prop_oneof!["[ -~]{0,6}", ".{0,4}", any::<String>()].prop_map(Const::String),
    ]
    .boxed()
}

fn ty() -> BoxedStrategy<Type> {
    let leaf = prop_oneof![
        3 => long_ident().prop_map(Type::Name),
        1 => typar().prop_map(Type::Var),
        1 => Just(Type::Anon),
    ];
    leaf.prop_recursive(3, 12, 3, |inner| {
        prop_oneof![
            (long_ident(), prop::collection::vec(inner.clone(), 1..=3)).prop_map(|(head, args)| {
                Type::App {
                    head,
                    args: Vec1::from_vec(args).expect("non-empty"),
                }
            }),
            (inner.clone(), inner.clone()).prop_map(|(a, r)| Type::Fun {
                arg: Box::new(a),
                ret: Box::new(r),
            }),
            prop::collection::vec(inner.clone(), 2..=3)
                .prop_map(|ts| Type::Tuple(Vec2::from_vec(ts).expect("two"))),
            (prop_oneof![Just(1u8), Just(2), Just(32)], inner).prop_map(|(rank, elem)| {
                Type::Array {
                    rank: ArrayRank::new(rank).expect("in range"),
                    elem: Box::new(elem),
                }
            }),
        ]
    })
    .boxed()
}

fn pat() -> BoxedStrategy<Pat> {
    let leaf = prop_oneof![
        1 => Just(Pat::Wildcard),
        4 => long_ident().prop_map(Pat::Name),
        2 => constant().prop_map(Pat::Const),
        1 => Just(Pat::Null),
        1 => ty().prop_map(Pat::IsInst),
    ];
    leaf.prop_recursive(3, 16, 3, |inner| {
        let b = inner.clone().prop_map(Box::new);
        prop_oneof![
            (long_ident(), prop::collection::vec(inner.clone(), 1..=2)).prop_map(|(name, args)| {
                Pat::Ctor {
                    name,
                    args: Vec1::from_vec(args).expect("non-empty"),
                }
            }),
            prop::collection::vec(inner.clone(), 2..=3)
                .prop_map(|ps| Pat::Tuple(Vec2::from_vec(ps).expect("two"))),
            prop::collection::vec(inner.clone(), 0..=2).prop_map(Pat::List),
            prop::collection::vec(inner.clone(), 0..=2).prop_map(Pat::Array),
            (b.clone(), b.clone()).prop_map(|(head, tail)| Pat::Cons { head, tail }),
            (b.clone(), ty()).prop_map(|(pat, ty)| Pat::Typed { pat, ty }),
            (b.clone(), b.clone()).prop_map(|(pat, alias)| Pat::As { pat, alias }),
            (b.clone(), b).prop_map(|(l, r)| Pat::Or(l, r)),
            prop::collection::vec(inner.clone(), 2..=3)
                .prop_map(|ps| Pat::Ands(Vec2::from_vec(ps).expect("two"))),
            prop::collection::vec((long_ident(), inner), 1..=2)
                .prop_map(|fs| Pat::Record(Vec1::from_vec(fs).expect("non-empty"))),
        ]
    })
    .boxed()
}

fn attributes(arg: BoxedStrategy<Expr>) -> BoxedStrategy<Vec<Attribute>> {
    prop_oneof![
        3 => Just(Vec::new()),
        1 => prop::collection::vec(
            (
                long_ident(),
                prop_oneof![2 => Just(Expr::Const(Const::Unit)), 1 => arg],
            )
                .prop_map(|(name, arg)| Attribute { name, arg }),
            1..=2,
        ),
    ]
    .boxed()
}

fn binding(expr: BoxedStrategy<Expr>) -> BoxedStrategy<Binding> {
    let head = prop_oneof![
        (any::<bool>(), access(), value_name()).prop_map(|(is_mutable, access, name)| {
            BindingHead::Name {
                is_mutable,
                access,
                name,
            }
        }),
        (access(), value_name(), prop::collection::vec(pat(), 1..=3)).prop_map(
            |(access, name, params)| BindingHead::Function {
                access,
                name,
                params: Vec1::from_vec(params).expect("non-empty"),
            }
        ),
        pat().prop_map(BindingHead::Pattern),
    ];
    (attributes(expr.clone()), any::<bool>(), head, expr)
        .prop_map(|(attributes, is_inline, head, body)| Binding {
            attributes,
            is_inline,
            head,
            body,
        })
        .boxed()
}

fn let_bindings(expr: BoxedStrategy<Expr>) -> BoxedStrategy<LetBindings> {
    prop_oneof![
        binding(expr.clone()).prop_map(|b| LetBindings::NonRec(Box::new(b))),
        prop::collection::vec(binding(expr), 1..=2)
            .prop_map(|bs| LetBindings::Rec(Vec1::from_vec(bs).expect("non-empty"))),
    ]
    .boxed()
}

fn clauses(expr: BoxedStrategy<Expr>) -> BoxedStrategy<Vec1<MatchClause>> {
    prop::collection::vec(
        (pat(), prop::option::weighted(0.25, expr.clone()), expr)
            .prop_map(|(pat, guard, result)| MatchClause { pat, guard, result }),
        1..=2,
    )
    .prop_map(|cs| Vec1::from_vec(cs).expect("non-empty"))
    .boxed()
}

pub fn expr() -> BoxedStrategy<Expr> {
    let leaf = prop_oneof![
        3 => constant().prop_map(Expr::Const),
        1 => Just(Expr::Null),
        4 => long_ident().prop_map(Expr::Name),
        1 => operator().prop_map(Expr::OpValue),
    ];
    leaf.prop_recursive(4, 24, 3, |inner| {
        let b = inner.clone().prop_map(Box::new);
        let items = prop::collection::vec(inner.clone(), 0..=2);
        prop_oneof![
            (b.clone(), b.clone()).prop_map(|(func, arg)| Expr::App { func, arg }),
            (infix_operator(), b.clone(), b.clone()).prop_map(|(op, lhs, rhs)| Expr::Infix {
                op,
                lhs,
                rhs
            }),
            prop::collection::vec(inner.clone(), 2..=3)
                .prop_map(|es| Expr::Tuple(Vec2::from_vec(es).expect("two"))),
            items.clone().prop_map(Expr::List),
            items.prop_map(Expr::Array),
            (
                prop::option::weighted(0.3, b.clone()),
                prop::collection::vec((long_ident(), inner.clone()), 1..=2),
            )
                .prop_map(|(copy, fields)| Expr::Record {
                    copy,
                    fields: Vec1::from_vec(fields).expect("non-empty"),
                }),
            (b.clone(), ident()).prop_map(|(expr, field)| Expr::FieldGet { expr, field }),
            (long_ident(), b.clone()).prop_map(|(target, value)| Expr::Set { target, value }),
            (prop::collection::vec(pat(), 1..=2), b.clone()).prop_map(|(params, body)| {
                Expr::Lambda {
                    params: Vec1::from_vec(params).expect("non-empty"),
                    body,
                }
            }),
            clauses(inner.clone()).prop_map(Expr::Function),
            (b.clone(), clauses(inner.clone()))
                .prop_map(|(scrutinee, clauses)| Expr::Match { scrutinee, clauses }),
            (b.clone(), b.clone(), prop::option::of(b.clone())).prop_map(
                |(cond, then_branch, else_branch)| Expr::IfThenElse {
                    cond,
                    then_branch,
                    else_branch,
                }
            ),
            (let_bindings(inner.clone()), b.clone())
                .prop_map(|(bindings, body)| Expr::LetIn { bindings, body }),
            (b.clone(), b.clone()).prop_map(|(x, y)| Expr::Sequential(x, y)),
            (b.clone(), ty()).prop_map(|(expr, ty)| Expr::Typed { expr, ty }),
            (b.clone(), ty()).prop_map(|(expr, ty)| Expr::TypeTest { expr, ty }),
            (b.clone(), ty()).prop_map(|(expr, ty)| Expr::Upcast { expr, ty }),
            (b.clone(), ty()).prop_map(|(expr, ty)| Expr::Downcast { expr, ty }),
            (b.clone(), b.clone()).prop_map(|(head, tail)| Expr::Cons { head, tail }),
            (b.clone(), clauses(inner)).prop_map(|(body, clauses)| Expr::TryWith { body, clauses }),
            (b.clone(), b.clone()).prop_map(|(body, finally)| Expr::TryFinally { body, finally }),
            (b.clone(), b.clone()).prop_map(|(cond, body)| Expr::While { cond, body }),
            (
                ident(),
                b.clone(),
                prop_oneof![Just(ForDirection::To), Just(ForDirection::Downto)],
                b.clone(),
                b.clone(),
            )
                .prop_map(|(var, from, direction, to, body)| Expr::For {
                    var,
                    from,
                    direction,
                    to,
                    body,
                }),
            (pat(), b.clone(), b.clone()).prop_map(|(pat, source, body)| Expr::ForEach {
                pat,
                source,
                body
            }),
            b.clone().prop_map(Expr::Lazy),
            b.clone().prop_map(Expr::Assert),
            b.prop_map(Expr::Do),
        ]
    })
    .boxed()
}

fn union_case() -> BoxedStrategy<UnionCase> {
    (
        ident(),
        prop::collection::vec(
            (prop::option::of(ident()), ty()).prop_map(|(name, ty)| UnionField { name, ty }),
            0..=2,
        ),
    )
        .prop_map(|(name, fields)| UnionCase { name, fields })
        .boxed()
}

fn type_defn() -> BoxedStrategy<TypeDefn> {
    let repr = prop_oneof![
        ty().prop_map(TypeRepr::Abbrev),
        prop::collection::vec(
            (any::<bool>(), ident(), ty()).prop_map(|(is_mutable, name, ty)| RecordField {
                is_mutable,
                name,
                ty,
            }),
            1..=3,
        )
        .prop_map(|fs| TypeRepr::Record(Vec1::from_vec(fs).expect("non-empty"))),
        prop::collection::vec(union_case(), 1..=3)
            .prop_map(|cs| TypeRepr::Union(Vec1::from_vec(cs).expect("non-empty"))),
    ];
    (
        attributes(expr()),
        access(),
        ident(),
        prop::collection::vec(typar(), 0..=2),
        repr,
    )
        .prop_map(|(attributes, access, name, typars, repr)| TypeDefn {
            attributes,
            access,
            name,
            typars,
            repr,
        })
        .boxed()
}

fn decls() -> BoxedStrategy<Vec<ModuleDecl>> {
    let leaf = prop_oneof![
        4 => let_bindings(expr()).prop_map(ModuleDecl::Let),
        2 => expr().prop_map(ModuleDecl::Expr),
        1 => long_ident().prop_map(ModuleDecl::Open),
        1 => (ident(), long_ident())
            .prop_map(|(name, target)| ModuleDecl::ModuleAbbrev { name, target }),
        2 => prop::collection::vec(type_defn(), 1..=2)
            .prop_map(|ds| ModuleDecl::Types(Vec1::from_vec(ds).expect("non-empty"))),
        1 => union_case().prop_map(ModuleDecl::Exception),
    ];
    let decl = leaf.prop_recursive(2, 8, 3, |inner| {
        (
            attributes(expr()),
            access(),
            any::<bool>(),
            ident(),
            prop::collection::vec(inner, 0..=3),
        )
            .prop_map(|(attributes, access, is_rec, name, decls)| {
                ModuleDecl::NestedModule(NestedModule {
                    attributes,
                    access,
                    is_rec,
                    name,
                    decls,
                })
            })
    });
    prop::collection::vec(decl, 0..=3).boxed()
}

pub fn impl_file() -> BoxedStrategy<ImplFile> {
    prop_oneof![
        decls().prop_map(ImplFile::AnonModule),
        (
            attributes(expr()),
            access(),
            any::<bool>(),
            long_ident(),
            decls()
        )
            .prop_map(|(attributes, access, is_rec, name, decls)| {
                ImplFile::NamedModule(NamedModule {
                    attributes,
                    access,
                    is_rec,
                    name,
                    decls,
                })
            }),
        prop::collection::vec(
            (
                any::<bool>(),
                prop_oneof![
                    1 => Just(NamespaceName::Global),
                    3 => long_ident().prop_map(NamespaceName::Named),
                ],
                decls(),
            )
                .prop_map(|(is_rec, name, decls)| Namespace {
                    is_rec,
                    name,
                    decls
                }),
            1..=2,
        )
        .prop_map(|ns| ImplFile::Namespaces(Vec1::from_vec(ns).expect("non-empty"))),
    ]
    .boxed()
}
