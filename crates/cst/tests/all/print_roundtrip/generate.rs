//! Generating arbitrary `borzoi_print` trees.
//!
//! Every value the tree's types allow is fair game: if some value prints as text
//! FCS rejects or reads as something else, either the printer is wrong or the
//! types let through a value F# cannot express, and both are bugs. So the leaves
//! lean on the edges: keywords and reserved words as names, names that need
//! quoting, every operator character, literal extremes, NaNs, lone surrogates.
//!
//! The strategies are generic over the tree's language version, and offer a
//! gated construct exactly where the version's gate has a witness.

use borzoi_print::names::{Ident, InfixOperator, LongIdent, Operator, TyparName, ValueName};
use borzoi_print::tree::{
    Access, AndBang, Args, ArrayRank, Attribute, AttributeArgs, Binding, BindingHead, Comp,
    CompClause, CompItem, Const, Context, Expr, Float32, Float64, ForDirection, ForSource,
    ImplFile, LetBang, LetBindings, ListBody, ListComp, LocalBindings, MatchClause, ModuleDecl,
    NamedModule, Namespace, NamespaceName, NestedModule, Pat, Range, RecordField, Stmt, StmtExpr,
    Type, TypeDefn, TypeRepr, UnionCase, UnionField, UseBang, UseBinding, UseName,
};
use borzoi_print::vec::{Vec1, Vec2};
use borzoi_print::version::{Gate, Version};
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

pub(super) const OPERATORS: &[&str] = &[
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

fn args<V: Version>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<Args<V>> {
    prop_oneof![
        prop::collection::vec(expr.clone(), 2..=3)
            .prop_map(|es| Args::Positional(Vec2::from_vec(es).expect("two"))),
        (
            prop::collection::vec(expr.clone(), 0..=2),
            prop::collection::vec((ident(), expr), 1..=2),
        )
            .prop_map(|(positional, named)| Args::Named {
                positional,
                named: Vec1::from_vec(named).expect("non-empty"),
            }),
    ]
    .boxed()
}

fn attributes<V: Version>(arg: BoxedStrategy<Expr<V>>) -> BoxedStrategy<Vec<Attribute<V>>> {
    let args = prop_oneof![
        2 => Just(AttributeArgs::Value(Expr::Const(Const::Unit))),
        1 => arg.clone().prop_map(AttributeArgs::Value),
        1 => args(arg).prop_map(AttributeArgs::List),
    ];
    prop_oneof![
        3 => Just(Vec::new()),
        1 => prop::collection::vec(
            (long_ident(), args).prop_map(|(name, args)| Attribute { name, args }),
            1..=2,
        ),
    ]
    .boxed()
}

fn binding<V: Version>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<Binding<V>> {
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

/// A `let` group an expression or computation expression takes.
fn local_bindings<V: Version>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<LocalBindings<V>> {
    let_bindings(expr)
        .prop_filter_map("access or attributes", |b| LocalBindings::new(b).ok())
        .boxed()
}

fn let_bindings<V: Version>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<LetBindings<V>> {
    prop_oneof![
        binding(expr.clone()).prop_map(|b| LetBindings::NonRec(Box::new(b))),
        prop::collection::vec(binding(expr), 1..=2)
            .prop_map(|bs| LetBindings::Rec(Vec1::from_vec(bs).expect("non-empty"))),
    ]
    .boxed()
}

fn clauses<V: Version>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<Vec1<MatchClause<V>>> {
    prop::collection::vec(
        (pat(), prop::option::weighted(0.25, expr.clone()), expr)
            .prop_map(|(pat, guard, result)| MatchClause { pat, guard, result }),
        1..=2,
    )
    .prop_map(|cs| Vec1::from_vec(cs).expect("non-empty"))
    .boxed()
}

fn comp_clauses<V: Version, K: Context>(
    expr: BoxedStrategy<Expr<V>>,
    comp: BoxedStrategy<Comp<V, K>>,
) -> BoxedStrategy<Vec1<CompClause<V, K>>> {
    prop::collection::vec(
        (pat(), prop::option::weighted(0.25, expr), comp)
            .prop_map(|(pat, guard, body)| CompClause { pat, guard, body }),
        1..=2,
    )
    .prop_map(|cs| Vec1::from_vec(cs).expect("non-empty"))
    .boxed()
}

fn range<V: Version>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<Range<V>> {
    (expr.clone(), prop::option::of(expr.clone()), expr)
        .prop_map(|(from, step, to)| Range { from, step, to })
        .boxed()
}

fn for_source<V: Version>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<ForSource<V>> {
    prop_oneof![
        2 => expr.clone().prop_map(ForSource::Expr),
        1 => range(expr).prop_map(ForSource::Range),
    ]
    .boxed()
}

/// An expression statement, of an expression `K` takes there.
fn stmt_expr<V: Version, K: Context>(
    expr: BoxedStrategy<Expr<V>>,
) -> BoxedStrategy<StmtExpr<V, K>> {
    expr.prop_filter_map("a statement-shaped expression", |e| StmtExpr::new(e).ok())
        .boxed()
}

/// A list's body: as often a literal's elements as a comprehension, and
/// sometimes a range.
fn list_body<V: Version>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<ListBody<V>> {
    prop_oneof![
        2 => prop::collection::vec(expr.clone(), 1..=3)
            .prop_map(|es| ListBody::Elements(Vec1::from_vec(es).expect("non-empty"))),
        2 => comp(expr.clone())
            .prop_filter_map("a literal's elements", |c| ListComp::new(c).ok())
            .prop_map(ListBody::Comp),
        1 => range(expr).prop_map(ListBody::Range),
    ]
    .boxed()
}

/// What a `use` or `use!` binds, a discard where `G` has one.
fn use_name<G: Gate>() -> BoxedStrategy<UseName<G>> {
    match G::WITNESS {
        Some(gate) => prop_oneof![
            3 => value_name().prop_map(UseName::Named),
            1 => Just(UseName::Discard(gate)),
        ]
        .boxed(),
        None => value_name().prop_map(UseName::Named).boxed(),
    }
}

/// `items`, each with its weight, where its gate (`None` if absent) allows.
fn gated<T: std::fmt::Debug + 'static>(
    items: Vec<(u32, Option<BoxedStrategy<T>>)>,
) -> BoxedStrategy<T> {
    proptest::strategy::Union::new_weighted(
        items
            .into_iter()
            .filter_map(|(w, s)| s.map(|s| (w, s)))
            .collect(),
    )
    .boxed()
}

/// A computation expression's body over the expressions `expr` draws, with
/// what context `K` takes.
fn comp<V: Version, K: Context>(expr: BoxedStrategy<Expr<V>>) -> BoxedStrategy<Comp<V, K>> {
    let e = expr.clone();
    let bang = K::Bang::WITNESS;
    let simple = gated(vec![
        (3, Some(stmt_expr(e.clone()).prop_map(Stmt::Expr).boxed())),
        (
            1,
            bang.map(|gate| {
                e.clone()
                    .prop_map(move |expr| Stmt::DoBang { gate, expr })
                    .boxed()
            }),
        ),
        (
            1,
            bang.map(|gate| {
                e.clone()
                    .prop_map(move |expr| Stmt::Return { gate, expr })
                    .boxed()
            }),
        ),
        (
            1,
            bang.map(|gate| {
                e.clone()
                    .prop_map(move |expr| Stmt::ReturnFrom { gate, expr })
                    .boxed()
            }),
        ),
        (1, Some(e.clone().prop_map(Stmt::Yield).boxed())),
        (1, Some(e.clone().prop_map(Stmt::YieldFrom).boxed())),
    ]);
    simple
        .clone()
        .prop_map(Comp::stmt)
        .prop_recursive(3, 12, 3, move |inner| {
            let e = expr.clone();
            let c = inner.clone().prop_map(Box::new);
            let stmt = gated(vec![
                (4, Some(simple.clone())),
                (
                    1,
                    Some(
                        (e.clone(), c.clone(), prop::option::of(c.clone()))
                            .prop_map(|(cond, then_branch, else_branch)| Stmt::IfThenElse {
                                cond,
                                then_branch,
                                else_branch,
                            })
                            .boxed(),
                    ),
                ),
                (
                    1,
                    Some(
                        (e.clone(), comp_clauses(e.clone(), inner.clone()))
                            .prop_map(|(scrutinee, clauses)| Stmt::Match { scrutinee, clauses })
                            .boxed(),
                    ),
                ),
                (
                    1,
                    bang.map(|gate| {
                        (e.clone(), comp_clauses(e.clone(), inner.clone()))
                            .prop_map(move |(scrutinee, clauses)| Stmt::MatchBang {
                                gate,
                                scrutinee,
                                clauses,
                            })
                            .boxed()
                    }),
                ),
                (
                    1,
                    Some(
                        (e.clone(), c.clone())
                            .prop_map(|(cond, body)| Stmt::While { cond, body })
                            .boxed(),
                    ),
                ),
                (
                    1,
                    V::WhileBang::WITNESS.zip(bang).map(|(gate, bang)| {
                        (e.clone(), c.clone())
                            .prop_map(move |(cond, body)| Stmt::WhileBang {
                                gate,
                                bang,
                                cond,
                                body,
                            })
                            .boxed()
                    }),
                ),
                (
                    1,
                    Some(
                        (
                            ident(),
                            e.clone(),
                            prop_oneof![Just(ForDirection::To), Just(ForDirection::Downto)],
                            e.clone(),
                            c.clone(),
                        )
                            .prop_map(|(var, from, direction, to, body)| Stmt::For {
                                var,
                                from,
                                direction,
                                to,
                                body,
                            })
                            .boxed(),
                    ),
                ),
                (
                    1,
                    Some(
                        (pat(), for_source(e.clone()), c.clone())
                            .prop_map(|(pat, source, body)| Stmt::ForEach { pat, source, body })
                            .boxed(),
                    ),
                ),
                (
                    1,
                    K::TryWith::<V>::WITNESS.map(|gate| {
                        (c.clone(), comp_clauses(e.clone(), inner.clone()))
                            .prop_map(move |(body, clauses)| Stmt::TryWith {
                                gate,
                                body,
                                clauses,
                            })
                            .boxed()
                    }),
                ),
                (
                    1,
                    Some(
                        (c.clone(), e.clone())
                            .prop_map(|(body, finally)| Stmt::TryFinally { body, finally })
                            .boxed(),
                    ),
                ),
            ]);
            let ands = match V::AndBang::WITNESS {
                Some(gate) => prop::collection::vec(
                    (pat(), e.clone()).prop_map(move |(pat, value)| AndBang { gate, pat, value }),
                    0..=2,
                )
                .boxed(),
                None => Just(Vec::new()).boxed(),
            };
            let item = gated(vec![
                (4, Some(stmt.clone().prop_map(CompItem::Stmt).boxed())),
                (
                    1,
                    Some(local_bindings(e.clone()).prop_map(CompItem::Let).boxed()),
                ),
                (
                    1,
                    Some(
                        (use_name(), e.clone())
                            .prop_map(|(name, value)| CompItem::Use(UseBinding { name, value }))
                            .boxed(),
                    ),
                ),
                (
                    1,
                    bang.map(|gate| {
                        (pat(), e.clone(), ands)
                            .prop_map(move |(pat, value, ands)| {
                                CompItem::LetBang(LetBang {
                                    gate,
                                    pat,
                                    value,
                                    ands,
                                })
                            })
                            .boxed()
                    }),
                ),
                (
                    1,
                    bang.map(|gate| {
                        (use_name(), e.clone())
                            .prop_map(move |(name, value)| {
                                CompItem::UseBang(UseBang { gate, name, value })
                            })
                            .boxed()
                    }),
                ),
            ]);
            (prop::collection::vec(item, 0..=3), stmt).prop_map(|(init, last)| Comp { init, last })
        })
        .boxed()
}

pub fn expr<V: Version>() -> BoxedStrategy<Expr<V>> {
    let mut leaves: Vec<(u32, BoxedStrategy<Expr<V>>)> = vec![
        (3, constant().prop_map(Expr::Const).boxed()),
        (1, Just(Expr::Null).boxed()),
        (4, long_ident().prop_map(Expr::Name).boxed()),
        (1, operator().prop_map(Expr::OpValue).boxed()),
    ];
    if let Some(gate) = V::AccessorFunctionShorthand::WITNESS {
        leaves.push((
            1,
            long_ident()
                .prop_map(move |path| Expr::DotLambda { gate, path })
                .boxed(),
        ));
    }
    let leaf = proptest::strategy::Union::new_weighted(leaves);
    leaf.prop_recursive(4, 24, 3, |inner| {
        let b = inner.clone().prop_map(Box::new);
        prop_oneof![
            (b.clone(), b.clone()).prop_map(|(func, arg)| Expr::App { func, arg }),
            // A tuple argument is where `App` and `MethodApp` meet, and a
            // recursive draw rarely lands on one.
            (b.clone(), prop::collection::vec(inner.clone(), 2..=3)).prop_map(|(func, es)| {
                Expr::App {
                    func,
                    arg: Box::new(Expr::Tuple(Vec2::from_vec(es).expect("two"))),
                }
            }),
            (b.clone(), args(inner.clone()))
                .prop_map(|(func, args)| Expr::MethodApp { func, args }),
            (infix_operator(), b.clone(), b.clone()).prop_map(|(op, lhs, rhs)| Expr::Infix {
                op,
                lhs,
                rhs
            }),
            prop::collection::vec(inner.clone(), 2..=3)
                .prop_map(|es| Expr::Tuple(Vec2::from_vec(es).expect("two"))),
            prop::option::weighted(0.8, list_body(inner.clone()).prop_map(Box::new))
                .prop_map(Expr::List),
            prop::option::weighted(0.8, list_body(inner.clone()).prop_map(Box::new))
                .prop_map(Expr::Array),
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
            (local_bindings(inner.clone()), b.clone())
                .prop_map(|(bindings, body)| Expr::LetIn { bindings, body }),
            (b.clone(), b.clone()).prop_map(|(x, y)| Expr::Sequential(x, y)),
            (b.clone(), ty()).prop_map(|(expr, ty)| Expr::Typed { expr, ty }),
            (b.clone(), ty()).prop_map(|(expr, ty)| Expr::TypeTest { expr, ty }),
            (b.clone(), ty()).prop_map(|(expr, ty)| Expr::Upcast { expr, ty }),
            (b.clone(), ty()).prop_map(|(expr, ty)| Expr::Downcast { expr, ty }),
            (b.clone(), b.clone()).prop_map(|(head, tail)| Expr::Cons { head, tail }),
            (b.clone(), clauses(inner.clone()))
                .prop_map(|(body, clauses)| Expr::TryWith { body, clauses }),
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
            (
                pat(),
                for_source(inner.clone()).prop_map(Box::new),
                b.clone()
            )
                .prop_map(|(pat, source, body)| Expr::ForEach { pat, source, body }),
            (
                prop_oneof![
                    3 => long_ident().prop_map(Expr::Name),
                    1 => inner.clone(),
                ]
                .prop_map(Box::new),
                comp(inner.clone()).prop_map(Box::new),
            )
                .prop_map(|(builder, body)| Expr::Computation { builder, body }),
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

fn type_defn<V: Version>() -> BoxedStrategy<TypeDefn<V>> {
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

fn decls<V: Version>() -> BoxedStrategy<Vec<ModuleDecl<V>>> {
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

pub fn impl_file<V: Version>() -> BoxedStrategy<ImplFile<V>> {
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
