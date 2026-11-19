//! Generating well-typed `borzoi_print` trees, for FCS's checker to grade.
//!
//! [`super::generate`] draws every value the tree's types allow, but over
//! arbitrary names, so only F#'s parser can grade its trees: the checker would
//! report the names unbound. Here each expression is drawn for a type, out of
//! [`super::check::PRELUDE`]'s names and the binders in scope, so FCS's
//! checker must accept the file. The syntax around those leaves is drawn as
//! freely as the tree allows: every binding modifier in every combination,
//! every statement in every body, names that need quoting. Where the tree's
//! own constructors refuse a value ([`LocalBindings::new`], [`StmtExpr::new`],
//! [`ListComp::new`]), the draw is filtered through them, so what reaches the
//! checker is what the types admit; a checker error is then a value F# cannot
//! express that the types let through, or a printer bug.
//!
//! The generator does not draw what F#'s checker refuses for reasons the tree
//! cannot see, which are name resolution's and inference's, not syntax's: it
//! keeps names in scope and of the right type, a name bound once per pattern
//! and per module, a local `mutable` out of closures, a recursive group's
//! names clear of what its bodies see, an inline body clear of less
//! accessible values (FS1113), and every type fixed before the checker reads
//! it: a parameter annotated whole, a lookup's receiver and a runtime test's
//! subject annotated, and `null` never left to an operator's resolution.
//!
//! [`run`] draws each tree on a runner of its own, capped in filter
//! rejections: a filter whose predicate cannot pass by redrawing what it
//! filters fails there, naming itself, rather than spinning.

use std::collections::BTreeSet;
use std::fmt::Debug;
use std::rc::Rc;

use borzoi_print::names::{
    EntityName, ExceptionName, Ident, InfixOperator, LongIdent, Operator, UnionCaseName, ValueName,
    VarName,
};
use borzoi_print::tree::{
    Access, AliasPat, AndBang, Args, ArrayRank, AsAlias, Attribute, AttributeArgs, Binding,
    BindingHead, Comp, CompClause, CompItem, Const, Context, ExceptionDefn, Expr, ForDirection,
    ForSource, ImplFile, InBuilder, InCollection, LetBang, LetBindings, ListBody, ListComp,
    LocalBindings, MatchClause, ModuleBindings, ModuleBody, ModuleDecl, NestedModule, Pat, Range,
    RecDecls, RecordField, Stmt, StmtExpr, Type, TypeDefn, TypeRepr, UnionCase, UnionField,
    UseBang, UseBinding, UseName,
};
use borzoi_print::vec::{Vec1, Vec2};
use borzoi_print::version::{Gate, Version};
use proptest::prelude::*;
use proptest::strategy::{BoxedStrategy, Union};

/// The types the generator draws expressions of.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Int,
    Bool,
    Unit,
    Str,
    Obj,
    Exn,
    Disposable,
    /// The prelude's record `R`, with fields `A` and `mutable C`, both `int`.
    Record,
    /// The prelude's builder type `B`.
    Builder,
    List(Box<Ty>),
    Array(Box<Ty>),
    Seq(Box<Ty>),
    Option(Box<Ty>),
    Lazy(Box<Ty>),
    Tuple(Vec<Ty>),
    Fun(Box<Ty>, Box<Ty>),
}

impl Ty {
    fn list(t: Ty) -> Ty {
        Ty::List(Box::new(t))
    }

    fn fun(a: Ty, b: Ty) -> Ty {
        Ty::Fun(Box::new(a), Box::new(b))
    }

    /// Whether F#'s `=` takes values of the type.
    fn has_equality(&self) -> bool {
        match self {
            Ty::Fun(..) => false,
            Ty::List(t) | Ty::Array(t) | Ty::Option(t) => t.has_equality(),
            Ty::Tuple(ts) => ts.iter().all(Ty::has_equality),
            _ => true,
        }
    }
}

fn ident(s: &str) -> Ident {
    Ident::new(s).expect("an identifier")
}

fn path(s: &str) -> LongIdent {
    LongIdent(Vec1::from_vec(s.split('.').map(ident).collect()).expect("non-empty"))
}

fn name<V: Version>(s: &str) -> Expr<V> {
    Expr::Name(path(s))
}

fn named(s: &str) -> Type {
    Type::Name(path(s))
}

fn app(head: &str, arg: Type) -> Type {
    Type::App {
        head: path(head),
        args: Vec1::new(arg, Vec::new()),
    }
}

/// The type as F# spells it.
pub fn type_of(ty: &Ty) -> Type {
    match ty {
        Ty::Int => named("int"),
        Ty::Bool => named("bool"),
        Ty::Unit => named("unit"),
        Ty::Str => named("string"),
        Ty::Obj => named("obj"),
        Ty::Exn => named("exn"),
        Ty::Disposable => named("System.IDisposable"),
        Ty::Record => named("R"),
        Ty::Builder => named("B"),
        Ty::List(t) => app("list", type_of(t)),
        Ty::Array(t) => Type::Array {
            rank: ArrayRank::new(1).expect("rank 1"),
            elem: Box::new(type_of(t)),
        },
        Ty::Seq(t) => app("seq", type_of(t)),
        Ty::Option(t) => app("option", type_of(t)),
        Ty::Lazy(t) => app("Lazy", type_of(t)),
        Ty::Tuple(ts) => {
            Type::Tuple(Vec2::from_vec(ts.iter().map(type_of).collect()).expect("two"))
        }
        Ty::Fun(a, b) => Type::Fun {
            arg: Box::new(type_of(a)),
            ret: Box::new(type_of(b)),
        },
    }
}

/// A value in scope: its path, its type, and whether it is a `mutable` that
/// a closure must not capture.
#[derive(Debug, Clone)]
pub struct Var {
    path: LongIdent,
    ty: Ty,
    local_mutable: bool,
    /// Whether it is a mutable an assignment may target.
    mutable: bool,
    /// Whether it is not visible outside its module: `private`, or brought
    /// into scope by an `open`.
    private: bool,
    /// Whether it is less accessible than public, `private` or `internal`
    /// itself or through its module, so an inline value may not use it
    /// (FS1113).
    restricted: bool,
}

/// What is in scope: the values, innermost last, a shadowed one dropped.
#[derive(Debug, Clone, Default)]
pub struct Scope {
    vars: Vec<Var>,
    /// Nested modules defined so far, which `open` and module abbreviations
    /// may name.
    modules: Vec<Ident>,
}

type Sc = Rc<Scope>;

impl Scope {
    /// The scope with `new` bound, each hiding what it shadows: a variable of
    /// its path, and, for a value `n`, every `n.x` through a module `n`, as
    /// F# reads a dotted name's head as a value first.
    fn with(&self, new: impl IntoIterator<Item = Var>) -> Scope {
        let mut out = self.clone();
        for v in new {
            let head = &v.path.segments()[0];
            let single = v.path.segments().len() == 1;
            out.vars.retain(|w| {
                w.path != v.path
                    && !(single && w.path.segments().len() > 1 && &w.path.segments()[0] == head)
            });
            out.vars.push(v);
        }
        out
    }

    /// Whether `n` heads a value's path or names a module in scope.
    fn names(&self, n: &Ident) -> bool {
        self.vars.iter().any(|v| &v.path.segments()[0] == n) || self.modules.contains(n)
    }

    /// The scope inside a closure: a local `mutable` cannot be captured.
    fn closure(&self) -> Scope {
        let mut out = self.clone();
        out.vars.retain(|v| !v.local_mutable);
        out
    }

    fn of_type(&self, ty: &Ty) -> Vec<LongIdent> {
        self.vars
            .iter()
            .filter(|v| v.ty == *ty)
            .map(|v| v.path.clone())
            .collect()
    }
}

fn local(name: &Ident, ty: Ty) -> Var {
    Var {
        path: LongIdent::single(name.clone()),
        ty,
        local_mutable: false,
        mutable: false,
        private: false,
        restricted: false,
    }
}

/// The prelude's values, by type.
pub fn prelude_scope() -> Scope {
    let v = |p: &str, ty: Ty| local(&ident(p), ty);
    Scope {
        vars: vec![
            v("builder", Ty::Builder),
            v("c", Ty::Bool),
            v("u", Ty::Unit),
            v("e", Ty::Obj),
            v("a", Ty::Int),
            v("b", Ty::Int),
            v("v", Ty::Disposable),
            v("t", Ty::Tuple(vec![Ty::Int, Ty::Int])),
            v("xs", Ty::Seq(Box::new(Ty::Obj))),
            v("ss", Ty::Seq(Box::new(Ty::Str))),
            v("w", Ty::Str),
            v("ls", Ty::list(Ty::Int)),
            v("rv", Ty::Record),
        ],
        modules: Vec::new(),
    }
}

/// Binder names: plain, quoted, primed, and the prelude's own, shadowing it.
const BINDERS: &[&str] = &[
    "x", "y", "p", "q", "x'", "a b", "val", "c", "t", "rec'", "Item", "Item2", "Data0",
];

/// Names in the type namespace: types, exceptions, union cases, modules. Some
/// start lower case, which F# refuses of a union case or an exception; `IsT`
/// is `T`'s tester from F# 9. Not `op_Nil` or `op_ColonColon`, which a union
/// case may be named but which then shadow `[]` and `::`. None is a value's
/// name ([`BINDERS`], [`prelude_scope`]), as a value shadows a module of its
/// name in a dotted path, which the scope does not follow.
const TYPE_NAMES: &[&str] = &[
    "T", "U", "E", "N", "Q", "t1", "type", "Ä", "Tags", "A.B", "IsT", "IsQ",
];

#[test]
fn value_and_type_names_are_disjoint() {
    let values: Vec<String> = BINDERS
        .iter()
        .map(|s| (*s).to_owned())
        .chain(
            prelude_scope()
                .vars
                .iter()
                .map(|v| v.path.segments()[0].as_str().to_owned()),
        )
        .collect();
    for t in TYPE_NAMES {
        assert!(
            !values.iter().any(|v| v == t),
            "{t:?} names a value and a module"
        );
    }
}

fn binder() -> BoxedStrategy<Ident> {
    prop::sample::select(BINDERS).prop_map(ident).boxed()
}

fn type_name() -> BoxedStrategy<Ident> {
    prop::sample::select(TYPE_NAMES)
        .prop_filter_map("not an identifier", |s| Ident::new(s).ok())
        .boxed()
}

/// `f`'s strategy, built only when drawn: the generator's strategies depend on
/// what is drawn above them, so building them eagerly would build every branch
/// at every depth.
fn defer<T: Debug + Clone + 'static>(
    f: impl Fn() -> BoxedStrategy<T> + 'static,
) -> BoxedStrategy<T> {
    Just(()).prop_flat_map(move |()| f()).boxed()
}

/// Weighted alternatives, for [`weighted`].
type Alts<T> = Vec<(u32, BoxedStrategy<T>)>;

fn weighted<T: Debug + 'static>(items: Alts<T>) -> BoxedStrategy<T> {
    Union::new_weighted(items).boxed()
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

/// A type to draw a subexpression at, `depth` levels of type constructors
/// deep at most.
pub fn arb_ty(depth: u32) -> BoxedStrategy<Ty> {
    let leaf = prop_oneof![
        4 => Just(Ty::Int),
        2 => Just(Ty::Bool),
        2 => Just(Ty::Str),
        1 => Just(Ty::Unit),
        1 => Just(Ty::Obj),
        1 => Just(Ty::Record),
        1 => Just(Ty::Exn),
        1 => Just(Ty::Disposable),
    ];
    leaf.prop_recursive(depth, 8, 2, |inner| {
        prop_oneof![
            inner.clone().prop_map(Ty::list),
            inner.clone().prop_map(|t| Ty::Array(Box::new(t))),
            inner.clone().prop_map(|t| Ty::Seq(Box::new(t))),
            inner.clone().prop_map(|t| Ty::Option(Box::new(t))),
            inner.clone().prop_map(|t| Ty::Lazy(Box::new(t))),
            prop::collection::vec(inner.clone(), 2..=3).prop_map(Ty::Tuple),
            (inner.clone(), inner).prop_map(|(a, b)| Ty::fun(a, b)),
        ]
    })
    .boxed()
}

fn int_const<V: Version>() -> BoxedStrategy<Expr<V>> {
    prop_oneof![Just(0), Just(1), Just(-1), Just(i32::MIN), any::<i32>()]
        .prop_map(|n| Expr::Const(Const::Int32(n)))
        .boxed()
}

/// Constants of the type, if it has any.
fn constants<V: Version>(ty: &Ty) -> Option<BoxedStrategy<Expr<V>>> {
    Some(match ty {
        Ty::Int => int_const(),
        Ty::Bool => any::<bool>()
            .prop_map(|b| Expr::Const(Const::Bool(b)))
            .boxed(),
        Ty::Unit => Just(Expr::Const(Const::Unit)).boxed(),
        Ty::Str => prop_oneof!["[a-z]{0,3}", ".{0,3}"]
            .prop_map(|s| Expr::Const(Const::String(s)))
            .boxed(),
        _ => return None,
    })
}

/// The binders a pattern binds, with their types.
type Bound = Vec<(Ident, Ty)>;

fn distinct(bound: &Bound) -> bool {
    let names: BTreeSet<&str> = bound.iter().map(|(n, _)| n.as_str()).collect();
    names.len() == bound.len()
}

fn vars(bound: &Bound) -> Vec<Var> {
    bound.iter().map(|(n, t)| local(n, t.clone())).collect()
}

/// A pattern matching values of `ty`, binding names only if `binds`, with
/// what it binds; each name bound once.
pub fn pat<V: Version>(ty: &Ty, depth: u32, binds: bool) -> BoxedStrategy<(Pat<V>, Bound)> {
    let ty = ty.clone();
    defer(move || pat_raw::<V>(&ty, depth, binds))
        .prop_filter("a name bound twice", |(_, b)| distinct(b))
        .boxed()
}

fn pat_raw<V: Version>(ty: &Ty, depth: u32, binds: bool) -> BoxedStrategy<(Pat<V>, Bound)> {
    let mut alts: Alts<(Pat<V>, Bound)> = vec![(2, Just((Pat::Wildcard, Vec::new())).boxed())];
    if binds {
        let t = ty.clone();
        alts.push((
            4,
            binder()
                .prop_map(move |n| {
                    (
                        Pat::Name(LongIdent::single(n.clone())),
                        vec![(n, t.clone())],
                    )
                })
                .boxed(),
        ));
    }
    let leaf = |p: Pat<V>| (2, Just((p, Vec::new())).boxed());
    match ty {
        Ty::Int => alts.push((
            2,
            prop_oneof![Just(0), Just(-1), any::<i32>()]
                .prop_map(|n| (Pat::Const(Const::Int32(n)), Vec::new()))
                .boxed(),
        )),
        Ty::Bool => alts.push((
            2,
            any::<bool>()
                .prop_map(|b| (Pat::Const(Const::Bool(b)), Vec::new()))
                .boxed(),
        )),
        Ty::Unit => alts.push(leaf(Pat::Const(Const::Unit))),
        Ty::Str => {
            alts.push(leaf(Pat::Const(Const::String("s".into()))));
            alts.push(leaf(Pat::Null));
        }
        Ty::Obj => {
            alts.push(leaf(Pat::Null));
            for t in ["int", "string", "R"] {
                alts.push(leaf(Pat::IsInst(named(t))));
            }
        }
        Ty::Exn => {
            alts.push(leaf(Pat::IsInst(named("System.ArgumentException"))));
            if depth > 0 {
                alts.push((
                    2,
                    pat::<V>(&Ty::Str, depth - 1, binds)
                        .prop_map(|(p, b)| {
                            (
                                Pat::Ctor {
                                    name: path("Failure"),
                                    args: Vec1::new(p, Vec::new()),
                                },
                                b,
                            )
                        })
                        .boxed(),
                ));
            }
        }
        _ => {}
    }
    if depth == 0 {
        return weighted(alts);
    }
    let d = depth - 1;
    match ty {
        Ty::Tuple(ts) => {
            let parts: Vec<_> = ts.iter().map(|t| pat::<V>(t, d, binds)).collect();
            alts.push((
                3,
                parts
                    .prop_map(|ps| {
                        let (pats, bound): (Vec<Pat<V>>, Vec<Bound>) = ps.into_iter().unzip();
                        (
                            Pat::Tuple(Vec2::from_vec(pats).expect("two")),
                            bound.concat(),
                        )
                    })
                    .boxed(),
            ));
        }
        Ty::List(t) | Ty::Array(t) => {
            let is_list = matches!(ty, Ty::List(_));
            alts.push((
                2,
                prop::collection::vec(pat::<V>(t, d, binds), 0..=2)
                    .prop_map(move |ps| {
                        let (pats, bound): (Vec<Pat<V>>, Vec<Bound>) = ps.into_iter().unzip();
                        let p = if is_list {
                            Pat::List(pats)
                        } else {
                            Pat::Array(pats)
                        };
                        (p, bound.concat())
                    })
                    .boxed(),
            ));
            if is_list {
                alts.push((
                    2,
                    (pat::<V>(t, d, binds), pat::<V>(ty, d, binds))
                        .prop_map(|((h, hb), (tl, tb))| {
                            (
                                Pat::Cons {
                                    head: Box::new(h),
                                    tail: Box::new(tl),
                                },
                                [hb, tb].concat(),
                            )
                        })
                        .boxed(),
                ));
            }
        }
        Ty::Option(t) => {
            alts.push(leaf(Pat::Name(path("None"))));
            alts.push((
                2,
                pat::<V>(t, d, binds)
                    .prop_map(|(p, b)| {
                        (
                            Pat::Ctor {
                                name: path("Some"),
                                args: Vec1::new(p, Vec::new()),
                            },
                            b,
                        )
                    })
                    .boxed(),
            ));
        }
        Ty::Record => {
            alts.push((
                2,
                (
                    prop::sample::subsequence(vec!["A", "R.A", "C"], 1..=2),
                    pat::<V>(&Ty::Int, d, binds),
                    pat::<V>(&Ty::Int, d, binds),
                )
                    .prop_filter("a field twice", |(fs, _, _)| {
                        !(fs.contains(&"A") && fs.contains(&"R.A"))
                    })
                    .prop_map(|(fs, p1, p2)| {
                        let mut bound = Vec::new();
                        let mut fields = Vec::new();
                        for (f, (p, b)) in fs.into_iter().zip([p1, p2]) {
                            fields.push((path(f), p));
                            bound.extend(b);
                        }
                        (
                            Pat::Record(Vec1::from_vec(fields).expect("non-empty")),
                            bound,
                        )
                    })
                    .boxed(),
            ));
        }
        _ => {}
    }
    let t = ty.clone();
    alts.push((
        2,
        pat::<V>(&t, d, binds)
            .prop_map(move |(p, b)| {
                (
                    Pat::Typed {
                        pat: Box::new(p),
                        ty: type_of(&t),
                    },
                    b,
                )
            })
            .boxed(),
    ));
    // Each side of `|` binds nothing, so both bind the same names.
    alts.push((
        1,
        (pat::<V>(ty, d, false), pat::<V>(ty, d, false))
            .prop_map(|((l, _), (r, _))| (Pat::Or(Box::new(l), Box::new(r)), Vec::new()))
            .boxed(),
    ));
    alts.push((
        1,
        (pat::<V>(ty, d, binds), pat::<V>(ty, d, binds))
            .prop_map(|((l, lb), (r, rb))| {
                (Pat::Ands(Vec2::new(l, r, Vec::new())), [lb, rb].concat())
            })
            .boxed(),
    ));
    if binds {
        let t = ty.clone();
        alts.push((
            1,
            (pat::<V>(ty, d, binds), binder())
                // A name F# could read as a constructor's is a variable
                // alias only from F# 6, as a pattern.
                .prop_filter_map("an alias F# refuses", move |((p, b), n)| {
                    let at = narrowed(&p, &t)?;
                    let alias = match VarName::new(n.clone()) {
                        Ok(v) => AsAlias::Var(v),
                        Err(n) => AsAlias::Pat(
                            AliasPat::new(
                                V::NonVariablePatternsToRightOfAsPatterns::WITNESS?,
                                Pat::Name(LongIdent::single(n)),
                            )
                            .ok()?,
                        ),
                    };
                    let mut bound = b;
                    bound.push((n, at));
                    Some((
                        Pat::As {
                            pat: Box::new(p),
                            alias,
                        },
                        bound,
                    ))
                })
                .boxed(),
        ));
        // `p as q` with `q` any pattern but a variable, at the type `p`
        // narrows to (F# 6).
        if let Some(gate) = V::NonVariablePatternsToRightOfAsPatterns::WITNESS {
            let t = ty.clone();
            let lhs = pat::<V>(ty, d, binds).prop_filter("a type test at no type of the scope", {
                let t = t.clone();
                move |(p, _)| narrowed(p, &t).is_some()
            });
            alts.push((
                1,
                lhs.prop_flat_map(move |(p, b)| {
                    let at = narrowed(&p, &t).expect("filtered above");
                    pat::<V>(&at, d, binds).prop_filter_map(
                        "a variable, or a name bound twice",
                        move |(q, qb)| {
                            let bound: Bound = b.iter().chain(&qb).cloned().collect();
                            distinct(&bound).then_some(())?;
                            let alias = AliasPat::new(gate, q).ok()?;
                            Some((
                                Pat::As {
                                    pat: Box::new(p.clone()),
                                    alias: AsAlias::Pat(alias),
                                },
                                bound,
                            ))
                        },
                    )
                })
                .boxed(),
            ));
        }
    }
    weighted(alts)
}

/// The type `p as q` matches `q` at: `T` after `:? T`, else `ty`, the type
/// `p` matches. `None` for a type test at a type the scope has no values of
/// (`System.ArgumentException`).
fn narrowed<V: Version>(p: &Pat<V>, ty: &Ty) -> Option<Ty> {
    let Pat::IsInst(tested) = p else {
        return Some(ty.clone());
    };
    let Type::Name(path) = tested else {
        return None;
    };
    match path.segments() {
        [only] => match only.as_str() {
            "int" => Some(Ty::Int),
            "string" => Some(Ty::Str),
            "R" => Some(Ty::Record),
            _ => None,
        },
        _ => None,
    }
}

/// A pattern for a binder, annotated whole: its type must be fixed before its
/// uses, which may test its runtime type, look a member up, or stand as an
/// implicit yield, whose reading F# decides by the type known at that point.
fn param<V: Version>(ty: &Ty, depth: u32) -> BoxedStrategy<(Pat<V>, Bound)> {
    let t = ty.clone();
    pat::<V>(ty, depth, true)
        .prop_map(move |(p, b)| {
            let p = if !matches!(p, Pat::Typed { .. }) {
                Pat::Typed {
                    pat: Box::new(p),
                    ty: type_of(&t),
                }
            } else {
                p
            };
            (p, b)
        })
        .boxed()
}

fn bx<V: Version>(e: Expr<V>) -> Box<Expr<V>> {
    Box::new(e)
}

/// An expression of type `ty` in scope `sc`, `depth` levels deep at most
/// (beyond the few levels a type's simplest value needs).
pub fn expr<V: Version>(ty: &Ty, sc: &Sc, depth: u32) -> BoxedStrategy<Expr<V>> {
    let (t, s) = (ty.clone(), sc.clone());
    defer(move || expr_now::<V>(&t, &s, depth))
}

/// The simplest values of `ty`: a name in scope, a constant, or the type's
/// constructor over simplest values.
fn simplest<V: Version>(ty: &Ty, sc: &Sc) -> BoxedStrategy<Expr<V>> {
    let mut alts: Vec<(u32, BoxedStrategy<Expr<V>>)> = Vec::new();
    let names = sc.of_type(ty);
    if !names.is_empty() {
        alts.push((3, prop::sample::select(names).prop_map(Expr::Name).boxed()));
    }
    if let Some(c) = constants(ty) {
        alts.push((3, c));
    }
    let s = sc.clone();
    let simple = move |t: &Ty| {
        let (t, s) = (t.clone(), s.clone());
        defer(move || simplest::<V>(&t, &s))
    };
    let made: BoxedStrategy<Expr<V>> = match ty {
        Ty::Int | Ty::Bool | Ty::Unit => {
            return weighted(alts);
        }
        Ty::Str => Just(Expr::Null).boxed(),
        Ty::Obj => prop_oneof![
            Just(Expr::Null),
            simple(&Ty::Int).prop_map(|e| Expr::Upcast {
                expr: bx(e),
                ty: named("obj"),
            }),
        ]
        .boxed(),
        Ty::Exn => simple(&Ty::Str)
            .prop_map(|m| Expr::App {
                func: bx(name("Failure")),
                arg: bx(m),
            })
            .boxed(),
        Ty::Disposable => Just(name("v")).boxed(),
        Ty::Record => (simple(&Ty::Int), simple(&Ty::Int))
            .prop_map(|(a, c)| Expr::Record {
                copy: None,
                fields: Vec1::new((path("A"), a), vec![(path("C"), c)]),
            })
            .boxed(),
        Ty::Builder => Just(Expr::App {
            func: bx(name("B")),
            arg: bx(Expr::Const(Const::Unit)),
        })
        .boxed(),
        Ty::List(t) => prop_oneof![
            Just(Expr::List(None)),
            simple(t).prop_map(|e| Expr::List(Some(Box::new(ListBody::Elements(Vec1::new(
                e,
                Vec::new()
            )))))),
        ]
        .boxed(),
        Ty::Array(t) => prop_oneof![
            Just(Expr::Array(None)),
            simple(t).prop_map(|e| Expr::Array(Some(Box::new(ListBody::Elements(Vec1::new(
                e,
                Vec::new()
            )))))),
        ]
        .boxed(),
        Ty::Seq(_) => Just(name("Seq.empty")).boxed(),
        Ty::Option(t) => prop_oneof![
            Just(name("None")),
            simple(t).prop_map(|e| Expr::App {
                func: bx(name("Some")),
                arg: bx(e),
            }),
        ]
        .boxed(),
        Ty::Lazy(t) => simple(t).prop_map(|e| Expr::Lazy(bx(e))).boxed(),
        Ty::Tuple(ts) => ts
            .iter()
            .map(&simple)
            .collect::<Vec<_>>()
            .prop_map(|es| Expr::Tuple(Vec2::from_vec(es).expect("two")))
            .boxed(),
        Ty::Fun(a, b) => {
            let inner = Rc::new(sc.closure());
            let b = (**b).clone();
            param::<V>(a, 1)
                .prop_flat_map(move |(p, bound)| {
                    let s = Rc::new(inner.with(vars(&bound)));
                    simplest::<V>(&b, &s).prop_map(move |body| Expr::Lambda {
                        params: Vec1::new(p.clone(), Vec::new()),
                        body: bx(body),
                    })
                })
                .boxed()
        }
    };
    alts.push((2, made));
    weighted(alts)
}

/// `e : obj`, so a runtime test or coercion from it is from `obj`, not from
/// the type `null` has before inference fixes it (FS0008).
fn as_obj<V: Version>(e: Expr<V>) -> Expr<V> {
    Expr::Typed {
        expr: bx(e),
        ty: named("obj"),
    }
}

/// `rule`'s strategy for `ty` in `sc` at `depth`, built only when drawn.
fn rule<V: Version>(
    w: u32,
    ty: &Ty,
    sc: &Sc,
    depth: u32,
    rule: fn(&Ty, &Sc, u32) -> BoxedStrategy<Expr<V>>,
) -> (u32, BoxedStrategy<Expr<V>>) {
    let (t, s) = (ty.clone(), sc.clone());
    (w, defer(move || rule(&t, &s, depth)))
}

fn expr_now<V: Version>(ty: &Ty, sc: &Sc, depth: u32) -> BoxedStrategy<Expr<V>> {
    if depth == 0 {
        return simplest(ty, sc);
    }
    let d = depth - 1;
    let mut alts = vec![(6, simplest::<V>(ty, sc))];
    // Rules for any type.
    alts.push(rule(2, ty, sc, d, |ty, sc, d| {
        // `f x`, the function drawn at `arg -> ty`.
        arb_ty(1)
            .prop_flat_map({
                let (ty, sc) = (ty.clone(), sc.clone());
                move |a| {
                    (
                        expr::<V>(&Ty::fun(a.clone(), ty.clone()), &sc, d),
                        expr::<V>(&a, &sc, d),
                    )
                }
            })
            .prop_map(|(func, arg)| Expr::App {
                func: bx(func),
                arg: bx(arg),
            })
            .boxed()
    }));
    alts.push(rule(1, ty, sc, d, |ty, sc, d| {
        // `f (a, b)`: a function of a pair applied to an argument list.
        (arb_ty(0), arb_ty(0))
            .prop_flat_map({
                let (ty, sc) = (ty.clone(), sc.clone());
                move |(a, b)| {
                    let f = Ty::fun(Ty::Tuple(vec![a.clone(), b.clone()]), ty.clone());
                    (
                        expr::<V>(&f, &sc, d),
                        expr::<V>(&a, &sc, d),
                        expr::<V>(&b, &sc, d),
                    )
                }
            })
            .prop_map(|(func, x, y)| Expr::MethodApp {
                func: bx(func),
                args: Args::Positional(Vec2::new(x, y, Vec::new())),
            })
            .boxed()
    }));
    alts.push(rule(1, ty, sc, d, |ty, sc, d| {
        // `x |> f` and `f <| x`.
        (arb_ty(1), any::<bool>())
            .prop_flat_map({
                let (ty, sc) = (ty.clone(), sc.clone());
                move |(a, forward)| {
                    (
                        expr::<V>(&a, &sc, d),
                        expr::<V>(&Ty::fun(a, ty.clone()), &sc, d),
                        Just(forward),
                    )
                }
            })
            .prop_map(|(x, f, forward)| {
                let (op, lhs, rhs) = if forward { ("|>", x, f) } else { ("<|", f, x) };
                Expr::Infix {
                    op: infix(op),
                    lhs: bx(lhs),
                    rhs: bx(rhs),
                }
            })
            .boxed()
    }));
    alts.push(rule(2, ty, sc, d, |ty, sc, d| {
        let unit = *ty == Ty::Unit;
        (
            expr::<V>(&Ty::Bool, sc, d),
            expr::<V>(ty, sc, d),
            if unit {
                prop::option::of(expr::<V>(ty, sc, d)).boxed()
            } else {
                expr::<V>(ty, sc, d).prop_map(Some).boxed()
            },
        )
            .prop_map(|(cond, then_branch, else_branch)| Expr::IfThenElse {
                cond: bx(cond),
                then_branch: bx(then_branch),
                else_branch: else_branch.map(bx),
            })
            .boxed()
    }));
    alts.push(rule(2, ty, sc, d, |ty, sc, d| {
        arb_ty(1)
            .prop_flat_map({
                let (ty, sc) = (ty.clone(), sc.clone());
                move |s| (expr::<V>(&s, &sc, d), clauses::<V>(&s, &ty, &sc, d))
            })
            .prop_map(|(scrutinee, clauses)| Expr::Match {
                scrutinee: bx(scrutinee),
                clauses,
            })
            .boxed()
    }));
    alts.push(rule(2, ty, sc, d, |ty, sc, d| {
        let ty = ty.clone();
        let sc = sc.clone();
        bindings::<V>(&sc, d, false)
            .prop_filter_map("F# refuses the group locally", |(b, bound)| {
                LocalBindings::new(b).ok().map(|b| (b, bound))
            })
            .prop_flat_map(move |(bindings, bound)| {
                let s = Rc::new(sc.with(bound));
                expr::<V>(&ty, &s, d).prop_map(move |body| Expr::LetIn {
                    bindings: bindings.clone(),
                    body: bx(body),
                })
            })
            .boxed()
    }));
    alts.push(rule(1, ty, sc, d, |ty, sc, d| {
        (expr::<V>(&Ty::Unit, sc, d), expr::<V>(ty, sc, d))
            .prop_map(|(x, y)| Expr::Sequential(bx(x), bx(y)))
            .boxed()
    }));
    alts.push(rule(1, ty, sc, d, |ty, sc, d| {
        let t = ty.clone();
        (expr::<V>(ty, sc, d), prop::bool::weighted(0.2))
            .prop_map(move |(e, anon)| Expr::Typed {
                expr: bx(e),
                ty: if anon { Type::Anon } else { type_of(&t) },
            })
            .boxed()
    }));
    alts.push(rule(1, ty, sc, d, |ty, sc, d| {
        (expr::<V>(ty, sc, d), exn_clauses::<V>(ty, sc, d))
            .prop_map(|(body, clauses)| Expr::TryWith {
                body: bx(body),
                clauses,
            })
            .boxed()
    }));
    alts.push(rule(1, ty, sc, d, |ty, sc, d| {
        (expr::<V>(ty, sc, d), expr::<V>(&Ty::Unit, sc, d))
            .prop_map(|(body, finally)| Expr::TryFinally {
                body: bx(body),
                finally: bx(finally),
            })
            .boxed()
    }));
    alts.push(rule(1, ty, sc, d, |ty, sc, d| {
        expr::<V>(&Ty::Lazy(Box::new(ty.clone())), sc, d)
            .prop_map(|e| Expr::FieldGet {
                expr: bx(e),
                field: ident("Value"),
            })
            .boxed()
    }));
    if !matches!(ty, Ty::Obj) {
        alts.push(rule(1, ty, sc, d, |ty, sc, d| {
            let t = type_of(ty);
            expr::<V>(&Ty::Obj, sc, d)
                .prop_map(move |e| Expr::Downcast {
                    expr: bx(as_obj(e)),
                    ty: t.clone(),
                })
                .boxed()
        }));
    }
    match ty {
        Ty::Int => {
            alts.push(rule(3, ty, sc, d, |_, sc, d| {
                (
                    prop::sample::select(vec![
                        "+", "-", "*", "/", "%", "&&&", "|||", "^^^", "<<<", ">>>",
                    ]),
                    expr::<V>(&Ty::Int, sc, d),
                    expr::<V>(&Ty::Int, sc, d),
                )
                    .prop_map(|(op, l, r)| Expr::Infix {
                        op: infix(op),
                        lhs: bx(l),
                        rhs: bx(r),
                    })
                    .boxed()
            }));
            alts.push(rule(2, ty, sc, d, |_, sc, d| method_call::<V>(sc, d)));
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                prop_oneof![
                    expr::<V>(&Ty::Record, sc, d).prop_map(|r| (r, Ty::Record, "A")),
                    expr::<V>(&Ty::Record, sc, d).prop_map(|r| (r, Ty::Record, "C")),
                    expr::<V>(&Ty::Str, sc, d).prop_map(|s| (s, Ty::Str, "Length")),
                ]
                // Annotated, as a member's lookup needs its object's type
                // fixed (FS0072).
                .prop_map(|(e, t, f)| Expr::FieldGet {
                    expr: bx(Expr::Typed {
                        expr: bx(e),
                        ty: type_of(&t),
                    }),
                    field: ident(f),
                })
                .boxed()
            }));
        }
        Ty::Bool => {
            alts.push(rule(2, ty, sc, d, |_, sc, d| {
                (
                    prop::sample::select(vec!["&&", "||"]),
                    expr::<V>(&Ty::Bool, sc, d),
                    expr::<V>(&Ty::Bool, sc, d),
                )
                    .prop_map(|(op, l, r)| Expr::Infix {
                        op: infix(op),
                        lhs: bx(l),
                        rhs: bx(r),
                    })
                    .boxed()
            }));
            alts.push(rule(2, ty, sc, d, |_, sc, d| {
                (
                    arb_ty(1),
                    prop::sample::select(vec!["=", "<>", "<", ">=", "<="]),
                )
                    .prop_filter("no ordering", |(t, op)| {
                        t.has_equality()
                            && (matches!(*op, "=" | "<>") || matches!(t, Ty::Int | Ty::Str))
                    })
                    .prop_flat_map({
                        let sc = sc.clone();
                        move |(t, op)| (Just(op), expr::<V>(&t, &sc, d), expr::<V>(&t, &sc, d))
                    })
                    .prop_map(|(op, l, r)| Expr::Infix {
                        op: infix(op),
                        lhs: bx(l),
                        rhs: bx(r),
                    })
                    .boxed()
            }));
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                (
                    expr::<V>(&Ty::Obj, sc, d),
                    prop::sample::select(vec!["int", "string", "R"]),
                )
                    .prop_map(|(e, t)| Expr::TypeTest {
                        expr: bx(as_obj(e)),
                        ty: named(t),
                    })
                    .boxed()
            }));
        }
        Ty::Unit => {
            alts.push(rule(2, ty, sc, d, |_, sc, d| {
                let targets: Vec<(LongIdent, Ty)> = sc
                    .vars
                    .iter()
                    .filter(|v| v.mutable)
                    .map(|v| (v.path.clone(), v.ty.clone()))
                    .chain([(path("rv.C"), Ty::Int)])
                    .collect();
                let sc = sc.clone();
                prop::sample::select(targets)
                    .prop_flat_map(move |(target, t)| {
                        expr::<V>(&t, &sc, d).prop_map(move |value| Expr::Set {
                            target: target.clone(),
                            value: bx(value),
                        })
                    })
                    .boxed()
            }));
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                (expr::<V>(&Ty::Bool, sc, d), expr::<V>(&Ty::Unit, sc, d))
                    .prop_map(|(cond, body)| Expr::While {
                        cond: bx(cond),
                        body: bx(body),
                    })
                    .boxed()
            }));
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                let sc = sc.clone();
                (
                    binder(),
                    expr::<V>(&Ty::Int, &sc, d),
                    expr::<V>(&Ty::Int, &sc, d),
                    prop_oneof![Just(ForDirection::To), Just(ForDirection::Downto)],
                )
                    .prop_flat_map(move |(var, from, to, direction)| {
                        let inner = Rc::new(sc.with([local(&var, Ty::Int)]));
                        expr::<V>(&Ty::Unit, &inner, d).prop_map(move |body| Expr::For {
                            var: var.clone(),
                            from: bx(from.clone()),
                            direction,
                            to: bx(to.clone()),
                            body: bx(body),
                        })
                    })
                    .boxed()
            }));
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                let sc = sc.clone();
                for_source::<V>(&sc, d)
                    .prop_flat_map(move |(source, elem)| {
                        let sc = sc.clone();
                        param::<V>(&elem, 1).prop_flat_map(move |(p, bound)| {
                            let inner = Rc::new(sc.with(vars(&bound)));
                            let source = source.clone();
                            expr::<V>(&Ty::Unit, &inner, d).prop_map(move |body| Expr::ForEach {
                                pat: p.clone(),
                                source: Box::new(source.clone()),
                                body: bx(body),
                            })
                        })
                    })
                    .boxed()
            }));
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                expr::<V>(&Ty::Bool, sc, d)
                    .prop_map(|e| Expr::Assert(bx(e)))
                    .boxed()
            }));
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                expr::<V>(&Ty::Unit, sc, d)
                    .prop_map(|e| Expr::Do(bx(e)))
                    .boxed()
            }));
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                let sc = sc.clone();
                arb_ty(1)
                    .prop_flat_map(move |t| expr::<V>(&t, &sc, d))
                    .prop_map(|e| Expr::App {
                        func: bx(name("ignore")),
                        arg: bx(e),
                    })
                    .boxed()
            }));
        }
        Ty::Str => {
            // `e.ToString ()`: a method called with no arguments.
            alts.push(rule(1, ty, sc, d, |_, sc, d| {
                expr::<V>(&Ty::Int, sc, d)
                    .prop_map(|e| Expr::App {
                        func: bx(Expr::FieldGet {
                            expr: bx(e),
                            field: ident("ToString"),
                        }),
                        arg: bx(Expr::Const(Const::Unit)),
                    })
                    .boxed()
            }));
            alts.push(rule(2, ty, sc, d, |_, sc, d| {
                // `a + b`, both annotated: with `null` on a side, `+`
                // resolves only once inference reaches the end, so it would
                // default to `int` (FS0071), and its type is unknown where a
                // list decides whether to yield it. (`^` is deprecated for
                // strings, FS0101.)
                let string = |e| Expr::Typed {
                    expr: bx(e),
                    ty: named("string"),
                };
                (expr::<V>(&Ty::Str, sc, d), expr::<V>(&Ty::Str, sc, d))
                    .prop_map(move |(l, r)| Expr::Infix {
                        op: infix("+"),
                        lhs: bx(string(l)),
                        rhs: bx(string(r)),
                    })
                    .boxed()
            }));
        }
        Ty::Obj => {
            alts.push(rule(2, ty, sc, d, |_, sc, d| {
                let sc = sc.clone();
                arb_ty(1)
                    .prop_flat_map(move |t| expr::<V>(&t, &sc, d))
                    .prop_map(|e| Expr::Upcast {
                        expr: bx(e),
                        ty: named("obj"),
                    })
                    .boxed()
            }));
            alts.push(rule(3, ty, sc, d, |_, sc, d| computation::<V>(sc, d)));
        }
        Ty::Record => {
            alts.push(rule(2, ty, sc, d, |_, sc, d| {
                (
                    prop::option::of(expr::<V>(&Ty::Record, sc, d)),
                    prop::sample::select(vec!["A", "R.A"]),
                    expr::<V>(&Ty::Int, sc, d),
                    expr::<V>(&Ty::Int, sc, d),
                    0..3usize,
                )
                    .prop_map(|(copy, a_label, x, y, shape)| {
                        let a = (path(a_label), x);
                        let c = (path("C"), y);
                        let fields = match (copy.is_some(), shape) {
                            (true, 0) => Vec1::new(a, Vec::new()),
                            (true, 1) => Vec1::new(c, Vec::new()),
                            (_, 2) => Vec1::new(c, vec![a]),
                            _ => Vec1::new(a, vec![c]),
                        };
                        Expr::Record {
                            copy: copy.map(bx),
                            fields,
                        }
                    })
                    .boxed()
            }));
        }
        Ty::List(t) | Ty::Array(t) => {
            let is_list = matches!(ty, Ty::List(_));
            let elem = (**t).clone();
            let (s, el) = (sc.clone(), elem.clone());
            alts.push((
                4,
                defer(move || list_body::<V>(&el, &s, d))
                    .prop_map(move |body| {
                        let body = Some(Box::new(body));
                        if is_list {
                            Expr::List(body)
                        } else {
                            Expr::Array(body)
                        }
                    })
                    .boxed(),
            ));
            if is_list {
                alts.push(rule(2, ty, sc, d, |ty, sc, d| {
                    let Ty::List(t) = ty else { unreachable!() };
                    prop_oneof![
                        (expr::<V>(t, sc, d), expr::<V>(ty, sc, d)).prop_map(|(h, tl)| {
                            Expr::Cons {
                                head: bx(h),
                                tail: bx(tl),
                            }
                        }),
                        (expr::<V>(ty, sc, d), expr::<V>(ty, sc, d)).prop_map(|(l, r)| {
                            Expr::Infix {
                                op: infix("@"),
                                lhs: bx(l),
                                rhs: bx(r),
                            }
                        }),
                    ]
                    .boxed()
                }));
            }
        }
        Ty::Seq(_) => {
            alts.push(rule(2, ty, sc, d, |ty, sc, d| {
                let Ty::Seq(t) = ty else { unreachable!() };
                let target = type_of(ty);
                expr::<V>(&Ty::list((**t).clone()), sc, d)
                    .prop_map(move |e| Expr::Upcast {
                        expr: bx(e),
                        ty: target.clone(),
                    })
                    .boxed()
            }));
        }
        Ty::Option(t) => {
            let t = (**t).clone();
            let s = sc.clone();
            alts.push((
                2,
                defer(move || expr::<V>(&t, &s, d))
                    .prop_map(|e| Expr::App {
                        func: bx(name("Some")),
                        arg: bx(e),
                    })
                    .boxed(),
            ));
        }
        Ty::Lazy(t) => {
            let t = (**t).clone();
            let s = Rc::new(sc.closure());
            alts.push((
                2,
                defer(move || expr::<V>(&t, &s, d))
                    .prop_map(|e| Expr::Lazy(bx(e)))
                    .boxed(),
            ));
        }
        Ty::Tuple(ts) => {
            let parts: Vec<_> = ts.iter().map(|t| expr::<V>(t, sc, d)).collect();
            alts.push((
                4,
                parts
                    .prop_map(|es| Expr::Tuple(Vec2::from_vec(es).expect("two")))
                    .boxed(),
            ));
        }
        Ty::Fun(a, b) => {
            alts.push(rule(4, ty, sc, d, |ty, sc, d| lambda::<V>(ty, sc, d)));
            let (a, b) = ((**a).clone(), (**b).clone());
            let inner = Rc::new(sc.closure());
            alts.push((
                2,
                defer(move || clauses::<V>(&a, &b, &inner, d))
                    .prop_map(Expr::Function)
                    .boxed(),
            ));
            if let Some(op) = op_value(ty) {
                alts.push((2, op.prop_map(Expr::OpValue).boxed()));
            }
            if *ty == Ty::fun(Ty::Str, Ty::Int)
                && let Some(gate) = V::AccessorFunctionShorthand::WITNESS
            {
                // Annotated, as `_.Length` needs its argument's type fixed.
                alts.push((
                    1,
                    Just(Expr::Typed {
                        expr: bx(Expr::DotLambda {
                            gate,
                            path: path("Length"),
                        }),
                        ty: type_of(ty),
                    })
                    .boxed(),
                ));
            }
        }
        Ty::Exn | Ty::Disposable | Ty::Builder => {}
    }
    weighted(alts)
}

fn infix(op: &str) -> InfixOperator {
    InfixOperator::new(Operator::new(op).expect("an operator")).expect("infix")
}

/// An operator value of the function type, if one has it.
fn op_value(ty: &Ty) -> Option<BoxedStrategy<Operator>> {
    let int_op = Ty::fun(Ty::Int, Ty::fun(Ty::Int, Ty::Int));
    let int_rel = Ty::fun(Ty::Int, Ty::fun(Ty::Int, Ty::Bool));
    let ops: Vec<&str> = if *ty == int_op {
        vec!["+", "-", "*", "/", "|||"]
    } else if *ty == int_rel {
        vec!["=", "<", "<>"]
    } else {
        return None;
    };
    Some(
        prop::sample::select(ops)
            .prop_map(|o| Operator::new(o).expect("an operator"))
            .boxed(),
    )
}

/// `fun p … -> e` of the function type, taking as many curried parameters as
/// it has (one or two).
fn lambda<V: Version>(ty: &Ty, sc: &Sc, d: u32) -> BoxedStrategy<Expr<V>> {
    let Ty::Fun(a, b) = ty else {
        unreachable!("a lambda of a function type")
    };
    let inner = sc.closure();
    let (a, b) = ((**a).clone(), (**b).clone());
    let two = match &b {
        Ty::Fun(b1, b2) => Some(((**b1).clone(), (**b2).clone())),
        _ => None,
    };
    let curried = two.is_some();
    (param::<V>(&a, 1), any::<bool>())
        .prop_flat_map(move |((p, bound), split)| {
            let sc = Rc::new(inner.with(vars(&bound)));
            match (&two, split && curried) {
                (Some((b1, b2)), true) => {
                    let b2 = b2.clone();
                    let p = p.clone();
                    let first = bound.clone();
                    param::<V>(b1, 1)
                        .prop_filter("a name bound twice", move |(_, qb)| {
                            distinct(&first.iter().chain(qb).cloned().collect())
                        })
                        .prop_flat_map(move |(q, qb)| {
                            let s = Rc::new(sc.with(vars(&qb)));
                            let p = p.clone();
                            expr::<V>(&b2, &s, d).prop_map(move |body| Expr::Lambda {
                                params: Vec1::new(p.clone(), vec![q.clone()]),
                                body: bx(body),
                            })
                        })
                        .boxed()
                }
                _ => {
                    let p = p.clone();
                    expr::<V>(&b, &sc, d)
                        .prop_map(move |body| Expr::Lambda {
                            params: Vec1::new(p.clone(), Vec::new()),
                            body: bx(body),
                        })
                        .boxed()
                }
            }
        })
        .boxed()
}

/// Match clauses over values of `scrutinee`, each giving `result`.
fn clauses<V: Version>(
    scrutinee: &Ty,
    result: &Ty,
    sc: &Sc,
    d: u32,
) -> BoxedStrategy<Vec1<MatchClause<V>>> {
    let (r, s) = (result.clone(), sc.clone());
    let clause = pat::<V>(scrutinee, 2, true).prop_flat_map(move |(p, bound)| {
        let inner = Rc::new(s.with(vars(&bound)));
        (
            prop::option::weighted(0.25, expr::<V>(&Ty::Bool, &inner, d)),
            expr::<V>(&r, &inner, d),
        )
            .prop_map(move |(guard, result)| MatchClause {
                pat: p.clone(),
                guard,
                result,
            })
    });
    // The first clause annotated, as a parameter is: its pattern fixes the
    // scrutinee's type before the clauses' bodies are read.
    let t = scrutinee.clone();
    prop::collection::vec(clause, 1..=2)
        .prop_map(move |cs| {
            let mut cs = Vec1::from_vec(cs).expect("non-empty").into_vec();
            if !matches!(cs[0].pat, Pat::Typed { .. }) {
                let p = std::mem::replace(&mut cs[0].pat, Pat::Wildcard);
                cs[0].pat = Pat::Typed {
                    pat: Box::new(p),
                    ty: type_of(&t),
                };
            }
            Vec1::from_vec(cs).expect("non-empty")
        })
        .boxed()
}

/// `with` clauses: over exceptions, each giving `result`.
fn exn_clauses<V: Version>(result: &Ty, sc: &Sc, d: u32) -> BoxedStrategy<Vec1<MatchClause<V>>> {
    clauses(&Ty::Exn, result, sc, d)
}

/// `Meth.F (…)`: a method with two parameters and an optional third, called
/// with an argument list, some of it by name, in any order.
fn method_call<V: Version>(sc: &Sc, d: u32) -> BoxedStrategy<Expr<V>> {
    let int = || expr::<V>(&Ty::Int, sc, d);
    prop_oneof![
        (int(), int(), prop::option::of(int())).prop_map(|(x, y, z)| Expr::MethodApp {
            func: bx(name("Meth.F")),
            args: Args::Positional(Vec2::new(x, y, z.into_iter().collect())),
        }),
        (0..=2usize, any::<bool>(), prop::collection::vec(int(), 3),)
            .prop_filter("no named argument", |(k, opt, _)| *k < 2 || *opt)
            .prop_flat_map(|(k, opt, values)| {
                let mut names: Vec<&str> = ["a", "b"][k..].to_vec();
                if opt {
                    names.push("c");
                }
                (Just(k), Just(values), Just(names).prop_shuffle())
            })
            .prop_map(|(k, values, names)| {
                let mut values = values.into_iter();
                let positional: Vec<Expr<V>> = values.by_ref().take(k).collect();
                let named: Vec<(Ident, Expr<V>)> =
                    names.into_iter().map(ident).zip(values).collect();
                Expr::MethodApp {
                    func: bx(name("Meth.F")),
                    args: Args::Named {
                        positional,
                        named: Vec1::from_vec(named).expect("non-empty"),
                    },
                }
            }),
        int().prop_map(|x| Expr::App {
            func: bx(name("Meth.G")),
            arg: bx(x),
        }),
        // `Meth.H ()`, the overload taking nothing; `Meth.H (())` would pass
        // `()` to the one taking `obj`, which returns a `string`.
        Just(Expr::App {
            func: bx(name("Meth.H")),
            arg: bx(Expr::Const(Const::Unit)),
        }),
    ]
    .boxed()
}

/// A `for … in` source, and the type of what it yields.
fn for_source<V: Version>(sc: &Sc, d: u32) -> BoxedStrategy<(ForSource<V>, Ty)> {
    let s = sc.clone();
    prop_oneof![
        3 => (arb_ty(1), 0..3u8).prop_flat_map(move |(t, kind)| {
            let coll = match kind {
                0 => Ty::list(t.clone()),
                1 => Ty::Array(Box::new(t.clone())),
                _ => Ty::Seq(Box::new(t.clone())),
            };
            (expr::<V>(&coll, &s, d).prop_map(ForSource::Expr), Just(t))
        }),
        1 => range::<V>(sc, d).prop_map(|r| (ForSource::Range(r), Ty::Int)),
    ]
    .boxed()
}

fn range<V: Version>(sc: &Sc, d: u32) -> BoxedStrategy<Range<V>> {
    let int = || expr::<V>(&Ty::Int, sc, d);
    (int(), prop::option::of(int()), int())
        .prop_map(|(from, step, to)| Range { from, step, to })
        .boxed()
}

/// A list's body of elements of `elem`: a literal's elements, a range of
/// `int`s, or a comprehension.
fn list_body<V: Version>(elem: &Ty, sc: &Sc, d: u32) -> BoxedStrategy<ListBody<V>> {
    let mut alts: Vec<(u32, BoxedStrategy<ListBody<V>>)> = vec![(
        2,
        prop::collection::vec(expr::<V>(elem, sc, d), 1..=3)
            .prop_map(|es| ListBody::Elements(Vec1::from_vec(es).expect("non-empty")))
            .boxed(),
    )];
    if *elem == Ty::Int {
        alts.push((1, range::<V>(sc, d).prop_map(ListBody::Range).boxed()));
    }
    let inner = Rc::new(sc.closure());
    alts.push((
        3,
        comp::<V, InCollection>(Some(elem.clone()), &inner, d)
            .prop_filter_map("a literal's elements, or refused", |c| {
                ListComp::new(c).ok()
            })
            .prop_map(ListBody::Comp)
            .boxed(),
    ));
    weighted(alts)
}

/// `builder { … }`.
fn computation<V: Version>(sc: &Sc, d: u32) -> BoxedStrategy<Expr<V>> {
    let inner = Rc::new(sc.closure());
    (
        prop_oneof![
            3 => expr::<V>(&Ty::Builder, sc, 0),
            1 => Just(Expr::App { func: bx(name("B")), arg: bx(Expr::Const(Const::Unit)) }),
        ],
        comp::<V, InBuilder>(None, &inner, d),
    )
        .prop_map(|(builder, body)| Expr::Computation {
            builder: bx(builder),
            body: Box::new(body),
        })
        .boxed()
}

/// A body's element type: a list's, or any type in a builder, whose `Yield`
/// takes `obj`.
type Elem = Option<Ty>;

fn elem_ty(elem: &Elem) -> BoxedStrategy<Ty> {
    match elem {
        Some(t) => Just(t.clone()).boxed(),
        None => arb_ty(1),
    }
}

/// A computation expression's body in context `K`, of elements of `elem`.
/// Whether it may yield is drawn first: a body with no `yield` anywhere
/// yields its expression statements from F# 4.7 (implicit yields), so they
/// may have the element's type; a body with a `yield` executes them, so they
/// are `unit`.
pub fn comp<V: Version, K: Context>(elem: Elem, sc: &Sc, d: u32) -> BoxedStrategy<Comp<V, K>> {
    let sc = sc.clone();
    let implicit = match V::ImplicitYield::WITNESS {
        Some(_) => any::<bool>().boxed(),
        None => Just(false).boxed(),
    };
    implicit
        .prop_flat_map(move |implicit| body::<V, K>(elem.clone(), implicit, &sc, d))
        .boxed()
}

/// A body: up to two items, each in the scope of the ones before, then a
/// statement.
fn body<V: Version, K: Context>(
    elem: Elem,
    implicit: bool,
    sc: &Sc,
    d: u32,
) -> BoxedStrategy<Comp<V, K>> {
    let sc = sc.clone();
    (0..=2u32)
        .prop_flat_map(move |n| items::<V, K>(n, elem.clone(), implicit, &sc, d))
        .boxed()
}

fn items<V: Version, K: Context>(
    n: u32,
    elem: Elem,
    implicit: bool,
    sc: &Sc,
    d: u32,
) -> BoxedStrategy<Comp<V, K>> {
    if n == 0 {
        return stmt::<V, K>(elem, implicit, sc, d)
            .prop_map(Comp::stmt)
            .boxed();
    }
    let e = elem.clone();
    item::<V, K>(elem, implicit, sc, d)
        .prop_flat_map(move |(item, scope)| {
            let s = Rc::new(scope);
            items::<V, K>(n - 1, e.clone(), implicit, &s, d).prop_map(move |rest| {
                let mut init = vec![item.clone()];
                init.extend(rest.init);
                Comp {
                    init,
                    last: rest.last,
                }
            })
        })
        .boxed()
}

/// One item of a body, and the scope after it.
fn item<V: Version, K: Context>(
    elem: Elem,
    implicit: bool,
    sc: &Sc,
    d: u32,
) -> BoxedStrategy<(CompItem<V, K>, Scope)> {
    let mut alts: Alts<(CompItem<V, K>, Scope)> = Vec::new();
    {
        let s = sc.clone();
        let e = elem.clone();
        alts.push((
            4,
            defer(move || {
                let s2 = s.clone();
                stmt::<V, K>(e.clone(), implicit, &s, d)
                    .prop_map(move |st| (CompItem::Stmt(st), (*s2).clone()))
                    .boxed()
            }),
        ));
    }
    {
        let s = sc.clone();
        alts.push((
            2,
            defer(move || {
                let s2 = s.clone();
                bindings::<V>(&s, d, false)
                    .prop_filter_map("F# refuses the group locally", |(b, bound)| {
                        LocalBindings::new(b).ok().map(|b| (b, bound))
                    })
                    .prop_map(move |(b, bound)| {
                        // A body's later statements are closures, which a
                        // local `mutable` cannot be captured by.
                        (CompItem::Let(b), s2.with(bound).closure())
                    })
                    .boxed()
            }),
        ));
    }
    {
        let s = sc.clone();
        alts.push((
            1,
            defer(move || {
                let s2 = s.clone();
                (
                    use_name::<borzoi_print::version::Available>(),
                    expr::<V>(&Ty::Disposable, &s, d),
                )
                    .prop_map(move |(name, value)| {
                        let scope = bind_use(&s2, &name);
                        (CompItem::Use(UseBinding { name, value }), scope)
                    })
                    .boxed()
            }),
        ));
    }
    if let Some(gate) = K::Bang::WITNESS {
        let s = sc.clone();
        alts.push((
            2,
            defer(move || {
                let s = s.clone();
                (arb_ty(1), ands_types::<V>())
                    .prop_flat_map(move |(t, ats)| {
                        let mut parts = vec![(param::<V>(&t, 1), expr::<V>(&t, &s, d))];
                        for at in &ats {
                            parts.push((param::<V>(at, 1), expr::<V>(at, &s, d)));
                        }
                        let s = s.clone();
                        parts.prop_filter_map("a name bound twice", move |parts| {
                            let bound: Bound =
                                parts.iter().flat_map(|((_, b), _)| b.clone()).collect();
                            if !distinct(&bound) {
                                return None;
                            }
                            let mut it = parts.into_iter();
                            let ((pat, _), value) = it.next().expect("a binding");
                            let ands = it
                                .map(|((pat, _), value)| AndBang {
                                    gate: V::AndBang::WITNESS.expect("drawn only where gated"),
                                    pat,
                                    value,
                                })
                                .collect();
                            Some((
                                CompItem::LetBang(LetBang {
                                    gate,
                                    pat,
                                    value,
                                    ands,
                                }),
                                s.with(vars(&bound)),
                            ))
                        })
                    })
                    .boxed()
            }),
        ));
        let s = sc.clone();
        alts.push((
            1,
            defer(move || {
                let s2 = s.clone();
                (
                    use_name::<V::UseBangBindingValueDiscard>(),
                    expr::<V>(&Ty::Disposable, &s, d),
                )
                    .prop_map(move |(name, value)| {
                        let scope = bind_use(&s2, &name);
                        (CompItem::UseBang(UseBang { gate, name, value }), scope)
                    })
                    .boxed()
            }),
        ));
    }
    weighted(alts)
}

fn ands_types<V: Version>() -> BoxedStrategy<Vec<Ty>> {
    match V::AndBang::WITNESS {
        Some(_) => prop::collection::vec(arb_ty(1), 0..=2).boxed(),
        None => Just(Vec::new()).boxed(),
    }
}

fn bind_use<G: Gate>(sc: &Scope, name: &UseName<G>) -> Scope {
    match name {
        UseName::Named(ValueName::Ident(n)) => sc.with([local(n, Ty::Disposable)]),
        _ => sc.clone(),
    }
}

fn use_name<G: Gate>() -> BoxedStrategy<UseName<G>> {
    let named = binder().prop_map(|n| UseName::Named(ValueName::Ident(n)));
    match G::WITNESS {
        Some(gate) => prop_oneof![3 => named, 1 => Just(UseName::Discard(gate))].boxed(),
        None => named.boxed(),
    }
}

/// A statement of a body of `elem`s.
fn stmt<V: Version, K: Context>(
    elem: Elem,
    implicit: bool,
    sc: &Sc,
    d: u32,
) -> BoxedStrategy<Stmt<V, K>> {
    let s = sc.clone();
    let mut alts: Vec<(u32, BoxedStrategy<Stmt<V, K>>)> = Vec::new();
    {
        let (s, e) = (s.clone(), elem.clone());
        alts.push((
            4,
            defer(move || {
                let s = s.clone();
                let ty = if implicit {
                    prop_oneof![elem_ty(&e), Just(Ty::Unit)].boxed()
                } else {
                    Just(Ty::Unit).boxed()
                };
                ty.prop_flat_map(move |t| expr::<V>(&t, &s, d))
                    .prop_filter_map("F# reads it as another statement", |e| {
                        StmtExpr::new(e).ok()
                    })
                    .prop_map(Stmt::Expr)
                    .boxed()
            }),
        ));
    }
    if !implicit {
        let (s1, e1) = (s.clone(), elem.clone());
        alts.push((
            3,
            defer(move || {
                let s = s1.clone();
                elem_ty(&e1)
                    .prop_flat_map(move |t| expr::<V>(&t, &s, d))
                    .prop_map(Stmt::Yield)
                    .boxed()
            }),
        ));
        let (s2, e2) = (s.clone(), elem.clone());
        alts.push((
            1,
            defer(move || {
                let s = s2.clone();
                let builder = e2.is_none();
                (elem_ty(&e2), 0..3u8)
                    .prop_flat_map(move |(t, kind)| {
                        let source = match (builder, kind) {
                            (true, _) => t,
                            (false, 0) => Ty::list(t),
                            (false, 1) => Ty::Array(Box::new(t)),
                            (false, _) => Ty::Seq(Box::new(t)),
                        };
                        expr::<V>(&source, &s, d)
                    })
                    .prop_map(Stmt::YieldFrom)
                    .boxed()
            }),
        ));
    }
    if let Some(gate) = K::Bang::WITNESS {
        let s1 = s.clone();
        alts.push((
            1,
            defer(move || {
                expr::<V>(&Ty::Unit, &s1, d)
                    .prop_map(move |expr| Stmt::DoBang { gate, expr })
                    .boxed()
            }),
        ));
        let s2 = s.clone();
        alts.push((
            2,
            defer(move || {
                let s = s2.clone();
                (arb_ty(1), any::<bool>())
                    .prop_flat_map(move |(t, from)| (expr::<V>(&t, &s, d), Just(from)))
                    .prop_map(move |(expr, from)| {
                        if from {
                            Stmt::ReturnFrom { gate, expr }
                        } else {
                            Stmt::Return { gate, expr }
                        }
                    })
                    .boxed()
            }),
        ));
    }
    if d > 0 {
        let d = d - 1;
        let sub = {
            let e = elem.clone();
            move |sc: &Scope| body::<V, K>(e.clone(), implicit, &Rc::new(sc.clone()), d)
        };
        {
            let (s, sub) = (s.clone(), sub.clone());
            alts.push((
                2,
                defer(move || {
                    (
                        expr::<V>(&Ty::Bool, &s, d),
                        sub(&s),
                        prop::option::of(sub(&s)),
                    )
                        .prop_map(|(cond, then_branch, else_branch)| Stmt::IfThenElse {
                            cond,
                            then_branch: Box::new(then_branch),
                            else_branch: else_branch.map(Box::new),
                        })
                        .boxed()
                }),
            ));
        }
        {
            let (s, sub) = (s.clone(), sub.clone());
            alts.push((
                1,
                defer(move || {
                    let (s, sub) = (s.clone(), sub.clone());
                    arb_ty(1)
                        .prop_flat_map(move |t| {
                            (
                                expr::<V>(&t, &s, d),
                                comp_clauses::<V, K>(&t, &s, sub.clone()),
                                Just(()),
                            )
                        })
                        .prop_map(|(scrutinee, clauses, ())| Stmt::Match { scrutinee, clauses })
                        .boxed()
                }),
            ));
        }
        if let Some(gate) = K::Bang::WITNESS {
            let (s1, sub1) = (s.clone(), sub.clone());
            alts.push((
                1,
                defer(move || {
                    let (s, sub) = (s1.clone(), sub1.clone());
                    arb_ty(1)
                        .prop_flat_map(move |t| {
                            (
                                expr::<V>(&t, &s, d),
                                comp_clauses::<V, K>(&t, &s, sub.clone()),
                            )
                        })
                        .prop_map(move |(scrutinee, clauses)| Stmt::MatchBang {
                            gate,
                            scrutinee,
                            clauses,
                        })
                        .boxed()
                }),
            ));
            if let Some(while_bang) = V::WhileBang::WITNESS {
                let (s, sub) = (s.clone(), sub.clone());
                alts.push((
                    1,
                    defer(move || {
                        (expr::<V>(&Ty::Bool, &s, d), sub(&s))
                            .prop_map(move |(cond, body)| Stmt::WhileBang {
                                gate: while_bang,
                                bang: gate,
                                cond,
                                body: Box::new(body),
                            })
                            .boxed()
                    }),
                ));
            }
        }
        {
            let (s, sub) = (s.clone(), sub.clone());
            alts.push((
                1,
                defer(move || {
                    (expr::<V>(&Ty::Bool, &s, d), sub(&s))
                        .prop_map(|(cond, body)| Stmt::While {
                            cond,
                            body: Box::new(body),
                        })
                        .boxed()
                }),
            ));
        }
        {
            let (s, sub) = (s.clone(), sub.clone());
            alts.push((
                1,
                defer(move || {
                    let (s, sub) = (s.clone(), sub.clone());
                    (
                        binder(),
                        expr::<V>(&Ty::Int, &s, d),
                        expr::<V>(&Ty::Int, &s, d),
                        prop_oneof![Just(ForDirection::To), Just(ForDirection::Downto)],
                    )
                        .prop_flat_map(move |(var, from, to, direction)| {
                            sub(&s.with([local(&var, Ty::Int)])).prop_map(move |body| Stmt::For {
                                var: var.clone(),
                                from: from.clone(),
                                direction,
                                to: to.clone(),
                                body: Box::new(body),
                            })
                        })
                        .boxed()
                }),
            ));
        }
        {
            let (s, sub) = (s.clone(), sub.clone());
            alts.push((
                2,
                defer(move || {
                    let (s, sub) = (s.clone(), sub.clone());
                    for_source::<V>(&s, d)
                        .prop_flat_map(move |(source, t)| {
                            let (s, sub) = (s.clone(), sub.clone());
                            param::<V>(&t, 1).prop_flat_map(move |(pat, bound)| {
                                let source = source.clone();
                                sub(&s.with(vars(&bound))).prop_map(move |body| Stmt::ForEach {
                                    pat: pat.clone(),
                                    source: source.clone(),
                                    body: Box::new(body),
                                })
                            })
                        })
                        .boxed()
                }),
            ));
        }
        if let Some(gate) = K::TryWith::<V>::WITNESS {
            let (s, sub) = (s.clone(), sub.clone());
            alts.push((
                1,
                defer(move || {
                    (sub(&s), comp_clauses::<V, K>(&Ty::Exn, &s, sub.clone()))
                        .prop_map(move |(body, clauses)| Stmt::TryWith {
                            gate,
                            body: Box::new(body),
                            clauses,
                        })
                        .boxed()
                }),
            ));
        }
        {
            let (s, sub) = (s.clone(), sub.clone());
            alts.push((
                1,
                defer(move || {
                    (sub(&s), expr::<V>(&Ty::Unit, &s, d))
                        .prop_map(|(body, finally)| Stmt::TryFinally {
                            body: Box::new(body),
                            finally,
                        })
                        .boxed()
                }),
            ));
        }
    }
    weighted(alts)
}

fn comp_clauses<V: Version, K: Context>(
    scrutinee: &Ty,
    sc: &Sc,
    sub: impl Fn(&Scope) -> BoxedStrategy<Comp<V, K>> + Clone + 'static,
) -> BoxedStrategy<Vec1<CompClause<V, K>>> {
    let s = sc.clone();
    let t = scrutinee.clone();
    let clause = pat::<V>(scrutinee, 2, true).prop_flat_map(move |(p, bound)| {
        let inner = s.with(vars(&bound));
        let guard_scope = Rc::new(inner.clone());
        (
            prop::option::weighted(0.25, expr::<V>(&Ty::Bool, &guard_scope, 0)),
            sub(&inner),
        )
            .prop_map(move |(guard, body)| CompClause {
                pat: p.clone(),
                guard,
                body,
            })
    });
    prop::collection::vec(clause, 1..=2)
        .prop_map(move |mut cs| {
            // The first clause annotated, as in `clauses`.
            if !matches!(cs[0].pat, Pat::Typed { .. }) {
                let p = std::mem::replace(&mut cs[0].pat, Pat::Wildcard);
                cs[0].pat = Pat::Typed {
                    pat: Box::new(p),
                    ty: type_of(&t),
                };
            }
            Vec1::from_vec(cs).expect("non-empty")
        })
        .boxed()
}

/// Attributes: the prelude's `A`, and `B` with an `int` argument.
fn attributes<V: Version>() -> BoxedStrategy<Vec<Attribute<V>>> {
    let attribute = prop_oneof![
        Just(Attribute {
            name: path("A"),
            args: AttributeArgs::Value(Expr::Const(Const::Unit)),
        }),
        Just(Attribute {
            name: path("AAttribute"),
            args: AttributeArgs::Value(Expr::Const(Const::Unit)),
        }),
        int_const::<V>().prop_map(|n| Attribute {
            name: path("B"),
            args: AttributeArgs::Value(n),
        }),
    ];
    prop_oneof![
        3 => Just(Vec::new()),
        1 => prop::collection::vec(attribute, 1..=2),
    ]
    .boxed()
}

/// A `let` group, and what it binds. At module level (`module_level`) a
/// binding that is not a function has its value annotated, as F# does not
/// generalise a value whose type it leaves open there.
pub fn bindings<V: Version>(
    sc: &Sc,
    d: u32,
    module_level: bool,
) -> BoxedStrategy<(LetBindings<V>, Vec<Var>)> {
    let s = sc.clone();
    let one = move || binding::<V>(&s, d, module_level);
    let outer = sc.clone();
    prop_oneof![
        3 => one().prop_map(|(b, vs)| (LetBindings::NonRec(Box::new(b)), vs)),
        // A recursive group's names are in scope in each of its bodies, which
        // were drawn without them, so none may name a value those bodies see.
        1 => prop::collection::vec(one(), 1..=2)
            .prop_map(|bs| {
                let (bs, vs): (Vec<_>, Vec<_>) = bs.into_iter().unzip();
                (LetBindings::Rec(Vec1::from_vec(bs).expect("non-empty")), vs.concat())
            })
            .prop_filter("a recursive name the bodies see", move |(_, vs)| {
                !vs.iter().any(|v| outer.vars.iter().any(|w| w.path == v.path))
            }),
    ]
    .prop_filter("a name bound twice", |(_, vs)| {
        let names: BTreeSet<Vec<&str>> = vs
            .iter()
            .map(|v| v.path.segments().iter().map(Ident::as_str).collect())
            .collect();
        names.len() == vs.len()
    })
    .boxed()
}

/// One binding, and what it binds.
fn binding<V: Version>(
    sc: &Sc,
    d: u32,
    module_level: bool,
) -> BoxedStrategy<(Binding<V>, Vec<Var>)> {
    let head_and_body = move |s: Sc| -> BoxedStrategy<(BindingHead<V>, Expr<V>, Vec<Var>)> {
        prop_oneof![
        // `let [mutable] [access] x = e`
        2 => (arb_ty(1), any::<bool>(), access(), binder()).prop_flat_map({
            let s = s.clone();
            move |(t, is_mutable, access, name)| {
                let var = Var {
                    path: LongIdent::single(name.clone()),
                    ty: t.clone(),
                    local_mutable: is_mutable && !module_level,
                    mutable: is_mutable,
                    private: access == Some(Access::Private),
                    restricted: restricted(access),
                };
                value::<V>(&t, &s, d, module_level).prop_map(move |body| {
                    (
                        BindingHead::Name {
                            is_mutable,
                            access,
                            name: ValueName::Ident(name.clone()),
                        },
                        body,
                        vec![var.clone()],
                    )
                })
            }
        }),
        // `let [access] f p q = e`
        2 => (prop::collection::vec(arb_ty(1), 1..=2), arb_ty(1), access(), binder())
            .prop_flat_map({
                let s = s.clone();
                move |(params, ret, access, name)| {
                    let parts: Vec<_> = params.iter().map(|t| param::<V>(t, 1)).collect();
                    let parts = parts.prop_filter("a name bound twice", |ps| {
                        distinct(&ps.iter().flat_map(|(_, b)| b.clone()).collect())
                    });
                    let s = s.clone();
                    let fty = params
                        .iter()
                        .rev()
                        .fold(ret.clone(), |acc, p| Ty::fun(p.clone(), acc));
                    let ret = ret.clone();
                    parts.prop_flat_map(move |ps| {
                        let bound: Bound = ps.iter().flat_map(|(_, b)| b.clone()).collect();
                        let inner = Rc::new(s.closure().with(vars(&bound)));
                        let pats: Vec<Pat<V>> = ps.iter().map(|(p, _)| p.clone()).collect();
                        let var = Var {
                            private: access == Some(Access::Private),
                            restricted: restricted(access),
                            ..local(&name, fty.clone())
                        };
                        let name = name.clone();
                        expr::<V>(&ret, &inner, d)
                            .prop_map(move |body| {
                                (
                                    BindingHead::Function {
                                        access,
                                        name: ValueName::Ident(name.clone()),
                                        params: Vec1::from_vec(pats.clone()).expect("non-empty"),
                                    },
                                    body,
                                    vec![var.clone()],
                                )
                            })
                    })
                }
            }),
        // `let _ = e`
        1 => arb_ty(1).prop_flat_map({
            let s = s.clone();
            move |t| {
                value::<V>(&t, &s, d, module_level)
                    .prop_map(|body| (BindingHead::Pattern(Pat::Wildcard), body, Vec::new()))
            }
        }),
        // `let (p) = e`
        1 => arb_ty(1).prop_flat_map({
            let s = s.clone();
            move |t| {
                let s = s.clone();
                // Annotated like a parameter: older checkers read the
                // pattern before the value (FS0008).
                (param::<V>(&t, 2), Just(t)).prop_flat_map(move |((p, bound), t)| {
                    let vs = vars(&bound);
                    value::<V>(&t, &s, d, module_level)
                        .prop_map(move |body| (BindingHead::Pattern(p.clone()), body, vs.clone()))
                })
            }
        }),
    ]
        .boxed()
    };
    let s = sc.clone();
    (attributes::<V>(), any::<bool>())
        .prop_flat_map(move |(attributes, is_inline)| {
            // An inline body may use only what is as accessible as it.
            let scope = if is_inline {
                Rc::new(Scope {
                    vars: s.vars.iter().filter(|v| !v.restricted).cloned().collect(),
                    modules: s.modules.clone(),
                })
            } else {
                s.clone()
            };
            head_and_body(scope).prop_map(move |(head, body, vs)| {
                (
                    Binding {
                        attributes: attributes.clone(),
                        is_inline,
                        head,
                        body,
                    },
                    vs,
                )
            })
        })
        .boxed()
}

/// Whether `access` makes a value less accessible than public.
fn restricted(access: Option<Access>) -> bool {
    matches!(access, Some(Access::Private | Access::Internal))
}

/// A binding's value of `ty`, annotated at module level.
fn value<V: Version>(ty: &Ty, sc: &Sc, d: u32, module_level: bool) -> BoxedStrategy<Expr<V>> {
    let t = type_of(ty);
    expr::<V>(ty, sc, d)
        .prop_map(move |e| {
            if module_level {
                Expr::Typed {
                    expr: bx(e),
                    ty: t.clone(),
                }
            } else {
                e
            }
        })
        .boxed()
}

/// The names a module has declared in the type namespace.
type Declared = Rc<BTreeSet<String>>;

/// Up to `n` declarations, each in the scope of the ones before, none
/// redeclaring a name.
fn decls<V: Version>(
    n: u32,
    sc: &Sc,
    declared: &Declared,
    depth: u32,
) -> BoxedStrategy<(Vec<ModuleDecl<V>>, Scope, Vec<Var>)> {
    if n == 0 {
        return Just((Vec::new(), (**sc).clone(), Vec::new())).boxed();
    }
    let declared = declared.clone();
    decl::<V>(sc, &declared, depth)
        .prop_flat_map(move |(decl, scope, names, values)| {
            let mut all = (*declared).clone();
            all.extend(names);
            let d = Rc::new(all);
            decls::<V>(n - 1, &Rc::new(scope), &d, depth).prop_map(
                move |(mut rest, scope, mut later)| {
                    rest.insert(0, decl.clone());
                    let mut values = values.clone();
                    values.append(&mut later);
                    (rest, scope, values)
                },
            )
        })
        .boxed()
}

/// What one declaration draws: it, the scope after it, the type-namespace
/// names it declares, and the values it declares, by their paths from the
/// module it sits in.
type DeclDraw<V> = (ModuleDecl<V>, Scope, Vec<String>, Vec<Var>);

/// A declaration, the scope after it, and the type-namespace names and the
/// values it declares.
fn decl<V: Version>(sc: &Sc, declared: &Declared, depth: u32) -> BoxedStrategy<DeclDraw<V>> {
    let fresh = {
        let declared = declared.clone();
        move || {
            let declared = declared.clone();
            type_name().prop_filter("declared already", move |n| !declared.contains(n.as_str()))
        }
    };
    let s = sc.clone();
    let mut alts: Alts<DeclDraw<V>> = Vec::new();
    {
        let s = s.clone();
        let declared = declared.clone();
        alts.push((
            4,
            defer(move || {
                let s2 = s.clone();
                let declared = declared.clone();
                bindings::<V>(&s, 3, true)
                    .prop_filter_map("a module's value declared twice", move |(b, bound)| {
                        let names: Vec<String> = bound
                            .iter()
                            .map(|v| format!("value {}", v.path.segments()[0].as_str()))
                            .collect();
                        if names.iter().any(|n| declared.contains(n)) {
                            return None;
                        }
                        let group = ModuleBindings::new(b).ok()?;
                        Some((ModuleDecl::Let(group), s2.with(bound.clone()), names, bound))
                    })
                    .boxed()
            }),
        ));
    }
    {
        let s = s.clone();
        alts.push((
            2,
            defer(move || {
                let s2 = s.clone();
                expr::<V>(&Ty::Unit, &s, 3)
                    .prop_map(move |e| (ModuleDecl::Expr(e), (*s2).clone(), Vec::new(), Vec::new()))
                    .boxed()
            }),
        ));
    }
    {
        let s = s.clone();
        let mut targets = vec![path("System")];
        targets.extend(s.modules.iter().map(|m| LongIdent::single(m.clone())));
        alts.push((
            1,
            prop::sample::select(targets)
                .prop_map(move |m| {
                    // A module's values, by their bare names, which shadow
                    // what had them; not the module's own to export.
                    let opened: Vec<Var> = s
                        .vars
                        .iter()
                        .filter_map(|v| match v.path.segments() {
                            [head, rest @ ..]
                                if !rest.is_empty() && m.segments() == [head.clone()] =>
                            {
                                Some(Var {
                                    path: LongIdent(
                                        Vec1::from_vec(rest.to_vec()).expect("non-empty"),
                                    ),
                                    private: true,
                                    ..v.clone()
                                })
                            }
                            _ => None,
                        })
                        .collect();
                    (ModuleDecl::Open(m), s.with(opened), Vec::new(), Vec::new())
                })
                .boxed(),
        ));
    }
    if !sc.modules.is_empty() {
        let s = sc.clone();
        let fresh = fresh.clone();
        alts.push((
            1,
            defer(move || {
                let s = s.clone();
                // Not a name in scope: an abbreviation would shadow its
                // paths, which the scope does not follow.
                let taken = s.clone();
                let name = fresh().prop_filter("a name in scope", move |n| !taken.names(n));
                (name, prop::sample::select(s.modules.clone()))
                    .prop_map(move |(name, target)| {
                        (
                            ModuleDecl::ModuleAbbrev {
                                name: name.clone(),
                                target: LongIdent::single(target),
                            },
                            (*s).clone(),
                            vec![name.as_str().to_owned()],
                            Vec::new(),
                        )
                    })
                    .boxed()
            }),
        ));
    }
    if depth > 0 {
        let s = sc.clone();
        let fresh = fresh.clone();
        alts.push((
            2,
            defer(move || {
                let s = s.clone();
                (
                    attributes::<V>(),
                    access(),
                    any::<bool>(),
                    fresh().prop_filter_map("not an entity's name", |n| EntityName::new(n).ok()),
                    0..=3u32,
                )
                    .prop_flat_map(move |(attributes, access, is_rec, entity, n)| {
                        let name = entity.ident().clone();
                        let s = s.clone();
                        let inner = Rc::new(Scope {
                            vars: s.vars.clone(),
                            modules: s.modules.clone(),
                        });
                        decls::<V>(n, &inner, &Rc::new(BTreeSet::new()), depth - 1).prop_filter_map(
                            "F# refuses the module",
                            move |(decls, _, values)| {
                                // The module's own values, by their path from
                                // outside it; a private one is not visible.
                                let exported: Vec<Var> = values
                                    .iter()
                                    .filter(|v| !v.private)
                                    .map(|v| Var {
                                        path: LongIdent(Vec1::new(
                                            name.clone(),
                                            v.path.segments().to_vec(),
                                        )),
                                        restricted: v.restricted || restricted(access),
                                        ..v.clone()
                                    })
                                    .collect();
                                // Behind a value of the module's name, F# reads
                                // `N.x` as a member of the value.
                                let exported =
                                    if s.vars.iter().any(|v| v.path.segments() == [name.clone()]) {
                                        Vec::new()
                                    } else {
                                        exported
                                    };
                                let exported_values = exported.clone();
                                let mut scope = s.with(exported);
                                scope.modules.push(name.clone());
                                let body = if is_rec {
                                    if !fresh_group(&decls, &s) {
                                        return None;
                                    }
                                    ModuleBody::Rec(RecDecls::new(decls).ok()?)
                                } else {
                                    ModuleBody::NonRec(decls)
                                };
                                Some((
                                    ModuleDecl::NestedModule(NestedModule {
                                        attributes: attributes.clone(),
                                        access,
                                        name: entity.clone(),
                                        body,
                                    }),
                                    scope,
                                    vec![name.as_str().to_owned()],
                                    exported_values.clone(),
                                ))
                            },
                        )
                    })
                    .boxed()
            }),
        ));
    }
    {
        let s = sc.clone();
        let fresh = fresh.clone();
        alts.push((
            2,
            defer(move || {
                let s = s.clone();
                prop::collection::vec((fresh(), type_defn::<V>()), 1..=2)
                    .prop_filter("a type declared twice", |ds| {
                        let names: BTreeSet<&str> = ds.iter().map(|(n, _)| n.as_str()).collect();
                        names.len() == ds.len()
                    })
                    .prop_filter_map("F# refuses a definition", move |ds| {
                        let names = ds.iter().map(|(n, _)| n.as_str().to_owned()).collect();
                        let defs = ds
                            .into_iter()
                            .map(|(name, (attributes, access, typars, repr))| {
                                let name = EntityName::new(name).ok()?;
                                TypeDefn::new(attributes, access, name, typars, repr).ok()
                            })
                            .collect::<Option<Vec<_>>>()?;
                        Some((
                            ModuleDecl::Types(Vec1::from_vec(defs).expect("non-empty")),
                            (*s).clone(),
                            names,
                            Vec::new(),
                        ))
                    })
                    .boxed()
            }),
        ));
    }
    {
        let s = sc.clone();
        alts.push((
            1,
            defer(move || {
                let s = s.clone();
                (
                    fresh(),
                    prop::collection::vec(union_field(Vec::new()), 0..=2),
                )
                    .prop_filter_map("F# refuses the exception", move |(name, fields)| {
                        let names = vec![name.as_str().to_owned()];
                        let exn =
                            ExceptionDefn::new(ExceptionName::new(name).ok()?, fields).ok()?;
                        Some((ModuleDecl::Exception(exn), (*s).clone(), names, Vec::new()))
                    })
                    .boxed()
            }),
        ));
    }
    weighted(alts)
}

/// Whether `decls`, as a recursive group in scope `sc`, keep the meaning the
/// generator drew them with. Its scope runs in order, but a recursive group's
/// every value and module is in scope throughout it, its own definition
/// included; so none may name a value or module of `sc`, nor share a name
/// with another, at any of the group's levels.
fn fresh_group<V: Version>(decls: &[ModuleDecl<V>], sc: &Scope) -> bool {
    fn names<V: Version>(
        decls: &[ModuleDecl<V>],
        values: &mut Vec<String>,
        modules: &mut Vec<String>,
    ) {
        for d in decls {
            match d {
                ModuleDecl::Let(group) => {
                    for b in group.bindings().as_slice() {
                        match &b.head {
                            BindingHead::Name { name, .. } | BindingHead::Function { name, .. } => {
                                if let ValueName::Ident(i) = name {
                                    values.push(i.as_str().to_owned());
                                }
                            }
                            BindingHead::Pattern(p) => pat_names(p, values),
                        }
                    }
                }
                ModuleDecl::NestedModule(m) => {
                    modules.push(m.name.as_str().to_owned());
                    names(m.body.decls(), values, modules);
                }
                ModuleDecl::ModuleAbbrev { name, .. } => modules.push(name.as_str().to_owned()),
                _ => {}
            }
        }
    }
    let (mut values, mut modules) = (Vec::new(), Vec::new());
    names(decls, &mut values, &mut modules);
    let distinct = |xs: &[String]| xs.iter().collect::<BTreeSet<_>>().len() == xs.len();
    distinct(&values)
        && distinct(&modules)
        && !values.iter().any(|v| {
            sc.vars
                .iter()
                .any(|w| matches!(w.path.segments(), [only] if only.as_str() == v))
        })
        && !modules
            .iter()
            .any(|m| sc.modules.iter().any(|n| n.as_str() == m))
}

/// Push the names `p` binds onto `out`.
fn pat_names<V: Version>(p: &Pat<V>, out: &mut Vec<String>) {
    match p {
        Pat::Name(n) => {
            if let [only] = n.segments()
                && only.as_str() != "None"
            {
                out.push(only.as_str().to_owned());
            }
        }
        Pat::Ctor { args, .. } => args.as_slice().iter().for_each(|a| pat_names(a, out)),
        Pat::Tuple(ps) | Pat::Ands(ps) => ps.as_slice().iter().for_each(|a| pat_names(a, out)),
        Pat::List(ps) | Pat::Array(ps) => ps.iter().for_each(|a| pat_names(a, out)),
        Pat::Cons { head, tail } => {
            pat_names(head, out);
            pat_names(tail, out);
        }
        Pat::Typed { pat, .. } => pat_names(pat, out),
        Pat::As { pat, alias } => {
            pat_names(pat, out);
            match alias {
                AsAlias::Var(v) => out.push(v.as_str().to_owned()),
                AsAlias::Pat(a) => pat_names(a.pat(), out),
            }
        }
        Pat::Record(fs) => fs.as_slice().iter().for_each(|(_, p)| pat_names(p, out)),
        Pat::Or(l, _) => pat_names(l, out),
        Pat::Wildcard | Pat::Const(_) | Pat::Null | Pat::IsInst(_) => {}
    }
}

/// A field type: a drawn type, or one of `typars`.
fn field_type(typars: Vec<borzoi_print::names::TyparName>) -> BoxedStrategy<Type> {
    let drawn = arb_ty(1).prop_map(|t| type_of(&t));
    // What a declaration refuses: `_`, alone or in a type (FS0715), and a
    // type parameter it does not declare, `'c` (FS0039).
    let undeclared = borzoi_print::names::TyparName::new("c").expect("a type variable");
    let refused = prop_oneof![
        Just(Type::Anon),
        Just(app("list", Type::Anon)),
        Just(Type::Var(undeclared)),
    ];
    if typars.is_empty() {
        prop_oneof![8 => drawn, 1 => refused].boxed()
    } else {
        prop_oneof![
            8 => drawn,
            4 => prop::sample::select(typars).prop_map(Type::Var),
            1 => refused,
        ]
        .boxed()
    }
}

fn union_field(typars: Vec<borzoi_print::names::TyparName>) -> BoxedStrategy<UnionField> {
    (prop::option::of(binder()), field_type(typars))
        .prop_map(|(name, ty)| UnionField { name, ty })
        .boxed()
}

/// A type definition's attributes, access, type parameters and
/// representation, for [`TypeDefn::new`] with a name.
type DefnParts<V> = (
    Vec<Attribute<V>>,
    Option<Access>,
    Vec<borzoi_print::names::TyparName>,
    TypeRepr,
);

/// A type definition but its name.
fn type_defn<V: Version>() -> BoxedStrategy<DefnParts<V>> {
    let typars =
        prop::collection::vec(prop::sample::select(vec!["a", "b"]), 0..=2).prop_map(|ts| {
            ts.into_iter()
                .map(|t| borzoi_print::names::TyparName::new(t).expect("a type variable"))
                .collect::<Vec<_>>()
        });
    (attributes::<V>(), access(), typars)
        .prop_flat_map(|(attributes, access, typars)| {
            let tp = typars.clone();
            let repr = prop_oneof![
                field_type(tp.clone()).prop_map(TypeRepr::Abbrev),
                prop::collection::vec(
                    (any::<bool>(), binder(), field_type(tp.clone())).prop_map(
                        |(is_mutable, name, ty)| RecordField {
                            is_mutable,
                            name,
                            ty
                        }
                    ),
                    1..=3,
                )
                .prop_map(|fs| TypeRepr::Record(Vec1::from_vec(fs).expect("non-empty"))),
                prop::collection::vec(
                    (
                        type_name(),
                        prop::collection::vec(union_field(tp.clone()), 0..=2)
                    )
                        .prop_filter_map(
                            "F# refuses the case",
                            |(name, fields)| {
                                UnionCase::new(UnionCaseName::new(name).ok()?, fields).ok()
                            }
                        ),
                    1..=3,
                )
                .prop_map(|cs| TypeRepr::Union(Vec1::from_vec(cs).expect("non-empty"))),
            ];
            (Just(attributes), Just(access), Just(typars), repr)
        })
        .boxed()
}

/// A file of well-typed declarations over the prelude's names.
pub fn impl_file<V: Version>() -> BoxedStrategy<ImplFile<V>> {
    let sc = Rc::new(prelude_scope());
    (1..=4u32)
        .prop_flat_map(move |n| decls::<V>(n, &sc, &Rc::new(BTreeSet::new()), 1))
        .prop_map(|(decls, _, _)| ImplFile::AnonModule(decls))
        .boxed()
}

/// From F# 9 each union case has a tester property, `IsA` for `A` and
/// `IsEmpty`/`IsCons` for `[]`/`::`, which may share a name with neither
/// another case (FS0023) nor another tester (FS0438). Over every union of
/// two cases from the names that can collide, at a version with testers and
/// one without, [`TypeDefn::new`] must admit exactly the unions FCS accepts.
#[test]
fn union_testers_are_refused_exactly() {
    use borzoi_print::version::{V8_0, V9_0};

    const NAMES: &[&str] = &[
        "A",
        "IsA",
        "op_Nil",
        "op_ColonColon",
        "Empty",
        "Cons",
        "IsEmpty",
        "IsCons",
    ];
    fn admits<V: Version>(a: &str, b: &str) -> bool {
        let case = |n: &str| {
            let name = UnionCaseName::new(ident(n)).expect("a union case's name");
            UnionCase::new(name, Vec::new()).expect("a case")
        };
        let repr = TypeRepr::Union(Vec1::new(case(a), vec![case(b)]));
        let name = EntityName::new(ident("Y")).expect("an entity's name");
        TypeDefn::<V>::new(Vec::new(), None, name, Vec::new(), repr).is_ok()
    }
    let pairs: Vec<(&str, &str)> = NAMES
        .iter()
        .flat_map(|a| NAMES.iter().filter(move |b| *b != a).map(move |b| (*a, *b)))
        .collect();
    let failures: Vec<String> = crate::common::par_map(pairs.len() * 2, |i| {
        let (a, b) = pairs[i / 2];
        let (lang, admitted) = if i % 2 == 0 {
            (V8_0::LANGUAGE, admits::<V8_0>(a, b))
        } else {
            (V9_0::LANGUAGE, admits::<V9_0>(a, b))
        };
        let source = format!("type Y = | {a} | {b}\n");
        let errors = super::check::check_standalone_errors(&source, lang);
        (admitted != errors.is_empty()).then(|| {
            format!(
                "at {lang}, `{}`: tree admits {admitted}, FCS {errors:?}",
                source.trim()
            )
        })
    })
    .into_iter()
    .flatten()
    .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

/// Every first character [`UnionCaseName::new`] and [`ExceptionName::new`]
/// admit must be one FCS reads as upper case, though Rust's Unicode tables
/// may be newer than the runtime's: each admitted character up to U+04FF,
/// and a few past it, starts a case's and an exception's name in one file,
/// which FCS's checker must accept.
#[test]
fn every_admitted_case_initial_checks() {
    use borzoi_print::names::ExceptionName;
    use borzoi_print::version::DefaultVersion;

    let candidates = (0x41..=0x4FFu32).chain([0x1C90, 0xA7CE, 0x10400]);
    let mut source = String::new();
    let mut admitted = 0;
    for (i, c) in candidates.filter_map(char::from_u32).enumerate() {
        let Ok(name) = Ident::new(&format!("{c}C")) else {
            continue;
        };
        if UnionCaseName::new(name.clone()).is_ok() {
            source.push_str(&format!("type Y{i} = | ``{c}C``\n"));
            admitted += 1;
        }
        if ExceptionName::new(name).is_ok() {
            source.push_str(&format!("exception ``{c}C{i}``\n"));
        }
    }
    assert!(admitted > 100, "too few initials admitted: {admitted}");
    let errors = super::check::check_standalone_errors(&source, DefaultVersion::LANGUAGE);
    let lines: Vec<&str> = source.lines().collect();
    let refused: Vec<String> = errors
        .iter()
        .map(|(line, code, _)| format!("FS{code:04} {}", lines[*line as usize - 1]))
        .collect();
    assert!(refused.is_empty(), "{}", refused.join("\n"));
}

/// A file's `module` or `namespace` header names entities, so F#'s checker
/// refuses there what it refuses in a type's or nested module's name
/// (FS0883). The typed generator draws anonymous files only, as its trees
/// are checked inside modules of their own, so each header is checked here,
/// on its own, with every candidate name the tree admits.
#[test]
fn every_header_name_checks() {
    use borzoi_print::names::EntityPath;
    use borzoi_print::print_impl_file;
    use borzoi_print::tree::{NamedModule, Namespace, NamespaceName};
    use borzoi_print::version::DefaultVersion;

    let candidates = TYPE_NAMES
        .iter()
        .chain(BINDERS)
        .chain(&["A+B", "A$B", "A&B", "A[B]", "A/B", "A\\B", "A*B", "A\"B"]);
    let admitted: Vec<EntityName> = candidates
        .filter_map(|s| EntityName::new(Ident::new(s).ok()?).ok())
        .collect();
    assert!(admitted.len() > 10, "too few header names: {admitted:?}");
    let failures: Vec<String> = admitted
        .iter()
        .flat_map(|n| {
            let path = EntityPath(Vec1::new(n.clone(), vec![n.clone()]));
            [
                ImplFile::<DefaultVersion>::NamedModule(NamedModule {
                    attributes: Vec::new(),
                    access: None,
                    name: path.clone(),
                    body: ModuleBody::NonRec(Vec::new()),
                }),
                ImplFile::Namespaces(Vec1::new(
                    Namespace {
                        name: NamespaceName::Named(path),
                        body: ModuleBody::NonRec(Vec::new()),
                    },
                    Vec::new(),
                )),
            ]
        })
        .filter_map(|file| {
            let printed = print_impl_file(&file);
            let errors = super::check::check_standalone_errors(&printed, DefaultVersion::LANGUAGE);
            (!errors.is_empty()).then(|| format!("{printed}{errors:?}"))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

/// The typed checks: each version's trees, drawn from a fixed seed, and a deep
/// twin from a fresh one.
mod run {
    use std::collections::BTreeSet;

    use borzoi_print::print_impl_file;
    use borzoi_print::tree::ImplFile;
    use borzoi_print::version::{
        LanguageVersion, Preview, V4_6, V4_7, V5_0, V6_0, V7_0, V8_0, V9_0, V10_0, V11_0, Version,
    };
    use proptest::strategy::{Strategy, ValueTree};
    use proptest::test_runner::{Config, RngAlgorithm, TestRng, TestRunner};

    use super::super::check::check_errors;
    use super::super::round_trips_at;
    use super::impl_file;
    use crate::common::par_map;

    /// How many FCS calls one failure's shrinking may spend.
    const SHRINK_BUDGET: usize = 300;

    /// How many filter rejections one tree's draw may make.
    const MAX_REJECTS: u32 = 100_000;

    /// How many failures, each with distinct errors, are shrunk and shown.
    const SHOWN: usize = 16;

    type Tree<V> = Box<dyn ValueTree<Value = ImplFile<V>>>;

    /// Why `file` fails, if it does: the errors FCS's checker reports at the
    /// file's version, or the round trip's failure.
    fn failure<V: Version>(file: &ImplFile<V>) -> Option<Failure> {
        let errors = check_errors(std::slice::from_ref(file), V::LANGUAGE).remove(0);
        if !errors.is_empty() {
            return Some(Failure::Check(errors));
        }
        round_trips(file).err().map(Failure::RoundTrip)
    }

    /// Whether `file` round-trips at its version and at the newest: each gate
    /// is a threshold, so the two ends stand for every version that reads it.
    fn round_trips<V: Version>(file: &ImplFile<V>) -> Result<(), String> {
        round_trips_at(file, &[V::LANGUAGE, LanguageVersion::MAX])
    }

    #[derive(Debug, Clone)]
    enum Failure {
        Check(Vec<(i64, String)>),
        RoundTrip(String),
    }

    impl Failure {
        fn codes(&self) -> BTreeSet<i64> {
            match self {
                Failure::Check(errors) => errors.iter().map(|(c, _)| *c).collect(),
                Failure::RoundTrip(_) => BTreeSet::new(),
            }
        }

        /// Whether `other` is the same failure, as far as shrinking goes: a
        /// check failure sharing an error code, or a round trip's.
        fn same_kind(&self, other: &Failure) -> bool {
            match (self, other) {
                (Failure::Check(_), Failure::Check(_)) => !self.codes().is_disjoint(&other.codes()),
                (Failure::RoundTrip(_), Failure::RoundTrip(_)) => true,
                _ => false,
            }
        }
    }

    impl std::fmt::Display for Failure {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Failure::Check(errors) => {
                    for (code, message) in errors {
                        writeln!(f, "FS{code:04}: {message}")?;
                    }
                    Ok(())
                }
                Failure::RoundTrip(why) => writeln!(f, "round trip: {why}"),
            }
        }
    }

    /// `tree` shrunk as far as `budget` FCS calls take it while it still
    /// fails as `original` does, and its failure.
    fn shrink<V: Version>(tree: &mut Tree<V>, original: &Failure) -> (ImplFile<V>, Failure) {
        let mut best = (tree.current(), original.clone());
        if !tree.simplify() {
            return best;
        }
        for _ in 0..SHRINK_BUDGET {
            let current = tree.current();
            match failure(&current).filter(|f| original.same_kind(f)) {
                Some(f) => {
                    best = (current, f);
                    if !tree.simplify() {
                        break;
                    }
                }
                None => {
                    if !tree.complicate() {
                        break;
                    }
                }
            }
        }
        best
    }

    /// The seed: `BORZOI_PRINT_SEED` (a number) if set, else `default`.
    fn seed(default: u64) -> u64 {
        std::env::var("BORZOI_PRINT_SEED")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(default)
    }

    /// `cases` typed files at `V` drawn from `seed`, each type-checked and
    /// round-tripped at `V`; the shrunk failures, described.
    fn failures<V: Version>(cases: usize, seed: u64) -> Vec<String> {
        let mut bytes = [0u8; 32];
        bytes[..8].copy_from_slice(&seed.to_le_bytes());
        let mut seeds = TestRunner::new_with_rng(
            Config::default(),
            TestRng::from_seed(RngAlgorithm::ChaCha, &bytes),
        );
        let strategy = impl_file::<V>();
        // Each tree draws on its own runner, so the cap on filter rejections
        // bounds one draw: a filter that cannot pass fails loudly, naming
        // itself, rather than spinning.
        let mut trees: Vec<Tree<V>> = (0..cases)
            .map(|i| {
                let config = Config {
                    max_local_rejects: MAX_REJECTS,
                    ..Config::default()
                };
                let mut runner = TestRunner::new_with_rng(config, seeds.new_rng());
                match strategy.new_tree(&mut runner) {
                    Ok(tree) => Box::new(tree) as Tree<V>,
                    Err(e) => panic!("tree {i} of seed {seed}: {e}\n{runner}"),
                }
            })
            .collect();
        let files: Vec<ImplFile<V>> = trees.iter().map(|t| t.current()).collect();
        let checked = check_errors(&files, V::LANGUAGE);
        let round: Vec<Option<String>> = par_map(files.len(), |i| round_trips(&files[i]).err());
        let failing: Vec<(usize, Failure)> = checked
            .into_iter()
            .zip(round)
            .enumerate()
            .filter_map(|(i, (errors, round))| {
                if !errors.is_empty() {
                    Some((i, Failure::Check(errors)))
                } else {
                    round.map(|r| (i, Failure::RoundTrip(r)))
                }
            })
            .collect();
        let total = failing.len();
        let all: Vec<Failure> = failing.iter().map(|(_, f)| f.clone()).collect();
        let mut shown: Vec<Failure> = Vec::new();
        let mut out = Vec::new();
        for (i, f) in failing {
            if shown.len() == SHOWN || shown.iter().any(|s| s.same_kind(&f)) {
                continue;
            }
            shown.push(f.clone());
            let (file, why) = shrink(&mut trees[i], &f);
            out.push(format!(
                "{why}--- shrunk ---\n{}--- drawn ---\n{}",
                print_impl_file(&file),
                print_impl_file(&files[i])
            ));
        }
        if total > 0 {
            let mut census: std::collections::BTreeMap<String, usize> = Default::default();
            for f in &all {
                match f {
                    Failure::Check(_) => f
                        .codes()
                        .into_iter()
                        .for_each(|c| *census.entry(format!("FS{c:04}")).or_default() += 1),
                    Failure::RoundTrip(_) => {
                        *census.entry("round trip".to_owned()).or_default() += 1
                    }
                }
            }
            out.insert(
                0,
                format!(
                    "{total} of {cases} typed files at {} fail (seed {seed}): {census:?}; the first of each kind, shrunk:",
                    V::LANGUAGE
                ),
            );
        }
        out
    }

    fn cases(default: usize) -> usize {
        std::env::var("BORZOI_PRINT_CASES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(default)
    }

    macro_rules! per_version {
        ($($module:ident: $version:ty;)*) => {$(
            mod $module {
                use super::*;

                #[test]
                fn every_typed_file_checks() {
                    let out = failures::<$version>(cases(128), seed(1));
                    assert!(out.is_empty(), "{}", out.join("\n\n"));
                }

                #[test]
                #[ignore = "deep twin of every_typed_file_checks"]
                fn deep_every_typed_file_checks() {
                    let fresh = std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .expect("after the epoch")
                        .as_nanos() as u64;
                    let out = failures::<$version>(cases(2048), seed(fresh));
                    assert!(out.is_empty(), "{}", out.join("\n\n"));
                }
            }
        )*};
    }

    per_version! {
        v4_6: V4_6;
        v4_7: V4_7;
        v5_0: V5_0;
        v6_0: V6_0;
        v7_0: V7_0;
        v8_0: V8_0;
        v9_0: V9_0;
        v10_0: V10_0;
        v11_0: V11_0;
        preview: Preview;
    }
}
