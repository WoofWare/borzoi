//! Every computation-expression statement nested in every body of every
//! statement, beside the generator's random ones, round-tripped and
//! type-checked at every version.
//!
//! Whether a statement's later parts (`else`, a `|` clause, `with`,
//! `finally`, `done`) and the next statement end the right construct depends
//! on what the body before them ends with: an `if` without `else` takes a
//! following `else` as its own, a `match` takes a following `|`. A random tree
//! rarely nests the one in the other, so this checks the pairs exhaustively:
//! each statement shape, as the whole of each body slot of each statement,
//! and as the last statement of that body, both with a statement after the
//! outer one and without, in each bracket a body can be in (`builder { }`,
//! `[ ]`, `[| |]`), with each statement and binding the context and version
//! allow.
//!
//! The table's names are [`super::check`]'s, so FCS's checker grades every
//! nesting too: a statement the types allow somewhere F#'s checker refuses it
//! (`return` in a list, a parenthesised `if` in a builder) fails here.

use borzoi_print::names::{Ident, InfixOperator, LongIdent, Operator, ValueName};
use borzoi_print::print_impl_file;
use borzoi_print::tree::{
    AndBang, Args, Binding, BindingHead, Comp, CompClause, CompItem, Const, Context, Expr,
    ForDirection, ForSource, ImplFile, InBuilder, InCollection, LetBang, LetBindings, ListBody,
    ListComp, LocalBindings, MatchClause, ModuleBindings, ModuleDecl, Pat, Range, Stmt, StmtExpr,
    Type, UseBang, UseBinding, UseName,
};
use borzoi_print::vec::{Vec1, Vec2};
use borzoi_print::version::{
    Gate, Preview, V4_6, V4_7, V5_0, V6_0, V7_0, V8_0, V9_0, V10_0, V11_0, Version,
};

use super::check::{check_failures, check_report};
use super::round_trips;
use crate::common::par_map;

fn ident(s: &str) -> Ident {
    Ident::new(s).expect("an identifier")
}

fn name<V: Version>(s: &str) -> Expr<V> {
    Expr::Name(LongIdent::single(ident(s)))
}

fn var<V: Version>(s: &str) -> Pat<V> {
    Pat::Name(LongIdent::single(ident(s)))
}

fn last<V: Version, K: Context>(s: Stmt<V, K>) -> Comp<V, K> {
    Comp::stmt(s)
}

/// `item`, then `last`.
fn then<V: Version, K: Context>(item: CompItem<V, K>, last: Stmt<V, K>) -> Comp<V, K> {
    Comp {
        init: vec![item],
        last,
    }
}

/// A statement ending a body with a value: `return` in a builder, `yield` in
/// a list.
fn result<V: Version, K: Context>(leaf: &str) -> Stmt<V, K> {
    match K::Bang::WITNESS {
        Some(gate) => Stmt::Return {
            gate,
            expr: name(leaf),
        },
        None => Stmt::Yield(name(leaf)),
    }
}

fn clauses<V: Version, K: Context>(body: &Comp<V, K>) -> Vec1<CompClause<V, K>> {
    let clause = |p: &str| CompClause {
        pat: var(p),
        guard: None,
        body: body.clone(),
    };
    Vec1::new(clause("p"), vec![clause("q")])
}

/// Each statement shape the context and version allow, with every body slot
/// holding `body`.
fn statements<V: Version, K: Context>(body: &Comp<V, K>) -> Vec<Stmt<V, K>> {
    let b = || Box::new(body.clone());
    let mut out = vec![
        Stmt::IfThenElse {
            cond: name("c"),
            then_branch: b(),
            else_branch: None,
        },
        Stmt::IfThenElse {
            cond: name("c"),
            then_branch: b(),
            else_branch: Some(b()),
        },
        Stmt::Match {
            scrutinee: name("e"),
            clauses: clauses(body),
        },
        Stmt::While {
            cond: name("c"),
            body: b(),
        },
        Stmt::For {
            var: ident("i"),
            from: name("a"),
            direction: ForDirection::To,
            to: name("b"),
            body: b(),
        },
        Stmt::ForEach {
            pat: var("x"),
            source: ForSource::Expr(name("xs")),
            body: b(),
        },
        Stmt::ForEach {
            pat: var("x"),
            source: ForSource::Range(Range {
                from: name("a"),
                step: Some(name("s")),
                to: name("b"),
            }),
            body: b(),
        },
        Stmt::TryFinally {
            body: b(),
            finally: name("f"),
        },
    ];
    if let Some(gate) = K::Bang::WITNESS {
        out.push(Stmt::MatchBang {
            gate,
            scrutinee: name("e"),
            clauses: clauses(body),
        });
        if let Some(while_bang) = V::WhileBang::WITNESS {
            out.push(Stmt::WhileBang {
                gate: while_bang,
                bang: gate,
                cond: name("c"),
                body: b(),
            });
        }
    }
    if let Some(gate) = K::TryWith::<V>::WITNESS {
        out.push(Stmt::TryWith {
            gate,
            body: b(),
            clauses: clauses(body),
        });
    }
    out
}

/// The statements with no body the context and version allow, one of each
/// kind.
fn simple<V: Version, K: Context>() -> Vec<Stmt<V, K>> {
    let mut out = vec![
        Stmt::Expr(StmtExpr::new(name("u")).expect("a name is an expression statement")),
        // A bare `do`, which in a list is a statement, not an element.
        Stmt::Expr(
            StmtExpr::new(Expr::Do(Box::new(name("u")))).expect("`do` is an expression statement"),
        ),
        Stmt::Yield(name("e")),
        Stmt::YieldFrom(name("xs")),
    ];
    // An `if` expression in parentheses, not the `if` statement, and
    // `( * )`, which F# reads as a parenthesised wildcard.
    let parenthesised = [
        Expr::IfThenElse {
            cond: Box::new(name("c")),
            then_branch: Box::new(name("u")),
            else_branch: Some(Box::new(name("u"))),
        },
        Expr::OpValue(Operator::new("*").expect("an operator")),
    ];
    for e in parenthesised {
        if let Ok(paren) = StmtExpr::new(e) {
            out.push(Stmt::Expr(paren));
        }
    }
    if let Some(gate) = K::Bang::WITNESS {
        out.push(Stmt::DoBang {
            gate,
            expr: name("u"),
        });
        out.push(Stmt::Return {
            gate,
            expr: name("e"),
        });
        out.push(Stmt::ReturnFrom {
            gate,
            expr: name("xs"),
        });
    }
    out
}

/// What a `use` or `use!` binds: `x`, and `_` where `G` has it.
fn use_names<G: Gate>() -> Vec<UseName<G>> {
    let mut out = vec![UseName::Named(ValueName::Ident(ident("x")))];
    if let Some(gate) = G::WITNESS {
        out.push(UseName::Discard(gate));
    }
    out
}

/// Each kind of local `let` group the types take: `binding`, then mutable,
/// an inline function, a recursive pair, and a pattern.
fn local_groups<V: Version>(binding: Binding<V>) -> Vec<LocalBindings<V>> {
    let with_head = |head: BindingHead<V>, is_inline: bool| Binding {
        attributes: Vec::new(),
        is_inline,
        body: name(if matches!(head, BindingHead::Pattern(_)) {
            "t"
        } else {
            "v"
        }),
        head,
    };
    let function = |f: &str| BindingHead::Function {
        access: None,
        name: ValueName::Ident(ident(f)),
        params: Vec1::new(var("p"), Vec::new()),
    };
    let groups = vec![
        LetBindings::NonRec(Box::new(binding)),
        LetBindings::NonRec(Box::new(with_head(
            BindingHead::Name {
                is_mutable: true,
                access: None,
                name: ValueName::Ident(ident("x")),
            },
            false,
        ))),
        LetBindings::NonRec(Box::new(with_head(function("g"), true))),
        LetBindings::Rec(Vec1::new(
            with_head(function("g"), false),
            vec![with_head(function("h"), false)],
        )),
        LetBindings::NonRec(Box::new(with_head(
            BindingHead::Pattern(Pat::Tuple(Vec2::new(var("x"), var("y"), Vec::new()))),
            false,
        ))),
    ];
    groups
        .into_iter()
        .map(|g| LocalBindings::new(g).expect("a local binding"))
        .collect()
}

/// Bodies worth nesting: each statement shape alone and followed by another,
/// over a body that yields and one that does not (which F# 4.6 can read as a
/// list literal's element), and each kind of binding over a statement.
fn bodies<V: Version, K: Context>() -> Vec<Comp<V, K>> {
    let r = || result::<V, K>("r");
    let u = || Stmt::Expr(StmtExpr::new(name("u")).expect("a name is an expression statement"));
    let mut shapes = simple::<V, K>();
    shapes.extend(statements(&last(r())));
    shapes.extend(statements(&last(u())));
    let mut out = Vec::new();
    for s in shapes {
        out.push(then(CompItem::Stmt(s.clone()), r()));
        out.push(last(s));
    }
    let x = Binding {
        attributes: Vec::new(),
        is_inline: false,
        head: BindingHead::Name {
            is_mutable: false,
            access: None,
            name: ValueName::Ident(ident("x")),
        },
        body: name("v"),
    };
    for group in local_groups(x) {
        out.push(then(CompItem::Let(group), r()));
    }
    for name in use_names() {
        let value = self::name("v");
        out.push(then(CompItem::Use(UseBinding { name, value }), r()));
    }
    if let Some(gate) = K::Bang::WITNESS {
        let mut ands = vec![Vec::new()];
        if let Some(and) = V::AndBang::WITNESS {
            ands.push(vec![AndBang {
                gate: and,
                pat: var("y"),
                value: name("v"),
            }]);
        }
        for ands in ands {
            let bang = LetBang {
                gate,
                pat: var("x"),
                value: name("v"),
                ands,
            };
            out.push(then(CompItem::LetBang(bang), r()));
        }
        for name in use_names() {
            let value = self::name("v");
            out.push(then(CompItem::UseBang(UseBang { gate, name, value }), r()));
        }
    }
    out
}

/// Each statement shape over each body, with a statement after it and
/// without.
fn nestings<V: Version, K: Context>() -> Vec<Comp<V, K>> {
    let mut out = Vec::new();
    for body in bodies::<V, K>() {
        for outer in statements(&body) {
            out.push(then(CompItem::Stmt(outer.clone()), result("z")));
            out.push(last(outer));
        }
    }
    out
}

/// `let x () = e`: a function, so a body that never yields, whose element
/// type is generic, is not a value the checker must generalise.
fn file<V: Version>(e: Expr<V>) -> ImplFile<V> {
    ImplFile::AnonModule(vec![ModuleDecl::Let(
        ModuleBindings::new(LetBindings::NonRec(Box::new(Binding {
            attributes: Vec::new(),
            is_inline: false,
            head: BindingHead::Function {
                access: None,
                name: ValueName::Ident(ident("x")),
                params: Vec1::new(Pat::Const(Const::Unit), Vec::new()),
            },
            body: e,
        })))
        .expect("a module's group"),
    )])
}

/// The table's files at `V`: each nesting in `builder { }`, `[ ]` and
/// `[| |]`, and the ranges a list can be.
fn table<V: Version>() -> Vec<ImplFile<V>> {
    let mut files = Vec::new();
    for body in nestings::<V, InBuilder>() {
        files.push(file(Expr::Computation {
            builder: Box::new(name("builder")),
            body: Box::new(body),
        }));
    }
    let mut lists: Vec<ListBody<V>> = nestings::<V, InCollection>()
        .into_iter()
        .filter_map(|c| ListComp::new(c).ok())
        .map(ListBody::Comp)
        .collect();
    for step in [None, Some(name("s"))] {
        lists.push(ListBody::Range(Range {
            from: name("a"),
            step,
            to: name("b"),
        }));
    }
    // A literal's elements, one and several, which F# 4.6 takes in
    // parentheses whatever they are.
    let paren_if = Expr::IfThenElse {
        cond: Box::new(name("c")),
        then_branch: Box::new(name("e")),
        else_branch: Some(Box::new(name("e"))),
    };
    for elements in [
        Vec1::new(name("e"), Vec::new()),
        Vec1::new(Expr::Do(Box::new(name("u"))), Vec::new()),
        Vec1::new(paren_if, vec![name("e"), name("r")]),
    ] {
        lists.push(ListBody::Elements(elements));
    }
    for body in lists {
        files.push(file(Expr::List(Some(Box::new(body.clone())))));
        files.push(file(Expr::Array(Some(Box::new(body)))));
    }
    files
}

/// Whether F# reads `comp` as a literal's elements whatever the version:
/// every statement an expression other than a bare `do`, and no binding.
fn is_elements<V: Version>(comp: &Comp<V, InCollection>) -> bool {
    let element =
        |s: &Stmt<V, InCollection>| matches!(s, Stmt::Expr(e) if !matches!(e.expr(), Expr::Do(_)));
    comp.init
        .iter()
        .all(|item| matches!(item, CompItem::Stmt(s) if element(s)))
        && element(&comp.last)
}

/// The table's comprehensions that [`ListComp::new`] refuses at `V` for any
/// reason but being a literal's elements, printed unchecked: F#'s checker
/// must reject each.
fn refused_lists<V: Version>() -> Vec<ImplFile<V>> {
    nestings::<V, InCollection>()
        .into_iter()
        .filter(|c| ListComp::new(c.clone()).is_err() && !is_elements(c))
        .map(|c| {
            file(Expr::List(Some(Box::new(ListBody::Comp(
                ListComp::unchecked(c),
            )))))
        })
        .collect()
}

/// What FCS's checker at `V` rejects in the table, and what it accepts of
/// what the table's types refuse, if anything.
fn statement_check_failures<V: Version>() -> Option<String> {
    let files = table::<V>();
    let failures = check_failures(&files, V::LANGUAGE);
    let refused = refused_lists::<V>();
    let rejected = check_failures(&refused, V::LANGUAGE).len();
    let mut report = Vec::new();
    if !failures.is_empty() {
        report.push(format!(
            "FCS's checker at {} rejects {} of {} nestings:\n\n{}",
            V::LANGUAGE,
            failures.len(),
            files.len(),
            check_report(&failures)
        ));
    }
    if rejected != refused.len() {
        let accepted: Vec<String> = refused
            .iter()
            .filter(|f| check_failures(std::slice::from_ref(*f), V::LANGUAGE).is_empty())
            .take(5)
            .map(print_impl_file)
            .collect();
        report.push(format!(
            "FCS's checker at {} accepts {} of the {} list bodies the types refuse, such as:\n{}",
            V::LANGUAGE,
            refused.len() - rejected,
            refused.len(),
            accepted.join("\n")
        ));
    }
    (!report.is_empty()).then(|| report.join("\n\n"))
}

#[test]
fn every_statement_checks_at_every_version() {
    // F# 4.6 refuses a list body of expressions and yield-free `if`s, so the
    // check that F# refuses what the types refuse has cases there.
    assert!(!refused_lists::<V4_6>().is_empty());
    let failures: Vec<String> = [
        statement_check_failures::<V4_6>(),
        statement_check_failures::<V4_7>(),
        statement_check_failures::<V5_0>(),
        statement_check_failures::<V6_0>(),
        statement_check_failures::<V7_0>(),
        statement_check_failures::<V8_0>(),
        statement_check_failures::<V9_0>(),
        statement_check_failures::<V10_0>(),
        statement_check_failures::<V11_0>(),
        statement_check_failures::<Preview>(),
    ]
    .into_iter()
    .flatten()
    .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}

fn every_statement_nests<V: Version>() {
    let files = table::<V>();
    assert!(files.len() > 1000, "only {} files", files.len());
    let failures: Vec<String> = par_map(files.len(), |i| round_trips(&files[i]).err())
        .into_iter()
        .flatten()
        .collect();
    assert!(
        failures.is_empty(),
        "{} of {} nestings do not round-trip:\n{}",
        failures.len(),
        files.len(),
        failures.join("\n\n")
    );
}

#[test]
fn every_statement_nests_in_every_body() {
    every_statement_nests::<Preview>();
}

#[test]
fn every_statement_nests_in_every_body_at_the_oldest_version() {
    every_statement_nests::<V4_6>();
}

/// One expression of each form, over plain names: each infix operator of the
/// generator's, and every other [`Expr`] variant.
fn expression_forms<V: Version>() -> Vec<Expr<V>> {
    let n = || Box::new(name::<V>("a"));
    let ty = || Type::Name(LongIdent::single(ident("T")));
    let clause = || {
        Vec1::new(
            MatchClause {
                pat: var("p"),
                guard: None,
                result: name("a"),
            },
            Vec::new(),
        )
    };
    let mut out: Vec<Expr<V>> = super::generate::OPERATORS
        .iter()
        .filter_map(|op| Operator::new(op).ok().and_then(InfixOperator::new))
        .map(|op| Expr::Infix {
            op,
            lhs: n(),
            rhs: n(),
        })
        .collect();
    out.extend([
        Expr::Const(Const::Int32(1)),
        Expr::Const(Const::Unit),
        Expr::Null,
        name("a"),
        Expr::OpValue(Operator::new("+").expect("an operator")),
        Expr::OpValue(Operator::new("*").expect("an operator")),
        Expr::App {
            func: n(),
            arg: n(),
        },
        Expr::MethodApp {
            func: n(),
            args: Args::Positional(Vec2::new(name("a"), name("b"), Vec::new())),
        },
        Expr::Tuple(Vec2::new(name("a"), name("b"), Vec::new())),
        Expr::List(None),
        Expr::Array(None),
        Expr::Record {
            copy: None,
            fields: Vec1::new((LongIdent::single(ident("A")), name("a")), Vec::new()),
        },
        Expr::FieldGet {
            expr: n(),
            field: ident("f"),
        },
        Expr::Set {
            target: LongIdent::single(ident("a")),
            value: n(),
        },
        Expr::Lambda {
            params: Vec1::new(var("p"), Vec::new()),
            body: n(),
        },
        Expr::Function(clause()),
        Expr::Match {
            scrutinee: n(),
            clauses: clause(),
        },
        Expr::IfThenElse {
            cond: n(),
            then_branch: n(),
            else_branch: Some(n()),
        },
        Expr::LetIn {
            bindings: LocalBindings::new(LetBindings::NonRec(Box::new(Binding {
                attributes: Vec::new(),
                is_inline: false,
                head: BindingHead::Name {
                    is_mutable: false,
                    access: None,
                    name: ValueName::Ident(ident("y")),
                },
                body: name("a"),
            })))
            .expect("a local binding"),
            body: n(),
        },
        Expr::Sequential(n(), n()),
        Expr::Typed {
            expr: n(),
            ty: ty(),
        },
        Expr::TypeTest {
            expr: n(),
            ty: ty(),
        },
        Expr::Upcast {
            expr: n(),
            ty: ty(),
        },
        Expr::Downcast {
            expr: n(),
            ty: ty(),
        },
        Expr::Cons {
            head: n(),
            tail: n(),
        },
        Expr::TryWith {
            body: n(),
            clauses: clause(),
        },
        Expr::TryFinally {
            body: n(),
            finally: n(),
        },
        Expr::While {
            cond: n(),
            body: n(),
        },
        Expr::For {
            var: ident("i"),
            from: n(),
            direction: ForDirection::To,
            to: n(),
            body: n(),
        },
        Expr::ForEach {
            pat: var("x"),
            source: Box::new(ForSource::Expr(name("a"))),
            body: n(),
        },
        Expr::Lazy(n()),
        Expr::Assert(n()),
        Expr::Do(n()),
        Expr::Computation {
            builder: n(),
            body: Box::new(Comp::stmt(result("r"))),
        },
    ]);
    if let Some(gate) = V::AccessorFunctionShorthand::WITNESS {
        out.push(Expr::DotLambda {
            gate,
            path: LongIdent::single(ident("A")),
        });
    }
    out
}

/// Each expression form as an expression statement, where `K` at `V` takes
/// it, before another statement and last.
fn expression_statements<V: Version, K: Context>() -> Vec<Comp<V, K>> {
    expression_forms::<V>()
        .into_iter()
        .filter_map(|e| StmtExpr::<V, K>::new(e).ok())
        .flat_map(|e| {
            [
                then(CompItem::Stmt(Stmt::Expr(e.clone())), result("z")),
                last(Stmt::Expr(e)),
            ]
        })
        .collect()
}

fn every_expression_is_a_statement<V: Version>() -> Vec<String> {
    let mut files: Vec<ImplFile<V>> = expression_statements::<V, InBuilder>()
        .into_iter()
        .map(|body| {
            file(Expr::Computation {
                builder: Box::new(name("builder")),
                body: Box::new(body),
            })
        })
        .collect();
    for body in expression_statements::<V, InCollection>() {
        if let Ok(body) = ListComp::new(body) {
            files.push(file(Expr::List(Some(Box::new(ListBody::Comp(body))))));
        }
    }
    // Each form as a literal's element, alone and before another.
    for e in expression_forms::<V>() {
        for elements in [
            Vec1::new(e.clone(), Vec::new()),
            Vec1::new(e, vec![name("z")]),
        ] {
            files.push(file(Expr::List(Some(Box::new(ListBody::Elements(
                elements,
            ))))));
        }
    }
    par_map(files.len(), |i| round_trips(&files[i]).err())
        .into_iter()
        .flatten()
        .collect()
}

#[test]
fn every_expression_form_is_a_statement_where_the_types_allow() {
    let mut failures = every_expression_is_a_statement::<V4_6>();
    failures.extend(every_expression_is_a_statement::<V4_7>());
    failures.extend(every_expression_is_a_statement::<Preview>());
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
