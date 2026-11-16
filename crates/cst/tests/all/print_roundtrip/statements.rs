//! Every computation-expression statement nested in every body of every
//! statement, beside the generator's random ones.
//!
//! Whether a statement's later parts (`else`, a `|` clause, `with`,
//! `finally`, `done`) and the next statement end the right construct depends
//! on what the body before them ends with: an `if` without `else` takes a
//! following `else` as its own, a `match` takes a following `|`. A random tree
//! rarely nests the one in the other, so this checks the pairs exhaustively:
//! each statement shape, as the whole of each body slot of each statement,
//! and as the last statement of that body, both with a statement after the
//! outer one and without, in each bracket a body can be in (`builder { }`,
//! `[ ]`, `[| |]`).

use borzoi_print::names::{Ident, LongIdent, ValueName};
use borzoi_print::tree::{
    BangKind, Binding, BindingHead, Comp, CompClause, Expr, ForDirection, ForSource, ImplFile,
    LetBindings, ModuleDecl, Pat, Range, Stmt,
};
use borzoi_print::vec::Vec1;
use borzoi_print::version::{Gate, Preview, V4_6, Version};

use super::round_trips;
use crate::common::par_map;

fn ident(s: &str) -> Ident {
    Ident::new(s).expect("an identifier")
}

fn name<V: Version>(s: &str) -> Expr<V> {
    Expr::Name(LongIdent::single(ident(s)))
}

fn var(s: &str) -> Pat {
    Pat::Name(LongIdent::single(ident(s)))
}

fn last<V: Version>(s: Stmt<V>) -> Comp<V> {
    Comp::Last(s)
}

fn clauses<V: Version>(body: &Comp<V>) -> Vec1<CompClause<V>> {
    let clause = |p: &str| CompClause {
        pat: var(p),
        guard: None,
        body: body.clone(),
    };
    Vec1::new(clause("p"), vec![clause("q")])
}

/// Each statement shape, with every body slot holding `body`.
fn statements<V: Version>(body: &Comp<V>) -> Vec<Stmt<V>> {
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
        Stmt::MatchBang {
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
        Stmt::TryWith {
            body: b(),
            clauses: clauses(body),
        },
        Stmt::TryFinally {
            body: b(),
            finally: name("f"),
        },
    ];
    if let Some(gate) = V::WhileBang::WITNESS {
        out.push(Stmt::WhileBang {
            gate,
            cond: name("c"),
            body: b(),
        });
    }
    out
}

/// The statements with no body, one of each kind.
fn simple<V: Version>() -> Vec<Stmt<V>> {
    vec![
        Stmt::Expr(name("e")),
        Stmt::DoBang(name("e")),
        Stmt::Return(name("e")),
        Stmt::ReturnFrom(name("e")),
        Stmt::Yield(name("e")),
        Stmt::YieldFrom(name("e")),
        Stmt::Range(Range {
            from: name("a"),
            step: None,
            to: name("b"),
        }),
    ]
}

/// Bodies worth nesting: each statement shape alone and followed by another,
/// and each kind of binding over a statement.
fn bodies<V: Version>() -> Vec<Comp<V>> {
    let inner = last(Stmt::Return(name("r")));
    let mut shapes = simple::<V>();
    shapes.extend(statements(&inner));
    let mut out = Vec::new();
    for s in shapes {
        out.push(Comp::Then(s.clone(), Box::new(inner.clone())));
        out.push(last(s));
    }
    let x = || {
        Box::new(Binding {
            attributes: Vec::new(),
            is_inline: false,
            head: BindingHead::Name {
                is_mutable: false,
                access: None,
                name: ValueName::Ident(ident("x")),
            },
            body: name("v"),
        })
    };
    out.push(Comp::Let(LetBindings::NonRec(x()), Box::new(inner.clone())));
    out.push(Comp::Use(x(), Box::new(inner.clone())));
    for kind in [BangKind::Let, BangKind::Use] {
        out.push(Comp::Bang {
            kind,
            pat: var("x"),
            value: name("v"),
            ands: Vec::new(),
            rest: Box::new(inner.clone()),
        });
    }
    out
}

/// `let x = builder { body }`, `[ body ]` or `[| body |]`.
fn files<V: Version>(body: Comp<V>) -> Vec<ImplFile<V>> {
    let body = Box::new(body);
    [
        Expr::Computation {
            builder: Box::new(name("builder")),
            body: body.clone(),
        },
        Expr::List(Some(body.clone())),
        Expr::Array(Some(body)),
    ]
    .into_iter()
    .map(file)
    .collect()
}

/// `let x = e`.
fn file<V: Version>(e: Expr<V>) -> ImplFile<V> {
    ImplFile::AnonModule(vec![ModuleDecl::Let(LetBindings::NonRec(Box::new(
        Binding {
            attributes: Vec::new(),
            is_inline: false,
            head: BindingHead::Name {
                is_mutable: false,
                access: None,
                name: ValueName::Ident(ident("x")),
            },
            body: e,
        },
    )))])
}

fn every_statement_nests<V: Version>() {
    let mut files = Vec::new();
    for body in bodies::<V>() {
        for outer in statements(&body) {
            let after = last(Stmt::Return(name("z")));
            files.extend(self::files(Comp::Then(outer.clone(), Box::new(after))));
            files.extend(self::files(last(outer)));
        }
    }
    assert!(files.len() > 1500, "only {} files", files.len());
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
