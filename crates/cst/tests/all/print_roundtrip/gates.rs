//! Each version gate held to FCS from below.
//!
//! The generated trees show a gate is not too *low*: a tree at a version
//! without the feature cannot hold the construct, and one at a version with it
//! is checked at that version. These show it is not too *high*: the
//! construct, printed, round-trips and type-checks ([`super::check`]) at its
//! version and is rejected one version below. Where FCS's parser enforces
//! the feature, the rejection must be its FS3350 naming the feature; where
//! only its checker does, which reports such a feature in its own words
//! (FS1228 for `use! _`, FS0796 for `try … with` in a list), the construct
//! must draw some checker error there.

use borzoi_cst::language_version::FcsStage;
use borzoi_print::names::{Ident, InfixOperator, LongIdent, Operator, ValueName};
use borzoi_print::print_impl_file;
use borzoi_print::tree::{
    AliasPat, AndBang, AsAlias, Binding, BindingHead, Comp, CompClause, CompItem, Const, Context,
    Expr, ImplFile, InBuilder, InCollection, LetBang, LetBindings, ListBody, ListComp, MatchClause,
    ModuleBindings, ModuleDecl, Pat, Stmt, StmtExpr, UseBang, UseName,
};
use borzoi_print::vec::Vec1;
use borzoi_print::version::{
    Available, LanguageFeature, LanguageVersion, Preview, V4_7, V5_0, V6_0, V8_0, V10_0, Version,
};

use super::check::{check_failures, check_report};
use super::{fcs_record_at, round_trips_at};
use crate::common::fcs_all_diagnostics;
use crate::common::fcs_record::on_deep_stack;

fn ident(s: &str) -> Ident {
    Ident::new(s).expect("an identifier")
}

fn name<V: Version>(s: &str) -> Expr<V> {
    Expr::Name(LongIdent::single(ident(s)))
}

fn var<V: Version>(s: &str) -> Pat<V> {
    Pat::Name(LongIdent::single(ident(s)))
}

/// `let x () = e`.
fn let_x<V: Version>(e: Expr<V>) -> ImplFile<V> {
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

/// `builder { body }`.
fn computation<V: Version>(body: Comp<V, InBuilder>) -> Expr<V> {
    Expr::Computation {
        builder: Box::new(name("builder")),
        body: Box::new(body),
    }
}

/// `[ body ]`.
fn list<V: Version>(body: Comp<V, InCollection>) -> Expr<V> {
    Expr::List(Some(Box::new(ListBody::Comp(
        ListComp::new(body).expect("a list body"),
    ))))
}

/// `return r`.
fn ret<V: Version, K: Context<Bang = Available>>() -> Stmt<V, K> {
    Stmt::Return {
        gate: Available,
        expr: name("r"),
    }
}

/// `tree`, which uses `feature` and is at its version, round-trips and
/// type-checks there and at `preview`, and FCS rejects it one version
/// earlier for want of it.
fn gate_is_exact<V: Version>(feature: LanguageFeature, tree: &ImplFile<V>) -> Result<(), String> {
    assert_eq!(V::LANGUAGE, feature.introduced(), "{feature:?}'s tree");
    round_trips_at(tree, &[V::LANGUAGE, LanguageVersion::MAX])?;
    let files = std::slice::from_ref(tree);
    for lang in [V::LANGUAGE, LanguageVersion::MAX] {
        let failures = check_failures(files, lang);
        if !failures.is_empty() {
            return Err(format!(
                "FCS's checker at {lang} rejects {feature:?}'s tree:\n{}",
                check_report(&failures)
            ));
        }
    }
    let below = *LanguageVersion::NUMBERED
        .iter()
        .rev()
        .find(|&&v| v < V::LANGUAGE)
        .expect("a version below the gate");
    let printed = print_impl_file(tree);
    let parser_enforces = feature
        .fcs_stages()
        .iter()
        .any(|s| matches!(s, FcsStage::Lex | FcsStage::LexFilter | FcsStage::Parse));
    if !parser_enforces {
        assert_eq!(
            feature.fcs_stages(),
            [FcsStage::Check],
            "{feature:?} is enforced by neither FCS's parser nor its checker"
        );
        return if check_failures(files, below).is_empty() {
            Err(format!(
                "FCS's checker at {below} accepts {feature:?}'s tree\n{printed}"
            ))
        } else {
            Ok(())
        };
    }
    let json = fcs_record_at(&printed, below);
    let diagnostics = fcs_all_diagnostics(&json, &printed);
    let expected = feature.not_available_message(below);
    if diagnostics
        .iter()
        .any(|(_, message, _)| message.contains(&expected))
    {
        Ok(())
    } else {
        Err(format!(
            "FCS at {below} does not reject {feature:?} with {expected:?}: {diagnostics:?}\n{printed}"
        ))
    }
}

/// A gate's check, run by [`gate_is_exact`].
type GateCase = fn() -> Result<(), String>;

/// Each gate's check, one per feature a [`Version`] gates.
fn cases() -> Vec<(LanguageFeature, GateCase)> {
    vec![
        (LanguageFeature::AccessorFunctionShorthand, || {
            // `ss |> Seq.map _.Length`, so `_` has a type when it is read.
            let map = Expr::App {
                func: Box::new(Expr::Name(LongIdent(Vec1::new(
                    ident("Seq"),
                    vec![ident("map")],
                )))),
                arg: Box::new(Expr::DotLambda {
                    gate: Available,
                    path: LongIdent::single(ident("Length")),
                }),
            };
            let pipe = Operator::new("|>")
                .ok()
                .and_then(InfixOperator::new)
                .expect("an infix operator");
            gate_is_exact::<V8_0>(
                LanguageFeature::AccessorFunctionShorthand,
                &let_x(Expr::Infix {
                    op: pipe,
                    lhs: Box::new(name("ss")),
                    rhs: Box::new(map),
                }),
            )
        }),
        (LanguageFeature::AndBang, || {
            let and = AndBang {
                gate: Available,
                pat: var("y"),
                value: name("b"),
            };
            gate_is_exact::<V5_0>(
                LanguageFeature::AndBang,
                &let_x(computation(Comp {
                    init: vec![CompItem::LetBang(LetBang {
                        gate: Available,
                        pat: var("x"),
                        value: name("a"),
                        ands: vec![and],
                    })],
                    last: ret(),
                })),
            )
        }),
        (LanguageFeature::WhileBang, || {
            gate_is_exact::<V8_0>(
                LanguageFeature::WhileBang,
                &let_x(computation(Comp::stmt(Stmt::WhileBang {
                    gate: Available,
                    bang: Available,
                    cond: name("c"),
                    body: Box::new(Comp::stmt(Stmt::DoBang {
                        gate: Available,
                        expr: name("u"),
                    })),
                }))),
            )
        }),
        (LanguageFeature::ImplicitYield, || {
            // A parenthesised `if` in a comprehension.
            let paren = StmtExpr::new(Expr::IfThenElse {
                cond: Box::new(name("c")),
                then_branch: Box::new(name("u")),
                else_branch: Some(Box::new(name("u"))),
            })
            .expect("4.7 takes a parenthesised statement in a list");
            gate_is_exact::<V4_7>(
                LanguageFeature::ImplicitYield,
                &let_x(list(Comp {
                    init: vec![CompItem::Stmt(Stmt::Expr(paren))],
                    last: Stmt::Yield(name("e")),
                })),
            )
        }),
        (LanguageFeature::TryWithInSeqExpression, || {
            gate_is_exact::<V8_0>(
                LanguageFeature::TryWithInSeqExpression,
                &let_x(list(Comp::stmt(Stmt::TryWith {
                    gate: Available,
                    body: Box::new(Comp::stmt(Stmt::Yield(name("e")))),
                    clauses: Vec1::new(
                        CompClause {
                            pat: var("p"),
                            guard: None,
                            body: Comp::stmt(Stmt::Yield(name("e"))),
                        },
                        Vec::new(),
                    ),
                }))),
            )
        }),
        (
            LanguageFeature::NonVariablePatternsToRightOfAsPatterns,
            || {
                // `match a with (_) as (_) -> ()`.
                let alias = AliasPat::new(Available, Pat::Wildcard).expect("not a variable");
                gate_is_exact::<V6_0>(
                    LanguageFeature::NonVariablePatternsToRightOfAsPatterns,
                    &let_x(Expr::Match {
                        scrutinee: Box::new(name("a")),
                        clauses: Vec1::new(
                            MatchClause {
                                pat: Pat::As {
                                    pat: Box::new(Pat::Wildcard),
                                    alias: AsAlias::Pat(alias),
                                },
                                guard: None,
                                result: Expr::Const(Const::Unit),
                            },
                            Vec::new(),
                        ),
                    }),
                )
            },
        ),
        (LanguageFeature::UseBangBindingValueDiscard, || {
            gate_is_exact::<V10_0>(
                LanguageFeature::UseBangBindingValueDiscard,
                &let_x(computation(Comp {
                    init: vec![CompItem::UseBang(UseBang {
                        gate: Available,
                        name: UseName::Discard(Available),
                        value: name("v"),
                    })],
                    last: ret(),
                })),
            )
        }),
    ]
}

#[test]
fn every_gate_has_a_case() {
    let mut gated: Vec<_> = Preview::GATES.iter().map(|&(f, _)| f).collect();
    let mut covered: Vec<_> = cases().into_iter().map(|(f, _)| f).collect();
    gated.sort_by_key(|f| format!("{f:?}"));
    covered.sort_by_key(|f| format!("{f:?}"));
    assert_eq!(gated, covered);
}

#[test]
fn every_gate_is_rejected_below_its_version() {
    let failures: Vec<String> = cases()
        .into_iter()
        .filter_map(|(feature, case)| {
            on_deep_stack(case)
                .err()
                .map(|e| format!("{feature:?}: {e}"))
        })
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
