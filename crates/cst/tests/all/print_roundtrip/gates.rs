//! Each version gate held to FCS from below.
//!
//! The generated trees show a gate is not too *low*: a tree at a version
//! without the feature cannot hold the construct, and one at a version with it
//! is checked at that version. These show it is not too *high*: the
//! construct, printed, is rejected by FCS at the version just below the gate,
//! with the FS3350 message naming the feature. A gate on a construct only FCS's
//! checker refuses below its version (`and!`) has nothing for this parse-only
//! oracle to see from below: its case checks the round trip at its version,
//! and that the feature table calls it checker-only, so a gate the parser
//! comes to enforce gets the full check.

use borzoi_cst::language_version::FcsStage;
use borzoi_print::names::{Ident, LongIdent, ValueName};
use borzoi_print::print_impl_file;
use borzoi_print::tree::{
    AndBang, BangKind, Binding, BindingHead, Comp, Expr, ImplFile, LetBindings, ModuleDecl, Pat,
    Stmt,
};
use borzoi_print::vec::Vec1;
use borzoi_print::version::{
    Available, LanguageFeature, LanguageVersion, Preview, V5_0, V8_0, Version,
};

use super::{fcs_record_at, round_trips_at};
use crate::common::fcs_all_diagnostics;

fn ident(s: &str) -> Ident {
    Ident::new(s).expect("an identifier")
}

/// `let x = e`.
fn let_x<V: Version>(e: Expr<V>) -> ImplFile<V> {
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

/// `tree`, which uses `feature` and is at its version, round-trips there and
/// at `preview`, and, if FCS's parser enforces `feature`, FCS rejects it one
/// version earlier for want of it.
fn gate_is_exact<V: Version>(feature: LanguageFeature, tree: &ImplFile<V>) -> Result<(), String> {
    assert_eq!(V::LANGUAGE, feature.introduced(), "{feature:?}'s tree");
    round_trips_at(tree, &[V::LANGUAGE, LanguageVersion::MAX])?;
    let parser_enforces = feature
        .fcs_stages()
        .iter()
        .any(|s| matches!(s, FcsStage::Lex | FcsStage::LexFilter | FcsStage::Parse));
    if !parser_enforces {
        assert_eq!(
            feature.fcs_stages(),
            [FcsStage::Check],
            "{feature:?} is enforced by neither FCS's parser nor only its checker"
        );
        return Ok(());
    }
    let below = *LanguageVersion::NUMBERED
        .iter()
        .rev()
        .find(|&&v| v < V::LANGUAGE)
        .expect("a version below the gate");
    let printed = print_impl_file(tree);
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
            let path = LongIdent(Vec1::new(ident("A"), vec![ident("B")]));
            gate_is_exact::<V8_0>(
                LanguageFeature::AccessorFunctionShorthand,
                &let_x(Expr::DotLambda {
                    gate: Available,
                    path,
                }),
            )
        }),
        (LanguageFeature::AndBang, || {
            let and = AndBang {
                gate: Available,
                pat: Pat::Name(LongIdent::single(ident("y"))),
                value: name("b"),
            };
            gate_is_exact::<V5_0>(
                LanguageFeature::AndBang,
                &let_x(computation(Comp::Bang {
                    kind: BangKind::Let,
                    pat: Pat::Name(LongIdent::single(ident("x"))),
                    value: name("a"),
                    ands: vec![and],
                    rest: Box::new(Comp::Last(Stmt::Return(name("x")))),
                })),
            )
        }),
        (LanguageFeature::WhileBang, || {
            gate_is_exact::<V8_0>(
                LanguageFeature::WhileBang,
                &let_x(computation(Comp::Last(Stmt::WhileBang {
                    gate: Available,
                    cond: name("c"),
                    body: Box::new(Comp::Last(Stmt::DoBang(name("a")))),
                }))),
            )
        }),
    ]
}

fn name<V: Version>(s: &str) -> Expr<V> {
    Expr::Name(LongIdent::single(ident(s)))
}

/// `async { body }`.
fn computation<V: Version>(body: Comp<V>) -> Expr<V> {
    Expr::Computation {
        builder: Box::new(name("async")),
        body: Box::new(body),
    }
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
        .filter_map(|(feature, case)| case().err().map(|e| format!("{feature:?}: {e}")))
        .collect();
    assert!(failures.is_empty(), "{}", failures.join("\n\n"));
}
