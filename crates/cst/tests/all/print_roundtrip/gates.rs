//! Each version gate held to FCS from below.
//!
//! The generated trees show a gate is not too *low*: a tree at a version
//! without the feature cannot hold the construct, and one at a version with it
//! is checked at that version. These show it is not too *high*: the
//! construct, printed, is rejected by FCS at the version just below the gate,
//! with the FS3350 message naming the feature. A gate on a construct only FCS's
//! checker refuses below its version has nothing for this parse-only oracle to
//! see, so every gate here must be one FCS's parser enforces.

use borzoi_cst::language_version::FcsStage;
use borzoi_print::names::{Ident, LongIdent, ValueName};
use borzoi_print::print_impl_file;
use borzoi_print::tree::{Binding, BindingHead, Expr, ImplFile, LetBindings, ModuleDecl};
use borzoi_print::vec::Vec1;
use borzoi_print::version::{Available, LanguageFeature, LanguageVersion, Preview, V8_0, Version};

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
/// at `preview`, and FCS rejects it one version earlier for want of `feature`.
fn gate_is_exact<V: Version>(feature: LanguageFeature, tree: &ImplFile<V>) -> Result<(), String> {
    assert_eq!(V::LANGUAGE, feature.introduced(), "{feature:?}'s tree");
    assert!(
        feature
            .fcs_stages()
            .iter()
            .any(|s| matches!(s, FcsStage::Lex | FcsStage::LexFilter | FcsStage::Parse)),
        "{feature:?} is not one FCS's parser enforces"
    );
    round_trips_at(tree, &[V::LANGUAGE, LanguageVersion::MAX])?;
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
    vec![(LanguageFeature::AccessorFunctionShorthand, || {
        let path = LongIdent(Vec1::new(ident("A"), vec![ident("B")]));
        gate_is_exact::<V8_0>(
            LanguageFeature::AccessorFunctionShorthand,
            &let_x(Expr::DotLambda {
                gate: Available,
                path,
            }),
        )
    })]
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
