//! The receiver's type at a member access
//! ([`InferredFile::receiver_type_at`]): what FCS knows of the receiver when
//! it looks the member up, which is what dot-completion offers members of
//! (#662's D4). It is keyed by the dot after the receiver, so it is there
//! for every segment of a chain and for an access whose member is not yet
//! written (`s.`), and it is recorded only where the receiver's type is
//! known at the access, never from what a later use makes of it.
//!
//! These pin the shapes; [`super::infer_suffix_irrelevance`] holds the
//! record to not depending on what follows the access, and
//! [`super::infer_entry_order_diff`]'s alphabet holds it to FCS reporting no
//! FS0072 (a lookup on a receiver it does not know) at a recorded access —
//! for accesses whose member is written only. Under a missing member FCS
//! reports nothing (`DiscardAfterMissingQualificationAfterDot`), so the
//! receivers of a recovered declaration are held by the cases here and by
//! the alphabet's member-deletion property
//! (`deleting_a_member_keeps_the_receiver_and_isolates_the_declaration`),
//! not by FCS.

use std::collections::BTreeMap;

use borzoi_cst::parser::parse;
use borzoi_cst::syntax::{AstNode, ImplFile, TextRange};
use borzoi_sema::{
    InferredFile, PrecedingTypes, ProjectItems, ResolvedFile, SyntaxRecovery, infer_file,
    resolve_file,
};

use crate::common::full_bcl_env;

fn infer(src: &str) -> (ResolvedFile, InferredFile) {
    let parsed = parse(src);
    let recovery = SyntaxRecovery::of(&parsed);
    let file = ImplFile::cast(parsed.root).expect("impl file");
    let env = full_bcl_env();
    let resolved = resolve_file(&file, &ProjectItems::default(), env, &recovery);
    let inferred = infer_file(&file, &resolved, env, &PrecedingTypes::default());
    (resolved, inferred)
}

/// Every recorded receiver type, by the offset of the dot it is keyed by.
fn receivers(inferred: &InferredFile) -> BTreeMap<usize, String> {
    inferred
        .receiver_types()
        .map(|(dot, ty)| {
            assert_eq!(
                u32::from(dot.len()),
                1,
                "a receiver is keyed by its one-character dot"
            );
            (u32::from(dot.start()) as usize, ty.render(full_bcl_env()))
        })
        .collect()
}

/// The offset of the last `.` of `needle`, which occurs exactly once in
/// `src`.
fn dot_of(src: &str, needle: &str) -> usize {
    let at = src.find(needle).expect("the needle occurs");
    assert_eq!(
        src.rfind(needle),
        Some(at),
        "`{needle}` occurs once in {src:?}"
    );
    at + needle.rfind('.').expect("the needle holds a dot")
}

/// The receiver type recorded at the last dot of `needle`.
fn receiver_at(src: &str, needle: &str) -> Option<String> {
    let (_, inferred) = infer(src);
    let dot = dot_of(src, needle);
    let range = TextRange::at((dot as u32).into(), 1.into());
    let looked_up = inferred
        .receiver_type_at(range)
        .map(|t| t.render(full_bcl_env()));
    assert_eq!(
        looked_up.as_ref(),
        receivers(&inferred).get(&dot),
        "the lookup and the table agree"
    );
    looked_up
}

const STRING: &str = "System.String";

#[test]
fn an_annotated_parameter_before_a_trailing_dot() {
    let src = "module M\nlet f (s: string) = s.\n";
    assert_eq!(receiver_at(src, "s.").as_deref(), Some(STRING));
}

#[test]
fn a_parameter_fixed_before_the_access() {
    // `g x` fixes `x : string` before FCS reaches `x.`.
    let src = "module M\nlet g (t: string) = 0\nlet f x = (g x, x.)\n";
    assert_eq!(receiver_at(src, "x.)").as_deref(), Some(STRING));
    let src = "module M\nlet g (t: string) = 0\nlet f x = (g x, x.Le)\n";
    assert_eq!(receiver_at(src, "x.Le").as_deref(), Some(STRING));
}

#[test]
fn a_parameter_fixed_only_after_the_access_has_none() {
    // FCS looks `Le` up on a receiver it does not know yet: FS0072. What `g x`
    // makes of `x` afterwards is not the receiver's type at the access.
    let src = "module M\nlet g (t: string) = 0\nlet f x = (x.Le, g x)\n";
    assert_eq!(receiver_at(src, "x.Le"), None);
    let src = "module M\nlet g (t: string) = 0\nlet f x = (x., g x)\n";
    assert_eq!(receiver_at(src, "x.,"), None);
}

#[test]
fn a_local_value_before_a_trailing_dot() {
    let src = "module M\nlet f () = let s = \"hi\" in s.\n";
    assert_eq!(receiver_at(src, "s.").as_deref(), Some(STRING));
}

#[test]
fn a_forward_reference_in_a_recursive_module_has_none() {
    let src = "module rec M\nlet a () = b.Length\nlet b = \"hi\"\n";
    assert_eq!(receiver_at(src, "b.Length"), None);
    let src = "module rec M\nlet a () = b.\nlet b = \"hi\"\n";
    assert_eq!(receiver_at(src, "b."), None);
}

#[test]
fn a_forward_reference_in_a_let_rec_group_has_none() {
    let src = "module M\nlet rec a () = b.Length\nand b = \"hi\"\n";
    assert_eq!(receiver_at(src, "b.Length"), None);
    let src = "module M\nlet rec a () = b.\nand b = \"hi\"\n";
    assert_eq!(receiver_at(src, "b."), None);
}

#[test]
fn a_forward_reference_to_a_later_member_has_none() {
    let src =
        "module M\ntype C() =\n    member this.P = this.Q.Length\n    member this.Q = \"hi\"\n";
    assert_eq!(receiver_at(src, "this.Q."), None);
    let src = "module M\ntype C() =\n    member this.P = this.Q.\n    member this.Q = \"hi\"\n";
    assert_eq!(receiver_at(src, "this.Q."), None);
}

#[test]
fn a_trailing_dot_in_function_position_has_its_receiver() {
    // `s.Insert(0, "z")` with its member deleted: the recovered `s.` is the
    // callee of an application.
    let src = "module M\nlet f (s: string) = ignore (s.(0, \"z\"))\n";
    assert_eq!(receiver_at(src, "s.").as_deref(), Some(STRING));
}

#[test]
fn every_segment_of_a_chain_has_its_receiver() {
    let src = "module M\nlet f (s: string) = s.Length.CompareTo(1)\n";
    assert_eq!(receiver_at(src, "s.").as_deref(), Some(STRING));
    assert_eq!(
        receiver_at(src, "s.Length.").as_deref(),
        Some("System.Int32")
    );
    let src = "module M\nlet f (s: string) = s.Length.\n";
    assert_eq!(
        receiver_at(src, "s.Length.").as_deref(),
        Some("System.Int32")
    );
}

#[test]
fn an_expression_receiver_and_a_method_call_result() {
    let src = "module M\nlet n = \"hi\".Length\n";
    assert_eq!(receiver_at(src, "\".").as_deref(), Some(STRING));
    let src = "module M\nlet f (s: string) = (s).Le\n";
    assert_eq!(receiver_at(src, ").").as_deref(), Some(STRING));
    let src = "module M\nlet f (s: string) = s.ToUpperInvariant().Length\n";
    assert_eq!(receiver_at(src, "s.").as_deref(), Some(STRING));
    assert_eq!(receiver_at(src, "().").as_deref(), Some(STRING));
}

#[test]
fn a_damaged_declaration_records_only_receivers_up_to_its_recovery() {
    // The first recovery is the trailing dot; the access after it, and every
    // declaration after it, are past what the parse can be shown to share
    // with FCS's.
    let src = "module M\nlet f (s: string) = (s., s.Length)\nlet h (t: string) = t.Length\n";
    let (resolved, inferred) = infer(src);
    let got = receivers(&inferred);
    let first = dot_of(src, "s.,");
    assert_eq!(
        got,
        BTreeMap::from([(first, STRING.to_string())]),
        "only the receiver at the recovery: {got:?}"
    );
    // Nothing else of the damaged declaration is published: it was walked for
    // its receivers alone.
    assert!(
        inferred.types().is_empty(),
        "no node of a damaged declaration: {:?}",
        inferred.types()
    );
    assert!(
        inferred.def_types().is_empty(),
        "no binder of a damaged declaration: {:?}",
        inferred
            .def_types()
            .keys()
            .map(|d| resolved.def(*d).range)
            .collect::<Vec<_>>()
    );
    assert!(inferred.member_resolutions().is_empty());
    assert!(
        inferred.incompleteness().is_empty(),
        "a damaged declaration takes no census entry: {:?}",
        inferred.incompleteness()
    );
}

#[test]
fn a_clean_declaration_before_a_damaged_one_publishes_as_before() {
    let clean = "module M\nlet n (t: string) = t.Length\n";
    let damaged = format!("{clean}let f (s: string) = s.\n");
    let (_, alone) = infer(clean);
    let (_, both) = infer(&damaged);
    assert_eq!(alone.types(), both.types());
    assert_eq!(alone.def_types(), both.def_types());
    assert_eq!(alone.member_resolutions(), both.member_resolutions());
    assert_eq!(alone.incompleteness(), both.incompleteness());
    let mut want = receivers(&alone);
    want.insert(dot_of(&damaged, "s."), STRING.to_string());
    assert_eq!(receivers(&both), want);
}

#[test]
fn a_file_past_the_type_budget_records_no_receiver() {
    // The receiver is ground at its access, but the read-off of the
    // doubling tuples after it passes the budget: the file publishes
    // nothing, receivers included, rather than reading a table whose answers
    // are no longer answers.
    let mut src = "module M\nlet n = \"hi\".Length\nlet a0 = 0\n".to_string();
    for k in 1..=12 {
        src.push_str(&format!("let a{k} = (a{p}, a{p})\n", p = k - 1));
    }
    let (_, inferred) = infer(&src);
    assert!(
        inferred.type_budget_exceeded().is_some(),
        "the family reaches the budget"
    );
    assert!(
        receivers(&inferred).is_empty(),
        "{:?}",
        receivers(&inferred)
    );
}

#[test]
fn a_declaration_after_a_recovery_records_nothing() {
    // The first recovery is not a trailing dot, so no declaration from it on
    // is walked at all.
    let src = "module M\nlet a = (1\nlet f (s: string) = s.Length\n";
    let (_, inferred) = infer(src);
    assert!(
        receivers(&inferred).is_empty(),
        "{:?}",
        receivers(&inferred)
    );
}
