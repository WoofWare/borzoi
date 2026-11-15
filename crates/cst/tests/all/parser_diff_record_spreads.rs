//! Differential test (`parser::parse` vs FCS): F# 11's record spreads
//! (`RecordSpreads`, dotnet/fsharp#18927). FCS parses them at every version
//! and gates them in its type checker, so these trees are the same at every
//! version; `parser_diff_feature_gates` and sema's
//! `check_time_gates_report_what_fcs_checks_report` hold the gate.
//!
//! - In a record expression, `{ ...e; F = x }`: each spread is a
//!   `SynExprRecordFieldOrSpread.Spread` among the fields, in source order
//!   (`recdExprCore`, `recdBinding`), also after `with` and `inherit`.
//! - In an anonymous record, `{| ...e; F = x |}` (`braceBarExprCore`).
//! - In a record type, `type R = { ...T; F: int }`
//!   (`SynFieldOrSpread.Spread(SynTypeSpread …)`, `recdFieldDecl`).
//!
//! And FCS's error forms: a spread with no source (`{ ... }`, a bare `...`
//! binding, FS3899; a bare `...` in a record type, FS3900), a spread before
//! `with` (`{ ...e with F = x }`, FS3903, which keeps `e` as the copy source),
//! and `...e` anywhere else (FS3902, `ArbitraryAfterError`).

use crate::common::recovery::assert_recovered_trees_agree;
use crate::common::{
    assert_asts_match, assert_asts_match_allow_errors, assert_asts_match_with_diagnostic,
    assert_sig_asts_match,
};

/// FS3899, `parsMissingSpreadSrcExpr`.
const MISSING_SPREAD_SOURCE_EXPR: i64 = 3899;
/// FS3900, `parsMissingSpreadSrcTy`.
const MISSING_SPREAD_SOURCE_TYPE: i64 = 3900;
/// FS3902, `parsSpreadNotSupported`.
const SPREAD_NOT_SUPPORTED: i64 = 3902;
/// FS3903, `parsSpreadNotSupportedBeforeWith`.
const SPREAD_BEFORE_WITH: i64 = 3903;

#[test]
fn record_expression_spreads() {
    for src in [
        "let a = { ...r }\n",
        "let a = { ...r; X = 1 }\n",
        "let a = { X = 1; ...r }\n",
        "let a = { ...r; ...s }\n",
        "let a = { ...r; X = 1; ...s; Y = 2 }\n",
        "let a = { ...r; }\n",
        "let a = { ...f x; X = 1 }\n",
        "let a = { ...a + b; X = 1 }\n",
        "let a = { ...x.Y; Z = 2 }\n",
        "let a = { ...(f x); Z = 2 }\n",
        "let a = { ...r :> obj; Z = 1 }\n",
        "let a = { ...if c then a else b }\n",
        "let a = { ...{ ...r }; Z = 1 }\n",
        "let a = { ...{| A = 1 |} }\n",
        "let a = { ...r X = 1 }\n",
        "let a = { ... X = 1 }\n",
        "let a = { ...r }.X\n",
        "let a = seq { ...xs }\n",
        "let a =\n    { ...r\n      X = 1 }\n",
        "let a = {\n    ...r\n    X = 1 }\n",
        "let a = { ...\n  r }\n",
        "let a = { x with ...r; X = 1 }\n",
        "let a = { x with ...r }\n",
        "let a = { x with X = 1; ...r }\n",
        "let a =\n    { x with\n        ...r\n        X = 1 }\n",
        "let a = { inherit B(); ...r }\n",
        "let a = { inherit B(); X = 1; ...r }\n",
        "let f r = { ...r; X = fun y -> y }\n",
    ] {
        assert_asts_match(src);
    }
}

#[test]
fn anonymous_record_spreads() {
    for src in [
        "let a = {| ...r |}\n",
        "let a = {| ...r; X = 1 |}\n",
        "let a = {| X = 1; ...r |}\n",
        "let a = {| ...r; ...s |}\n",
        "let a = struct {| ...r |}\n",
        "let a = struct {| ...r; X = 1 |}\n",
        "let a = {| x with ...r |}\n",
        "let a = {| x with ...r; X = 1 |}\n",
        "let a =\n    {| ...r\n       X = 1 |}\n",
        "let a = {| ...f x; X = 1 |}\n",
    ] {
        assert_asts_match(src);
    }
}

#[test]
fn record_type_spreads() {
    for src in [
        "type R = { ...T; X: int }\n",
        "type R = { X: int; ...T<int> }\n",
        "type R = { ...T }\n",
        "type R = { ...T; ...U }\n",
        "type R = { ...{| A: int |} }\n",
        "type R = { ...T * U }\n",
        "type R = { ...T -> int }\n",
        "type R = private { ...T }\n",
        "type R = { ...T; }\n",
        "type R = { ...\n  T }\n",
        "type R =\n    { ...T\n      X: int }\n",
        "type R<'a> = { ...T<'a>; mutable X: 'a }\n",
        "type R = { ...T; X: int }\nand S = { ...R }\n",
    ] {
        assert_asts_match(src);
    }
}

#[test]
fn signature_record_type_spreads() {
    for src in [
        "module M\ntype R = { ...T; X: int }\n",
        "module M\ntype R =\n    { X: int\n      ...T }\n",
    ] {
        assert_sig_asts_match(src);
    }
}

#[test]
fn spreads_without_a_source() {
    for src in [
        "let a = { ... }\n",
        "let a = { ...r; ... }\n",
        "let a = { x with ... }\n",
        "let a = {| ... |}\n",
        "let a = { ...r; ...; X = 1 }\n",
    ] {
        assert_asts_match_with_diagnostic(src, MISSING_SPREAD_SOURCE_EXPR);
    }
    for src in ["type R = { ... }\n", "type R = { ... ; X: int }\n"] {
        assert_asts_match_with_diagnostic(src, MISSING_SPREAD_SOURCE_TYPE);
    }
}

#[test]
fn spreads_before_with() {
    for src in [
        "let a = { ...r with X = 1 }\n",
        "let a = { ...r with }\n",
        "let a = { ...f x with X = 1; ...s }\n",
        "let a = { ...r with\n            X = 1 }\n",
        "let a = {| ...r with X = 1 |}\n",
    ] {
        assert_asts_match_with_diagnostic(src, SPREAD_BEFORE_WITH);
    }
}

#[test]
fn spreads_elsewhere() {
    for src in [
        "let a = ...x\n",
        "let a = ...\n",
        "let a = (...x)\n",
        "let a = (...)\n",
        "let a = [ ...xs ]\n",
        "let a = [ 1; ...xs ]\n",
        "let a = ...x, y\n",
        "let a = x, ...y\n",
        "let a = 1 + ...x\n",
        "let a = ...x |> f\n",
        "let a = ...x : int\n",
        "let a = ...x; 2\n",
        "let a = id (...x)\n",
        "let a = x.[...y]\n",
        "let a = { yield 1; ...xs }\n",
        "let a = { ...; X = 1 }\n",
        "match x with\n| _ -> ...y\n",
    ] {
        assert_asts_match_with_diagnostic(src, SPREAD_NOT_SUPPORTED);
    }
}

/// FCS's other errors around a spread: an attribute or `mutable` on a type
/// spread (FS0010 at the `...`), and a spread in an anonymous record type
/// (FS3244, which drops it).
#[test]
fn spread_recovery() {
    for src in [
        "let a = { ...r; yield 1 }\n",
        "let a = f ...x\n",
        "type R = { [<A>] ...T }\n",
        "type R = { mutable ...T }\n",
        "let f (x: {| ...T |}) = x\n",
        "let f (x: {| ...T; A: int |}) = x\n",
    ] {
        assert_recovered_trees_agree(&format!("module M\n{src}let after = 1\n"), 1);
    }
    assert_asts_match_allow_errors("let a = { ...r; yield 1 }\n");
}

/// A dotted field name in an anonymous record: FCS's parser accepts it
/// whether or not the record copies (`SynExprAnonRecordField` holds a
/// `SynLongIdent`); after a spread it updates a nested field.
#[test]
fn anonymous_record_dotted_fields() {
    for src in [
        "let a = {| ...r; Nested.B = 1 |}\n",
        "let a = {| ...o (); N.B = 4; ...p (); O.B = 5 |}\n",
    ] {
        assert_asts_match(src);
    }
}
