//! Differential test (`parser::parse` vs FCS): FSharp.Core's inline IL
//! `(# "instr" type (T) arg₀ … : retTy #)` in expression position, FCS's
//! `SynExpr.LibraryOnlyILAssembly(ilCode, typeArgs, args, retTy, _)`
//! (`pars.fsy` `inlineAssemblyExpr`). The type operand, the arguments and the
//! return type are compared; the instruction string is not, since FCS parses it
//! into IL instructions where our tree keeps the literal. FCS rejects the
//! `type (T)` operand in the files the oracle parses (FSharp.Core's
//! `prim-types.fs` uses it), so no case here has one.

use crate::common::assert_asts_match;

/// The bare retype: no instruction, one argument, a return type.
#[test]
fn diff_inline_il_retype() {
    assert_asts_match("let inline retype (x: 'T) : 'U = (# \"\" x : 'U #)\n");
}

/// Several curried arguments, in source order.
#[test]
fn diff_inline_il_curried_args() {
    assert_asts_match("let inline add (x: int) (y: int) : int = (# \"add\" x y : int #)\n");
}

/// Arguments that are themselves applications and parenthesised.
#[test]
fn diff_inline_il_compound_args() {
    assert_asts_match("let inline f x y = (# \"ceq\" (g x) y.Length : bool #)\n");
}

/// No return type, and the unit return `: ()`, both FCS's empty `retTy`.
#[test]
fn diff_inline_il_without_return_type() {
    assert_asts_match("let inline pop x = (# \"pop\" x #)\n");
    assert_asts_match("let inline pop x = (# \"pop\" x : () #)\n");
}

/// No arguments.
#[test]
fn diff_inline_il_without_args() {
    assert_asts_match("let inline empty () = (# \"ldnull\" : 'T list #)\n");
}

/// Inline IL in a static-optimization branch, the shape of
/// `fslib-extra-pervasives.fs`'s `print`.
#[test]
fn diff_inline_il_in_static_optimization_branch() {
    assert_asts_match(concat!(
        "let inline print (value: 'T) =\n",
        "    anyToString value\n",
        "    when 'T : string = write((# \"\" value : string #))\n",
        "    when 'T : char   = write((# \"\" value : char #))\n",
    ));
}
