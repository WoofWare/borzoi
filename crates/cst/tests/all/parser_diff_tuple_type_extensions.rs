//! Differential test (`parser::parse` vs FCS): tuple type extensions, F#
//! preview's `ExtensionConstraintSolutions` (dotnet/fsharp#19602). A type
//! definition's head may be a tuple type, `type (A * B) with …` (a
//! `System.Tuple` extension) or `type struct (A * B) with …` (a
//! `System.ValueTuple` one): FCS's `SynComponentInfo.synType` is then
//! `Paren(Tuple(false, …))` or `Tuple(true, …)` rather than a `LongIdent`
//! (`tyconNameAndTyparDecls`). FCS parses it at every version and gates it in
//! its type checker; sema's `check_time_gates_report_what_fcs_checks_report`
//! holds the gate.
//!
//! FCS accepts three recoveries without a diagnostic: a trailing `*` after the
//! first element (`(A *)`, `struct (A *)`, each with a `FromParseError` after
//! the `*`), and a lone element in the struct form (`struct (A)`, whose head
//! is `A`).

use crate::common::recovery::assert_recovered_trees_agree;
use crate::common::{assert_asts_match, assert_parse_verdicts_match, assert_sig_asts_match};

#[test]
fn tuple_type_extension_heads() {
    for src in [
        "type ('a & #seq<seq<int>> * 'b) with\n    member x.F = 1\n",
        "type (int * int) with\n    member x.F = 1\n",
        "type ('a * 'b) with\n    member x.F = 1\n",
        "type ('T1 * 'T2) with\n    static member inline (<*>) ((a, f), (b, x)) = (a, f x)\n",
        "type (int * int * string) with\n    member x.F = 1\n",
        "type ('a list * 'b option) with\n    member x.F = 1\n",
        "type (string | null * int) with\n    member x.F = 1\n",
        "type struct (int * int) with\n    member x.F = 1\n",
        "type struct ('a * 'b * 'c) with\n    member x.F = 1\n",
        "type private (int * int) with\n    member x.F = 1\n",
        "type internal struct (int * int) with\n    member x.F = 1\n",
        "type (int * int) =\n    member x.F = 1\n",
        "type ('T1 * 'T2)\n",
        "type (int * int)\nand (string * int) with\n    member x.F = 1\n",
        "type [<A>] (int * int) with\n    member x.F = 1\n",
    ] {
        assert_asts_match(src);
    }
}

/// FCS's silent recoveries.
#[test]
fn tuple_type_extension_head_recoveries() {
    for src in [
        "type ('T1 *)\n",
        "type ('T1 *) with\n    static member X = 1\n",
        "type struct (int *) with\n    member x.F = 1\n",
        "type struct (int) with\n    member x.F = 1\n",
    ] {
        assert_asts_match(src);
    }
}

#[test]
fn signature_tuple_type_extension_heads() {
    for src in [
        "module M\ntype (int * int) with\n    member F : int\n",
        "module M\ntype struct ('a * 'b) with\n    member F : int\n",
    ] {
        assert_sig_asts_match(src);
    }
}

/// Heads FCS rejects: a lone element without `struct`, an arrow, an empty
/// pair of parentheses.
#[test]
fn tuple_type_extension_head_errors() {
    for src in [
        "type (int -> int) with\n    member x.F = 1\n",
        "type (int) with\n    member x.F = 1\n",
        "type () with\n    member x.F = 1\n",
        "type (int * int *) with\n    member x.F = 1\n",
    ] {
        assert_recovered_trees_agree(&format!("module M\n{src}let after = 1\n"), 1);
    }
}

/// Every head the grid spells — an access modifier or none, `struct` or not,
/// first elements of every type shape a tuple element takes (an intersection
/// constraint among them, which a prefix typar list may also start with), the
/// tails FCS's `tupleOrQuotTypeElements` takes and the ones it does not, and a
/// `with` augmentation or an after-name access and a body — FCS's verdict,
/// and on what it accepts, its tree.
#[test]
fn tuple_type_extension_head_grid() {
    let (mut accepted, mut rejected) = (0, 0);
    for access in ["", "private "] {
        for kind in ["", "struct "] {
            for first in [
                "int",
                "'a",
                "'a list",
                "string | null",
                "'a & #seq<int>",
                "'a & #seq<seq<int>>",
                "'a & #seq<int * int>",
                "#seq<'a>",
                "int[]",
            ] {
                for tail in [
                    " * int",
                    " * 'b / 'c",
                    " *",
                    " * int *",
                    "",
                    " * (int -> int)",
                    " * int * string",
                ] {
                    for body in [
                        " with\n    member x.F = 1\n",
                        " private =\n    member x.F = 1\n",
                    ] {
                        let src = format!("type {access}{kind}({first}{tail}){body}");
                        if assert_parse_verdicts_match(&src) {
                            accepted += 1;
                        } else {
                            rejected += 1;
                        }
                    }
                }
            }
        }
    }
    assert!(
        accepted > 100 && rejected > 20,
        "the grid has degenerated: {accepted} accepted, {rejected} rejected"
    );
}
