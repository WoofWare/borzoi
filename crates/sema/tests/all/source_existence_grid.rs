//! The hand-written grid of producer projects `source_existence_diff`
//! grades: the skeleton's forms combined, nested, repeated and named as one
//! cell per shape, each verdict pinned in
//! `tests/manifests/source_existence_diff.txt`.

use borzoi_oracle_harness::manifest::Manifest;
use borzoi_oracle_harness::project_graph::Target;
use borzoi_sema::ProviderReferences;

use crate::common::corpus_manifest::{check_manifest, regenerate};
use crate::source_existence_diff::{Cell, grade_cells};

fn one(name: &str, text: &str) -> Cell {
    Cell::new(name, &[("Lib.fs", text)])
}

pub fn cells() -> Vec<Cell> {
    vec![
        // Headers.
        one("namespace", "namespace N\ntype T = { X: int }\n"),
        one(
            "namespace_dotted_and_fragments",
            "namespace A.B.C\ntype T = int * int\nnamespace A.D\ntype U = { Y: int }\nnamespace A.B.C\ntype V = | V1 | V2\n",
        ),
        one("namespace_empty", "namespace Empty.Inner\n"),
        one(
            "namespace_rec",
            "namespace rec R\ntype A = { B: B option }\ntype B = { A: A }\n",
        ),
        one(
            "namespace_global",
            "namespace global\ntype TopType = { X: int }\nmodule TopModuleless =\n    let x = 1\n",
        ),
        Cell::new(
            "namespace_two_files",
            &[
                ("A.fs", "namespace Shared.Ns\ntype First = int\n"),
                ("B.fs", "namespace Shared.Ns\ntype Second = string\n"),
            ],
        ),
        one(
            "module_header",
            "module Top.Level.Mod\nlet x = 1\ntype Inner = { A: int }\n",
        ),
        one(
            "module_header_single",
            "module Single\ntype T = { X: int }\n",
        ),
        // Modules.
        one(
            "module_nested_deep",
            "namespace Deep\nmodule L1 =\n    module L2 =\n        module L3 =\n            module L4 =\n                type Bottom = { X: int }\n",
        ),
        one(
            "module_rec",
            "module rec RecMod\ntype A = { B: B }\nand B = { A: A option }\nmodule Inner =\n    type C = int\n",
        ),
        one(
            "module_abbreviation",
            "namespace N\nmodule Real =\n    let x = 1\nmodule Alias = Real\n",
        ),
        one(
            "module_beside_type_of_its_name",
            "namespace N\ntype Thing = { X: int }\nmodule Thing =\n    let make () = { X = 1 }\n",
        ),
        one(
            "module_beside_exception_of_its_name",
            "namespace N\nexception Oops of string\nmodule Oops =\n    let raiseIt () = raise (Oops \"x\")\n",
        ),
        one(
            "module_empty_begin_end",
            "module Outer\nmodule Inner = begin end\nmodule Other = begin end\n",
        ),
        // Accessibility (read as public: no entity question reads it).
        one(
            "access",
            "namespace Acc\nmodule private Priv =\n    type InPriv = int\nmodule internal Int =\n    type internal I = { X: int }\n    type private P = { Y: int }\ntype private PT() = member _.X = 1\nexception internal IE of string\n",
        ),
        // Every type kind.
        one(
            "type_kinds",
            "namespace Kinds\ntype Cls(x: int) = member _.X = x\ntype Strukt = struct val X: int end\ntype IExplicit = interface abstract M: int end\ntype IInferred = abstract M: unit -> int\ntype Rec = { R: int }\ntype Uni = | U1 | U2 of int\ntype En = | A = 1 | B = 2\ntype Del = delegate of int -> int\ntype Empty = class end\n",
        ),
        one(
            "type_generic",
            "namespace Gen\ntype G<'a> = { V: 'a }\ntype G2<'a, 'b> = | P of 'a * 'b\ntype Post<'a> = 'a * 'a\ntype C<'a when 'a: equality>(x: 'a) = member _.X = x\n",
        ),
        one(
            "type_and_group",
            "namespace Group\ntype A = { B: B option }\nand B = { A: A }\nand C = int\n",
        ),
        one(
            "type_duplicate_name",
            "namespace Dup\ntype T = { X: int }\ntype T = { Y: int }\n",
        ),
        // Abbreviations.
        one(
            "abbreviations",
            "namespace Abbr\ntype I = int\ntype F = int -> string\ntype Tup = int * string\ntype Arr = int[]\ntype V<'a> = 'a\ntype Anon = {| X: int |}\ntype P = (string)\n",
        ),
        one(
            "abbreviation_of_every_fsharp_core_name",
            "namespace Core\ntype A1 = obj\ntype A2 = exn\ntype A3 = string\ntype A4 = bool\ntype A5 = unit\ntype A6 = decimal\ntype A7 = float\ntype A8 = int64\ntype A9 = byte\ntype A10 = bigint\ntype A11 = nativeint\n",
        ),
        // Exceptions.
        one(
            "exceptions",
            "namespace Exn\nexception E1\nexception E2 of string\nexception E3 of code: int * msg: string\nexception E4 = E2\nexception E5 of int with\n    member e.Code = 1\nend\n",
        ),
        // Augmentations.
        one(
            "augmentations",
            "namespace Aug\ntype R = { X: int }\ntype R with\n    member r.Y = r.X\nmodule M =\n    type R with\n        member r.Z = r.X\n",
        ),
        one(
            "augmentation_of_a_type_nowhere",
            "namespace AugNowhere\ntype Nowhere with\n    member x.M = 1\n",
        ),
        // Names.
        one(
            "names_backticked",
            "namespace Ticks\ntype ``My Type`` = { X: int }\nmodule ``a-b`` =\n    type ``1st`` = int\nexception ``Odd one`` of string\n",
        ),
        one(
            "names_unicode",
            "namespace Ünïcödé\ntype Élan = { X: int }\ntype Ωmega = int\nmodule Мир =\n    type Tуpe = int\n",
        ),
        one(
            "names_colliding",
            "namespace System\ntype String = { Fake: int }\nmodule List =\n    let x = 1\nmodule Option =\n    type Option<'a> = | Some of 'a\n",
        ),
        one(
            "names_fsharp_core",
            "namespace Microsoft.FSharp.Core\ntype Mine = int\nmodule Operators2 =\n    let x = 1\n",
        ),
        one(
            "names_ending_in_module_on_types",
            "namespace Ends\ntype ThingModule = { X: int }\nexception OopsModule of string\n",
        ),
        // Attributes the walk reads: on what declares no entity.
        one(
            "attributes_off_entities",
            "namespace Attrs\ntype R = { [<System.Obsolete>] X: int }\ntype U = | [<System.Obsolete>] C of int\nmodule M =\n    [<Literal>]\n    let L = 1\n    [<System.Obsolete>]\n    let f ([<System.ParamArray>] xs: int[]) = xs\n",
        ),
        one(
            "attributes_on_members",
            "namespace MemberAttrs\ntype T [<System.Obsolete>] (x: int) =\n    [<DefaultValue>]\n    val mutable y: int\n    [<System.Obsolete>]\n    let z = x\n    [<System.Obsolete>]\n    member _.M = z\n    member _.P with [<System.Obsolete>] get () = 1\ntype E = | [<System.Obsolete>] One = 1\ntype G<[<Measure>] 'u> = { V: float<'u> }\n",
        ),
        // Executables.
        {
            let mut cell = one("exe", "module Program\n[<EntryPoint>]\nlet main _ = 0\n");
            cell.graph.target = Target::Exe;
            cell
        },
        // A possible type provider declines a named target.
        Cell {
            providers: ProviderReferences::Possible,
            ..one("provider_possible", "namespace Prov\ntype A = int\n")
        },
        // Producers FCS rejects, whose recovered signature is graded.
        one(
            "fcs_rejects_a_value",
            "namespace Fails\ntype T = { X: int }\nmodule M =\n    let x: int = \"s\"\n",
        ),
    ]
}

#[test]
fn source_rows_hold_fcs_facts_over_the_grid() {
    let cells = cells();
    let (entries, failures) = grade_cells(&cells);
    assert!(
        failures.is_empty(),
        "{} failures:\n{}",
        failures.len(),
        failures.join("\n\n")
    );
    let manifest = Manifest::from_keyed(entries).expect("well-formed entries");
    check_manifest(
        "source_existence_diff",
        &manifest,
        &regenerate("source_existence_grid::source_rows_hold_fcs_facts_over_the_grid"),
    );
}
