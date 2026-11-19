//! The hand-written grid of producer projects `source_existence_diff` grades:
//! one cell per declaration form, attribute spelling, accessibility and
//! name shape, and the cells whose reference environment routes an
//! attribute name to a marker or away from one.

use borzoi_oracle_harness::project_graph::Target;
use borzoi_sema::Marker;

use crate::source_existence_diff::{Cell, Certificate, RefLib};

fn one(name: &str, text: &str) -> Cell {
    Cell::new(name, &[("Lib.fs", text)])
}

fn exe(mut cell: Cell) -> Cell {
    cell.target = Target::Exe;
    cell
}

fn with_defines(mut cell: Cell, defines: &[&str]) -> Cell {
    cell.defines = defines.iter().map(|d| (*d).to_owned()).collect();
    cell
}

fn with_ref(mut cell: Cell, name: &'static str, text: &str, certificate: Certificate) -> Cell {
    cell.refs.push(RefLib {
        name,
        files: vec![("Ref.fs".to_owned(), text.to_owned())],
    });
    cell.certificate = certificate;
    cell
}

pub fn cells() -> Vec<Cell> {
    let mut cells = vec![
        // Namespaces.
        one("namespace", "namespace N\ntype T = { X: int }\n"),
        one(
            "namespace_dotted_and_fragments",
            "namespace A.B.C\ntype T = int list\nnamespace A.D\ntype U = { Y: int }\nnamespace A.B.C\ntype V = | V1 | V2\n",
        ),
        one("namespace_empty", "namespace Empty.Inner\n"),
        one(
            "namespace_rec",
            "namespace rec R\ntype A = { B: B option }\ntype B = { A: A }\n",
        ),
        one(
            "namespace_global",
            "namespace global\ntype TopType = { X: int }\nmodule TopModule =\n    let x = 1\n",
        ),
        one(
            "namespace_shared_across_files",
            "namespace Shared\ntype First = int\n",
        ),
        Cell::new(
            "namespace_two_files",
            &[
                ("A.fs", "namespace Shared.Ns\ntype First = int\n"),
                ("B.fs", "namespace Shared.Ns\ntype Second = string\n"),
            ],
        ),
        // Modules.
        one(
            "module_header",
            "module Top.Level.Mod\nlet x = 1\ntype Inner = { A: int }\n",
        ),
        one(
            "module_nested_deep",
            "namespace Deep\nmodule L1 =\n    module L2 =\n        module L3 =\n            module L4 =\n                module L5 =\n                    type Bottom = { X: int }\n",
        ),
        one(
            "module_rec",
            "module rec RecMod\ntype A = { B: B }\nand B = { A: A option }\nmodule Inner =\n    type C = int\n",
        ),
        one(
            "module_abbreviation",
            "namespace N\nmodule Real =\n    let x = 1\nmodule Alias = Real\n",
        ),
        exe(one(
            "headerless",
            "let x = 1\ntype InHeaderless = { A: int }\n",
        )),
        exe(Cell::new(
            "headerless_last_of_two",
            &[
                ("First.fs", "module First\nlet a = 1\n"),
                (
                    "Main_Entry.fs",
                    "type InMain = { A: int }\nprintfn \"%d\" First.a\n",
                ),
            ],
        )),
        // Accessibility.
        one(
            "access",
            "namespace Acc\nmodule private Priv =\n    type InPriv = int\nmodule internal Int =\n    type internal I = { X: int }\n    type private P = { Y: int }\nmodule public Pub =\n    type public Q = { Z: int }\ntype private PT() = member _.X = 1\nexception internal IE of string\ntype C public () = member _.Y = 1\n",
        ),
        one(
            "access_inherited",
            "namespace AccIn\nmodule internal Int =\n    type Plain = { X: int }\n    exception PlainE of int\n    module Nested =\n        type Deeper = int\nmodule private Priv =\n    module public Pub =\n        type Q = { Z: int }\ntype internal T =\n    static member M = 1\n",
        ),
        // Every type kind.
        one(
            "type_kinds",
            "namespace Kinds\ntype Cls(x: int) = member _.X = x\n[<Struct>] type Str = { S: int }\ntype Strukt = struct val X: int end\ntype IExplicit = interface abstract M: int end\ntype IInferred = abstract M: unit -> int\n[<AbstractClass>] type Abs() = abstract M: int\ntype Rec = { R: int }\ntype Uni = | U1 | U2 of int\ntype En = | A = 1 | B = 2\ntype Del = delegate of int -> int\ntype Empty = class end\n",
        ),
        one(
            "type_generic",
            "namespace Gen\ntype G<'a> = { V: 'a }\ntype G2<'a, 'b> = | P of 'a * 'b\ntype Post<'a> = 'a list\n[<Measure>] type m\ntype Measured<[<Measure>] 'u> = { V: float<'u> }\n",
        ),
        one(
            "type_and_group",
            "namespace Group\ntype A = { B: B option }\nand B = { A: A }\nand [<AutoOpen>] C = int\n",
        ),
        // Abbreviations.
        one(
            "abbreviations",
            "namespace Abbr\ntype I = int\ntype L<'a> = 'a list\ntype F = int -> string\ntype Tup = int * string\ntype Self = Self\ntype Paren = (int)\n",
        ),
        one(
            "abbreviation_or_union",
            "namespace AbbrUnion\ntype Known = int\ntype ToKnown = Known\ntype Unknown = Nowhere\n",
        ),
        // Exceptions and measures.
        one(
            "exceptions",
            "namespace Exn\nexception E1\nexception E2 of string\nexception E3 of code: int * msg: string\nexception E4 = E2\n",
        ),
        one(
            "measures",
            "namespace Meas\n[<Measure>] type m\n[<Measure>] type s\n[<Measure>] type speed = m / s\n[<Microsoft.FSharp.Core.Measure>] type kg\n[<MeasureAttribute>] type g\n",
        ),
        // AutoOpen at every level and spelling.
        one(
            "auto_open_spellings",
            "namespace AO\n[<AutoOpen>]\nmodule A1 =\n    let x = 1\n[<AutoOpenAttribute>]\nmodule A2 =\n    let x = 1\n[<Microsoft.FSharp.Core.AutoOpen>]\nmodule A3 =\n    let x = 1\n[<FSharp.Core.AutoOpenAttribute>]\nmodule A4 =\n    let x = 1\nmodule Outer =\n    [<AutoOpen>]\n    module Inner =\n        [<AutoOpen>]\n        module Innermost =\n            let y = 1\n",
        ),
        one(
            "auto_open_header",
            "[<AutoOpen>]\nmodule AOHeader.Mod\nlet x = 1\n",
        ),
        one(
            "auto_open_type_and_abbreviation",
            "namespace AOT\n[<AutoOpen>]\ntype T() = static member M = 1\n[<AutoOpen>]\ntype Ab = System.String\n",
        ),
        one(
            "auto_open_with_other_attributes",
            "namespace AOO\n[<AutoOpen; RequireQualifiedAccess>]\nmodule Both =\n    let x = 1\n[<RequireQualifiedAccess>]\n[<AutoOpen>]\nmodule Two =\n    let x = 1\n[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]\nmodule Suffixed =\n    let x = 1\n",
        ),
        // Attribute targets.
        one(
            "attribute_targets",
            "namespace Targets\nopen System.Runtime.CompilerServices\n[<type: AutoOpen>]\ntype T() = static member M = 1\n[<type: CompiledName(\"Renamed\")>]\ntype U() = class end\ntype E =\n    [<return: Extension>]\n    static member R(s: string) = s\n    [<method: Extension>]\n    static member M(s: string) = s\nmodule Aug =\n    type System.String with\n        [<return: CompiledName(\"Q\")>]\n        member s.Orig() = 1\n",
        ),
        one(
            "attribute_target_assembly_on_type",
            "namespace TargetsAsm\n[<assembly: AutoOpen(\"TargetsAsm\")>]\ntype T() = static member M = 1\n[<assembly: AutoOpen(\"TargetsAsm\")>]\nmodule OnModule =\n    let x = 1\n",
        ),
        one(
            "attribute_target_module",
            "namespace TargetsModule\n[<module: AutoOpen>]\nmodule M =\n    let x = 1\n",
        ),
        // Codex round 1's shapes.
        one(
            "module_suffix_literal_flags",
            "namespace SuffixLit\nmodule C =\n    [<Literal>]\n    let flags = CompilationRepresentationFlags.ModuleSuffix\n[<CompilationRepresentation(C.flags)>]\nmodule Foo =\n    type Inner = { X: int }\n",
        ),
        one(
            "extension_cli_event",
            "namespace ExtEvent\nmodule M =\n    let ev = Event<int>()\n    type System.String with\n        [<CLIEvent>]\n        member s.Something = ev.Publish\n",
        ),
        one(
            "extension_measure_arity",
            "namespace ExtMeasure\ntype T<'a, [<Measure>] 'u> = { V: 'a }\nmodule M =\n    type T<'a, [<Measure>] 'u> with\n        member t.Info = 1\n",
        ),
        one(
            "auto_open_global_qualified",
            "namespace AOGlobal\n[<global.Microsoft.FSharp.Core.AutoOpen>]\nmodule M =\n    let x = 1\n",
        ),
        one(
            "augmentation_of_single_case_abbreviation",
            "module AugCase\nopen System.Runtime.CompilerServices\ntype T = Case\ntype T with\n    [<Extension>]\n    static member M(s: string) = s\n",
        ),
        one(
            "augmentation_of_local_exception",
            "module AugExn\nopen System.Runtime.CompilerServices\nexception E of string\ntype E with\n    [<Extension>]\n    static member M(s: string) = s\n",
        ),
        one(
            "extension_on_accessor",
            "module AccExt\nopen System.Runtime.CompilerServices\ntype T =\n    static member Foo with [<Extension>] get (x: string) = 1\n",
        ),
        Cell::new(
            "fsi_member_signature_getter",
            &[
                (
                    "Lib.fsi",
                    "namespace SigGet\nopen System.Runtime.CompilerServices\n[<Class>]\ntype T =\n    [<Extension>]\n    static member P: int\n",
                ),
                (
                    "Lib.fs",
                    "namespace SigGet\ntype T =\n    static member P = 1\n",
                ),
            ],
        ),
        Cell::new(
            "fsi_exception_members",
            &[
                (
                    "Lib.fsi",
                    "namespace SigExn\nopen System.Runtime.CompilerServices\nexception E of string\n    with\n        [<Extension>]\n        static member M: string -> string\n",
                ),
                (
                    "Lib.fs",
                    "namespace SigExn\nexception E of string\n    with\n        static member M(s: string) = s\n",
                ),
            ],
        ),
        one(
            "extension_constructors",
            "module CtorExt\nopen System.Runtime.CompilerServices\ntype T() =\n    [<Extension>]\n    new(s: string) = T()\n",
        ),
        one(
            "extension_class_let_and_interface",
            "module LetExt\nopen System.Runtime.CompilerServices\ntype T() =\n    [<Extension>]\n    static let f (s: string) = s\n    member _.G = f \"x\"\n",
        ),
        one(
            "extension_interface_implementation",
            "module IfaceExt\nopen System.Runtime.CompilerServices\ntype I =\n    abstract M: string -> string\ntype T() =\n    interface I with\n        [<Extension>]\n        member _.M(s) = s\n",
        ),
        one(
            "extension_val_field",
            "module FieldExt\nopen System.Runtime.CompilerServices\n[<Struct>]\ntype S =\n    [<Extension>]\n    val Field: int\n",
        ),
        one(
            "extension_destructuring_let",
            "module DestructExt\nopen System.Runtime.CompilerServices\n[<Extension>]\nlet (Some x) = Some 1\n",
        ),
        one(
            "exception_access_after_attribute",
            "namespace ExnAccess\n[<System.Obsolete>]\nexception internal Oops of string\n",
        ),
        one(
            "compiled_symbol",
            "namespace Compiled\n#if COMPILED\ntype Shown = { X: int }\n#else\ntype Hidden = { Y: int }\n#endif\n",
        ),
        // The module suffix.
        one(
            "module_suffix",
            "namespace Suffix\ntype Same = { X: int }\nmodule Same =\n    let x = 1\ntype Generic<'a> = { V: 'a }\nmodule Generic =\n    let y = 1\ntype MeasureG<[<Measure>] 'u> = { V: float<'u> }\nmodule MeasureG =\n    let z = 1\nmodule Lone =\n    let w = 1\ntype Later = int\n",
        ),
        one(
            "module_suffix_rec_exception",
            "module rec SuffixRecExn\nexception B of string\nmodule B =\n    let x = 1\n",
        ),
        one(
            "module_suffix_exception",
            "module SuffixExn\nexception B of string\nmodule B =\n    let x = 1\n",
        ),
        one(
            "module_suffix_rec_namespace",
            "namespace rec SuffixRecNs\ntype T = { X: int }\nmodule T =\n    let x = 1\nexception E of string\nmodule E =\n    let y = 1\n",
        ),
        one(
            "abbreviation_targets",
            "namespace AbbrT\nopen System\ntype Local = { X: int }\ntype ToLocal = Local\ntype ToCore = int\ntype ToObj = obj\ntype ToBcl = DateTime\n",
        ),
        one(
            "abbreviation_to_unknown_lower_case",
            "namespace AbbrLower\ntype ToLower = notatype\n",
        ),
        one(
            "module_suffix_later_type",
            "namespace SuffixLater\nmodule Thing =\n    let x = 1\ntype Thing = { X: int }\n",
        ),
        one(
            "module_suffix_augmentation_only",
            "module SuffixAug\ntype System.String with\n    member s.Len = s.Length\nmodule String =\n    let x = 1\n",
        ),
        // CompiledName.
        one(
            "compiled_name",
            "namespace CN\n[<CompiledName(\"RenamedType\")>]\ntype T() = member _.X = 1\n[<CompiledName(\"RenamedModule\")>]\nmodule M =\n    let x = 1\n[<CompiledNameAttribute(@\"Verbatim\")>]\ntype V = { A: int }\n",
        ),
        one(
            "compiled_name_exception_and_union",
            "namespace CNE\n[<CompiledName(\"RenamedExn\")>]\nexception E of string\n[<CompiledName(\"RenamedUnion\")>]\ntype U = | A | B\n[<CompiledName(\"RenamedAbbrev\")>]\ntype Ab = int\n",
        ),
        one(
            "extension_extern",
            "module ExtExtern\nopen System.Runtime.InteropServices\nopen System.Runtime.CompilerServices\n[<Extension; DllImport(\"libc\")>]\nextern int getpid()\n",
        ),
        // Signature pairs.
        Cell::new(
            "fsi_pair_hiding",
            &[
                (
                    "Lib.fsi",
                    "namespace Pair\ntype Shown = { X: int }\nmodule M =\n    val x: int\n",
                ),
                (
                    "Lib.fs",
                    "namespace Pair\ntype Shown = { X: int }\ntype Hidden = { Y: int }\nmodule M =\n    let x = 1\n    type HiddenInModule = int\n",
                ),
            ],
        ),
        Cell::new(
            "fsi_pair_access",
            &[
                (
                    "Lib.fsi",
                    "module PairAccess\ntype internal T =\n    new: unit -> T\n",
                ),
                ("Lib.fs", "module PairAccess\ntype T() = class end\n"),
            ],
        ),
        Cell::new(
            "fsi_pair_auto_open",
            &[
                (
                    "Lib.fsi",
                    "namespace PairAO\n[<AutoOpen>]\nmodule M =\n    val x: int\n",
                ),
                (
                    "Lib.fs",
                    "namespace PairAO\n[<AutoOpen>]\nmodule M =\n    let x = 1\n",
                ),
            ],
        ),
        // Conditional compilation under A's defines.
        with_defines(
            one(
                "defines",
                "namespace Def\n#if A_ONLY\ntype Shown = { X: int }\n#else\ntype Hidden = { Y: int }\n#endif\n#if B_ONLY\ntype NotA = int\n#endif\n",
            ),
            &["A_ONLY"],
        ),
        // Extension members.
        one(
            "extension_forms",
            "namespace Ext\nmodule Members =\n    type System.String with\n        member s.Method() = s.Length\n        member s.Prop = s.Length\n        member s.GetSet with get () = 1 and set (v: int) = ()\n        member s.OnlySet with set (v: int) = ()\n        static member Static() = 1\n        static member StaticProp = 1\n        static member (+++) (a: string, b: int) = a\n        member s.Item with get (i: int) = s.[i]\n        member s.Overload(x: int) = x\n        member s.Overload(x: string) = x\n",
        ),
        one(
            "extension_generic",
            "namespace ExtGen\nmodule M =\n    type List<'T> with\n        member l.Second = List.item 1 l\n    type System.Collections.Generic.Dictionary<'K, 'V> with\n        member d.Count2 = d.Count\n",
        ),
        one(
            "extension_of_abbreviation",
            "namespace ExtAbb\nmodule M =\n    type 'a option with\n        member o.IsIt = o.IsSome\n",
        ),
        one(
            "extension_intrinsic",
            "module ExtIntr\ntype Rec = { X: int }\ntype Rec with\n    member r.Y = r.X\ntype Cls() = member _.A = 1\ntype Cls with\n    member _.B = 2\ntype IFace = abstract M: int\nmodule IFaceExt =\n    type IFace with\n        member i.N = i.M\ntype Uni = | U of int\nmodule Later =\n    type Rec with\n        member r.Z = r.X\n",
        ),
        one(
            "extension_csharp_style",
            "namespace ExtCs\nopen System.Runtime.CompilerServices\n[<Extension>]\ntype Exts =\n    [<Extension>]\n    static member Twice(s: string) = s + s\n    [<Extension>]\n    static member Count(s: string, c: char) = 0\n    static member NotOne(s: string) = s\ntype Implied =\n    [<Extension>]\n    static member Thrice(s: string) = s + s + s\nmodule Lets =\n    [<Extension>]\n    let shout (s: string) = s.ToUpper()\n    let plain (s: string) = s\nmodule RecLets =\n    [<Extension>]\n    let rec whisper (s: string) = s.ToLower()\nmodule rec InRec =\n    [<Extension>]\n    let murmur (s: string) = s\n",
        ),
        one(
            "extension_compiled_name",
            "namespace ExtCn\nopen System.Runtime.CompilerServices\nmodule M =\n    type System.String with\n        [<CompiledName(\"Renamed\")>]\n        member s.Orig() = 1\n    [<Extension; CompiledName(\"renamedLet\")>]\n    let origLet (s: string) = s\n",
        ),
        one(
            "extension_compiled_name_property",
            "namespace ExtCnP\nopen System.Runtime.CompilerServices\ntype Holder =\n    [<Extension; CompiledName(\"RenamedProp\")>]\n    static member P(s: string) = 1\n    [<Extension; CompiledName(\"RenamedCsProp\")>]\n    static member Q = 1\nmodule M =\n    type System.String with\n        [<CompiledName(\"RenamedGetter\")>]\n        member s.Prop = 1\n        [<CompiledName(\"RenamedStatic\")>]\n        static member SProp with get () = 1 and set (v: int) = ()\n",
        ),
        one(
            "extension_active_pattern",
            "namespace ExtAp\nopen System.Runtime.CompilerServices\nmodule M =\n    [<Extension>]\n    let (|Big|_|) (s: string) = if s.Length > 3 then Some s else None\n",
        ),
        one(
            "extension_namespace_level",
            "namespace ExtNs\ntype System.Int32 with\n    member i.Double = i * 2\n",
        ),
        // Assembly-level AutoOpen.
        one(
            "assembly_auto_open",
            "namespace AsmAO\nmodule M =\n    let x = 1\n[<assembly: AutoOpen(\"AsmAO\")>]\n[<assembly: AutoOpen(@\"AsmAO.M\")>]\n[<assembly: AutoOpen(\"AsmAO\")>]\ndo ()\n",
        ),
        one(
            "assembly_auto_open_no_argument",
            "namespace AsmAONone\n[<assembly: AutoOpen>]\ndo ()\n",
        ),
        one(
            "assembly_auto_open_constant",
            "namespace AsmAOConst\nmodule C =\n    [<Literal>]\n    let Path = \"AsmAOConst\"\n[<assembly: AutoOpen(C.Path)>]\ndo ()\n",
        ),
        one(
            "assembly_other_attribute",
            "namespace AsmOther\n[<assembly: System.Reflection.AssemblyDescription(\"d\")>]\ndo ()\n",
        ),
        // Hostile names.
        one(
            "names_backticked",
            "namespace Odd.Inner\ntype ``My Type`` = { X: int }\nmodule ``a module`` =\n    type ``Spaced Abbrev`` = int\n    exception ``Odd Exn``\n    type ``let`` = { L: int }\n",
        ),
        one(
            "names_backticked_namespace",
            "namespace ``Odd Ns``.Inner\ntype T = { X: int }\n",
        ),
        one(
            "names_with_dot",
            "namespace Dotted\nmodule M =\n    type ``with.dot`` = { X: int }\n",
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
            "names_operators_and_keywords",
            "namespace Ops\nmodule M =\n    type System.String with\n        static member (|>>) (a: string, b: int) = a\n        member s.``member`` = 1\n        member s.``type`` () = 2\n",
        ),
        // Declines.
        one(
            "hash_nowarn",
            "namespace HashR\n#nowarn \"40\"\ntype T = int\n",
        ),
    ];
    // Reference environments that route an attribute name to a marker, or
    // away from one.
    cells.push(with_ref(
        one(
            "route_alias_auto_open",
            "namespace RouteAlias\nopen RefAlias\n[<AO>]\nmodule M =\n    let x = 1\n",
        ),
        "RefAliasLib",
        "namespace RefAlias\ntype AO = Microsoft.FSharp.Core.AutoOpenAttribute\n",
        Certificate::Override(vec![("AO", vec![Marker::AutoOpen])]),
    ));
    cells.push(with_ref(
        one(
            "route_alias_extension",
            "namespace RouteAliasExt\nopen RefAliasExt\n[<Ex>]\ntype T =\n    [<Ex>]\n    static member Twice(s: string) = s + s\n",
        ),
        "RefAliasExtLib",
        "namespace RefAliasExt\ntype Ex = System.Runtime.CompilerServices.ExtensionAttribute\n",
        Certificate::Override(vec![("Ex", vec![Marker::Extension])]),
    ));
    cells.push(with_ref(
        one(
            "route_shadow_auto_open",
            "namespace RouteShadow\nopen RefShadow\n[<AutoOpen>]\nmodule M =\n    let x = 1\n",
        ),
        "RefShadowLib",
        "namespace RefShadow\ntype AutoOpenAttribute() =\n    inherit System.Attribute()\n",
        Certificate::Override(vec![("AutoOpen", vec![])]),
    ));
    cells
}
