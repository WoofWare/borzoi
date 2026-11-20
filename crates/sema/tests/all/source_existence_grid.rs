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
            "namespace Targets\nopen System.Runtime.CompilerServices\n[<type: AutoOpen>]\ntype T() = static member M = 1\n[<type: CompiledName(\"Renamed\")>]\ntype U() = class end\ntype E =\n    [<return: Extension>]\n    static member R(s: string) = s\n    [<method: Extension>]\n    static member M(s: string) = s\nmodule Aug =\n    type System.Collections.Generic.List<'T> with\n        [<return: CompiledName(\"Q\")>]\n        member s.Orig() = 1\n",
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
            "namespace ExtEvent\nmodule M =\n    let ev = Event<int>()\n    type System.Collections.Generic.List<'T> with\n        [<CLIEvent>]\n        member s.Something = ev.Publish\n",
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
        // A class `let` is a method val only when it takes arguments, and
        // its name is mangled (`f@line[-k]`) when an earlier name in the
        // class's representation took it.
        one(
            "class_let_duplicate_names",
            "module LetDup\nopen System.Runtime.CompilerServices\ntype Dup() =\n    [<Extension>]\n    static let f (s: string) = s\n    [<Extension>]\n    static let f (s: string) = s + f s\n    [<Extension>]\n    static let f (s: string) = s + f s\n    member _.G = f \"x\"\n",
        ),
        one(
            "class_let_ctor_argument",
            "module LetArg\nopen System.Runtime.CompilerServices\ntype A(f: string) =\n    [<Extension>]\n    let f (s: string) = s + f\n    member _.G = f \"x\"\n",
        ),
        one(
            "class_let_self_identifier",
            "module LetSelf\nopen System.Runtime.CompilerServices\ntype S() as f =\n    [<Extension>]\n    static let f (s: string) = s\n    member _.G = f \"x\"\n    member _.H = f\n",
        ),
        one(
            "class_let_field",
            "module LetField\nopen System.Runtime.CompilerServices\ntype F() =\n    [<DefaultValue>]\n    static val mutable private f: int\n    [<Extension>]\n    static let f (s: string) = s\n    member _.G = f \"x\"\n",
        ),
        one(
            "class_let_after_destructuring",
            "module LetDestruct\nopen System.Runtime.CompilerServices\ntype D() =\n    static let f, g = 1, 2\n    [<Extension>]\n    static let f (s: string) = s\n    [<Extension>]\n    static let patternInput (s: string) = s\n    member _.G = f \"x\" + string g + patternInput \"y\"\n",
        ),
        one(
            "class_let_values",
            "module LetValues\nopen System.Runtime.CompilerServices\ntype V() =\n    [<Extension>]\n    static let v = 1\n    [<Extension>]\n    static let mutable m = fun (s: string) -> s\n    [<Extension>]\n    static let l = fun (s: string) -> s\n    [<Extension>]\n    static let t : string -> string = id\n    [<Extension>]\n    static let p = (fun (s: string) -> s)\n    member _.G = v + (m \"x\").Length + (l \"x\").Length + (t \"x\").Length + (p \"x\").Length\n",
        ),
        one(
            "class_let_parenthesised_heads",
            "module LetParen\nopen System.Runtime.CompilerServices\ntype H() =\n    [<Extension>]\n    static let (f: string -> string) = fun s -> s\n    [<Extension>]\n    static let (g) = fun (s: string) -> s\n    member _.G = f \"x\" + g \"y\"\n",
        ),
        one(
            "class_let_ident_on_next_line",
            "module LetNextLine\nopen System.Runtime.CompilerServices\ntype N() =\n    static let f (s: string) = s\n    [<Extension>]\n    static let\n        f (s: string) = s\n    member _.G = f \"x\"\n",
        ),
        one(
            "class_let_compiled_name_taken",
            "module LetCompiled\nopen System.Runtime.CompilerServices\ntype C() =\n    [<Extension>]\n    static let Q (s: string) = s\n    [<CompiledName(\"Q\")>]\n    member _.R() = Q \"x\"\n",
        ),
        one(
            "class_let_accessor_name_taken",
            "module LetAccessor\nopen System.Runtime.CompilerServices\ntype C() =\n    [<Extension>]\n    static let get_P (s: string) = s\n    member _.P = get_P \"x\"\n",
        ),
        one(
            "class_let_unused_self_identifier",
            "module LetSelfUnused\nopen System.Runtime.CompilerServices\ntype S() as f =\n    [<Extension>]\n    static let f (s: string) = s\n    member _.G = f \"x\"\n",
        ),
        one(
            "class_let_record_field",
            "module LetRecord\nopen System.Runtime.CompilerServices\ntype R =\n    { f: int }\n    [<Extension>]\n    static let f (s: string) = s\n    static member G = f \"x\"\n",
        ),
        one(
            "class_let_union_generated_names",
            "module LetUnion\nopen System.Runtime.CompilerServices\ntype U =\n    | A\n    | B of int\n    [<Extension>]\n    static let get_IsA (s: string) = s\n    [<Extension>]\n    static let get_Tag (s: string) = s\n    [<Extension>]\n    static let NewB (s: string) = s\n    static member G = get_IsA \"x\" + get_Tag \"y\" + NewB \"z\"\n",
        ),
        one(
            "class_let_named_like_a_mangled_name",
            "module LetMangled\nopen System.Runtime.CompilerServices\ntype M() =\n    static let f (s: string) = s\n    static let f (s: string) = s\n    [<Extension>]\n    static let ``f@5`` (s: string) = s\n    member _.G = f \"x\" + ``f@5`` \"y\"\n",
        ),
        one(
            "class_let_interface_member_name",
            "module LetIface\nopen System.Runtime.CompilerServices\ntype I =\n    abstract m: unit -> int\ntype C() =\n    [<Extension>]\n    static let m (s: string) = s\n    member _.G = m \"x\"\n    interface I with\n        member _.m() = 1\n",
        ),
        one(
            "class_let_wildcard_argument",
            "module LetWild\nopen System.Runtime.CompilerServices\ntype W(_: int, f: int) =\n    [<Extension>]\n    static let f (s: string) = s\n    [<Extension>]\n    static let g (s: string) = s\n    member _.G = f \"x\" + g \"y\"\n",
        ),
        one(
            "rec_module_class_with_constructor",
            "module rec RecCtor\ntype T() =\n    static let h (s: string) = s\n    [<System.Runtime.CompilerServices.Extension>]\n    new(s: string) = T()\n    member _.U = h \"x\"\n",
        ),
        one(
            "rec_module_class_with_constructor_nested",
            "namespace RecCtorNested\nmodule Outer =\n    module rec Inner =\n        type T() =\n            static let h (s: string) = s\n            [<System.Runtime.CompilerServices.Extension>]\n            new(s: string) = T()\n            member _.U = h \"x\"\n",
        ),
        one(
            "rec_module_class_with_constructor_and_let",
            "namespace RecCtorLet\nmodule Outer =\n    module rec Inner =\n        type T() =\n            static let h (s: string) = s\n            [<System.Runtime.CompilerServices.Extension>]\n            new(s: string) = T()\n            member _.U = h \"x\"\n        [<System.Runtime.CompilerServices.Extension>]\n        let f (s: string) = s\n",
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
            "module SuffixAug\ntype System.Collections.Generic.List<'T> with\n    member s.Len = s.Count\nmodule String =\n    let x = 1\n",
        ),
        // CompiledName.
        one(
            "compiled_name",
            "namespace CN\n[<CompiledName(\"RenamedType\")>]\ntype T() = member _.X = 1\n[<CompiledName(\"RenamedModule\")>]\nmodule M =\n    let x = 1\n[<CompiledNameAttribute(@\"Verbatim\")>]\ntype V = { A: int }\n",
        ),
        // A recursive group honours an exception's `[<CompiledName>]`.
        one(
            "compiled_name_exception_namespace_rec",
            "namespace rec CNR\n[<CompiledName(\"Renamed\")>]\nexception E of int\n",
        ),
        one(
            "compiled_name_exception_module_rec",
            "module rec CNM\n[<CompiledName(\"Renamed\")>]\nexception E of int\nmodule Inner =\n    [<CompiledName(\"InnerRenamed\")>]\n    exception F of int\n",
        ),
        one(
            "compiled_name_exception_rec_unreadable",
            "module rec CNU\n[<Literal>]\nlet N = \"Renamed\"\n[<CompiledName(N)>]\nexception E of int\n",
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
            "namespace Ext\nmodule Members =\n    type System.Collections.Generic.List<'T> with\n        member s.Method() = s.Count\n        member s.Prop = s.Count\n        member s.GetSet with get () = 1 and set (v: int) = ()\n        member s.OnlySet with set (v: int) = ()\n        static member Static() = 1\n        static member StaticProp = 1\n        static member (+++) (a: string, b: int) = a\n        member s.Item with get (i: int) = s.[i]\n        member s.Overload(x: int) = x\n        member s.Overload(x: string) = x\n",
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
            "namespace ExtCn\nopen System.Runtime.CompilerServices\nmodule M =\n    type System.Collections.Generic.List<'T> with\n        [<CompiledName(\"Renamed\")>]\n        member s.Orig() = 1\n    [<Extension; CompiledName(\"renamedLet\")>]\n    let origLet (s: string) = s\n",
        ),
        one(
            "extension_compiled_name_property",
            "namespace ExtCnP\nopen System.Runtime.CompilerServices\ntype Holder =\n    [<Extension; CompiledName(\"RenamedProp\")>]\n    static member P(s: string) = 1\n    [<Extension; CompiledName(\"RenamedCsProp\")>]\n    static member Q = 1\nmodule M =\n    type System.Collections.Generic.List<'T> with\n        [<CompiledName(\"RenamedGetter\")>]\n        member s.Prop = 1\n        [<CompiledName(\"RenamedStatic\")>]\n        static member SProp with get () = 1 and set (v: int) = ()\n",
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
        // An entity has no return value: a `return:` attribute is its own.
        one(
            "attribute_target_return_on_entities",
            "namespace RetEnt\n[<return: AutoOpen>]\nmodule M =\n    let x = 1\n[<return: CompiledName(\"Renamed\")>]\ntype T = { X: int }\n",
        ),
        // So do a primary constructor and a signature.
        one(
            "attribute_target_return_on_constructor_and_slot",
            "module RetCtor\n[<AbstractClass>]\ntype T [<return: System.Runtime.CompilerServices.Extension>] (x: int) =\n    [<return: System.Runtime.CompilerServices.Extension>]\n    abstract M: string -> string\n    member _.X = x\n",
        ),
        Cell::new(
            "attribute_target_return_on_signature_val",
            &[
                (
                    "Lib.fsi",
                    "module RetSig\n[<return: System.Runtime.CompilerServices.Extension>]\nval f: string -> string\n",
                ),
                ("Lib.fs", "module RetSig\nlet f (s: string) = s\n"),
            ],
        ),
        // Codex round 3's shapes, each now a generator dimension too.
        one(
            "module_let_duplicate_names",
            "module DupLet\nopen System.Runtime.CompilerServices\n[<Extension>]\nlet f (s: string) = s\n[<Extension>]\nlet f (s: string) = s\n",
        ),
        one(
            "event_on_accessor_in_augmentation",
            "module EvAcc\ntype System.Collections.Generic.List<'T> with\n    member x.Foo with [<CLIEvent>] get () = Event<int>().Publish\n",
        ),
        Cell::new(
            "constrained_member_signature",
            &[
                (
                    "Lib.fsi",
                    "module Constrained\ntype T =\n    new: unit -> T\n    [<System.Runtime.CompilerServices.Extension; CompiledName(\"Renamed\")>]\n    static member M: s: 'T -> bool when 'T: equality\n",
                ),
                (
                    "Lib.fs",
                    "module Constrained\ntype T() =\n    [<CompiledName(\"Renamed\")>]\n    static member M(s: 'T) = s = s\n",
                ),
            ],
        ),
        one(
            "local_attribute_attribute_alias",
            "namespace AttrAttr\ntype FooAttributeAttribute = Microsoft.FSharp.Core.AutoOpenAttribute\n[<FooAttribute>]\nmodule M =\n    let x = 1\n",
        ),
        one(
            "tuple_augmentation",
            "module TupleAug\ntype (int * int) with\n    member x.Prop = 5\ntype struct (int * string * bool) with\n    member x.Other = 6\n",
        ),
        one(
            "augmentation_constructor",
            "module AugCtor\ntype System.Collections.Generic.List<'T> with\n    new(x: string) = \"\"\n",
        ),
        one(
            "self_named_generic_abbreviation",
            "namespace SelfGeneric\ntype Foo = { X: int }\n[<System.Runtime.CompilerServices.Extension>]\ntype Foo<'a> = Foo\n",
        ),
        // Codex round 7: an active pattern's mangled name carries its own
        // line, and a quoted directive name is the directive.
        one(
            "class_let_active_pattern_on_next_line",
            "module ApLine\nopen System.Runtime.CompilerServices\ntype T() =\n    static let (|A|_|) (x: int) = Some x\n    [<Extension>]\n    static let\n        (|A|_|) (x: int) = Some x\n    member _.G = match 1 with A x -> x | _ -> 0\n",
        ),
        // The augmentation cells whose arity-less heads decline, with heads
        // that write their parameters, so the kinds and placement they
        // exercise stay graded.
        one(
            "extension_intrinsic_generic",
            "module ExtIntrG\ntype Rec<'a> = { X: 'a }\ntype Rec<'a> with\n    member r.Y = r.X\ntype Cls<'a>() = member _.A = 1\ntype Cls<'a> with\n    member _.B = 2\ntype IFace<'a> = abstract M: 'a\nmodule IFaceExt =\n    type IFace<'a> with\n        member i.N = i.M\ntype Uni<'a> = | U of 'a\nmodule Later =\n    type Rec<'a> with\n        member r.Z = r.X\n",
        ),
        one(
            "augmentation_of_single_case_abbreviation_generic",
            "module AugCaseG\nopen System.Runtime.CompilerServices\ntype T<'a> = Case\ntype T<'a> with\n    [<Extension>]\n    static member M(s: string) = s\n",
        ),
        one(
            "extension_namespace_level_generic",
            "namespace ExtNsG\ntype System.Collections.Generic.List<'T> with\n    member l.Double = l.Count * 2\n",
        ),
        one(
            "attribute_made_interface_augmentation_generic",
            "module AttrInterfaceG\n[<Interface>]\ntype I<'a>() =\n    abstract M: string -> string\ntype I<'a> with\n    static member Foo() = 1\n",
        ),
        // An override in a signature's augmentation: FCS rejects it and
        // imports the extension under ``List`1.ToString.Override``.
        Cell::new(
            "signature_augmentation_override",
            &[
                (
                    "Lib.fsi",
                    "module SigOverride\ntype System.Collections.Generic.List<'T> with\n    override ToString: unit -> string\n",
                ),
                (
                    "Lib.fs",
                    "module SigOverride\ntype System.Collections.Generic.List<'T> with\n    override l.ToString() = \"\"\n",
                ),
            ],
        ),
        // A type-provider producer whose check fails: FCS builds it no
        // assembly data, as it builds none for a type provider, so the oracle
        // cannot tell a source reading from a DLL one and grades nothing.
        one(
            "type_provider_assembly_failing",
            "namespace TpFail\n[<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\ndo ()\nmodule M =\n    let x: int = \"s\"\n",
        ),
        // A head whose argument pattern holds an active pattern on a later
        // line: FCS mangles by the binder's line, the head's first.
        one(
            "class_let_active_pattern_argument",
            "module ApArg\nopen System.Runtime.CompilerServices\ntype T(f: int) =\n    [<Extension>] static let f\n                    ((|Hi|_|): string -> unit option) = 1\n    member _.G = f\n",
        ),
        one(
            "quoted_load_directive",
            "module QuotedLoad\n#``load`` \"y.fsx\"\nlet x = 1\n",
        ),
        // The `Module` suffix, by every route FCS has to it: a flag value
        // passed through a literal, an exception of the module's name in a
        // recursive group, A's own namesake of the attribute (which FCS does
        // not obey), and the attribute itself over a nested module, which
        // the fold places under the written name. Each module ends in
        // `Module`, so the walk emits both readings.
        one(
            "module_suffix_literal_flag",
            "module LitSuffix\nmodule C =\n    [<Literal>]\n    let flags = CompilationRepresentationFlags.ModuleSuffix\n[<CompilationRepresentation(C.flags)>]\nmodule FooModule =\n    type T = int\n",
        ),
        one(
            "module_suffix_rec_group_exception",
            "module rec RecExnSuffix\nexception FooModule of int\nmodule FooModule =\n    type T = int\n",
        ),
        Cell::new(
            "module_suffix_namesake_attribute",
            &[
                (
                    "Namesake.fs",
                    "namespace Microsoft.FSharp.Core\ntype CompilationRepresentationAttribute(flags: CompilationRepresentationFlags) =\n    inherit System.Attribute()\n",
                ),
                (
                    "Use.fs",
                    "module NamesakeSuffix\n[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]\nmodule TestModule =\n    type T = int\n",
                ),
            ],
        ),
        one(
            "module_suffix_over_nested_module",
            "namespace FoldSuffix\n[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]\nmodule FooModule =\n    module Inner =\n        let x = 1\n",
        ),
        // The raw scans' cells (`RAW_SCANS`): a directive inside a nested
        // module, and an attribute FCS reads as the assembly's for standing
        // alone, with no `assembly:` target.
        one(
            "hash_reference_nested",
            "module HashNested\nmodule Inner =\n    #r \"x.dll\"\n    let x = 1\n",
        ),
        one(
            "standalone_assembly_attribute",
            "namespace StandaloneAo\nmodule M =\n    let x = 1\n[<AutoOpen(\"StandaloneAo.M\")>]\ndo ()\n",
        ),
        // A signature pair in one file excuses no lender in another: the
        // per-path accounting's witness.
        Cell::new(
            "lender_beside_signature_pair",
            &[
                ("Lib.fsi", "module PairElsewhere\nval x: int\n"),
                ("Lib.fs", "module PairElsewhere\nlet x = 1\n"),
                ("Other.fs", "namespace OtherNs\ntype A = int\n"),
            ],
        ),
        // Codex round 6: an active pattern inside a compound binding.
        one(
            "active_pattern_in_compound_binding",
            "module ApCompound\n[<System.Runtime.CompilerServices.Extension>]\nlet ((|Foo|_|) as f) = fun (x: int) -> Some x\n",
        ),
        one(
            "lender_under_suffixed_module",
            "namespace SuffixLender\nmodule FooModule =\n    [<AutoOpen>]\n    type Alias = int\n",
        ),
        // Extension-bearing shapes: their entity facts are graded here, their
        // extensions by the gate grids' referenced-project placements.
        one(
            "nullary_active_pattern_let",
            "module NullaryAp\n[<System.Runtime.CompilerServices.Extension>]\nlet (|Zero|_|) = function 0 -> Some () | _ -> None\n",
        ),
        one(
            "attribute_made_interface_augmentation",
            "module AttrInterface\n[<Interface>]\ntype I() =\n    abstract M: string -> string\ntype I with\n    static member Foo() = 1\n",
        ),
        Cell::new(
            "static_abstract_signature_augmentation",
            &[
                (
                    "Lib.fsi",
                    "module StaticAbstractSig\ntype System.Collections.Generic.List<'T> with\n    static abstract member Foo: int -> int\n",
                ),
                ("Lib.fs", "module StaticAbstractSig\nlet x = 1\n"),
            ],
        ),
        // Codex round 4's shapes.
        one(
            "intrinsic_augmentation_class_let",
            "module AugLet\ntype T() =\n    member _.X = 1\ntype T with\n    [<System.Runtime.CompilerServices.Extension>]\n    static let f (s: string) = s\n    static member G = f \"x\"\n",
        ),
        Cell::new(
            "signature_method_unreadable_rename",
            &[
                (
                    "Lib.fsi",
                    "module SigRename\ntype T =\n    new: unit -> T\n    [<System.Runtime.CompilerServices.Extension; CompiledName(\"X\" + \"Y\")>]\n    static member M: s: 'T -> bool when 'T: equality\n",
                ),
                (
                    "Lib.fs",
                    "module SigRename\ntype T() =\n    [<CompiledName(\"XY\")>]\n    static member M(s: 'T) = s = s\n",
                ),
            ],
        ),
        Cell::new(
            "signature_augmentation",
            &[
                (
                    "Lib.fsi",
                    "module SigAug\ntype System.Collections.Generic.List<'T> with\n    member S: int\n",
                ),
                (
                    "Lib.fs",
                    "module SigAug\ntype System.Collections.Generic.List<'T> with\n    member s.S = 1\n",
                ),
            ],
        ),
        Cell::new(
            "signature_augmentation_missing_in_implementation",
            &[
                (
                    "Lib.fsi",
                    "module SigAugMissing\ntype System.Collections.Generic.List<'T> with\n    member S: int\n",
                ),
                ("Lib.fs", "module SigAugMissing\nlet x = 1\n"),
            ],
        ),
        // A standalone attribute with no target is the assembly's when the
        // attribute allows it, as `[<AutoOpen>]` does.
        one(
            "assembly_auto_open_without_target",
            "namespace AsmNoTarget\nmodule M =\n    let x = 1\n[<AutoOpen(\"AsmNoTarget.M\")>]\ndo ()\n",
        ),
        one(
            "assembly_auto_open_without_target_in_module",
            "module AsmNoTargetMod\nlet x = 1\n[<AutoOpen(\"AsmNoTargetMod\")>]\ndo ()\n",
        ),
        // Abbreviation lenders: each is exact under the certificate, but
        // for a target that may be a union case, which the walk names.
        one(
            "abbreviation_lenders",
            "namespace Lenders\nopen System.Runtime.CompilerServices\n[<Extension>]\ntype S = string\n[<AutoOpen>]\ntype I = int\ntype Plain = int list\n",
        ),
        one(
            "abbreviation_lender_or_union",
            "namespace LenderOrUnion\n[<AutoOpen>]\ntype A = Somewhere\n",
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
            "namespace Ops\nmodule M =\n    type System.Collections.Generic.List<'T> with\n        static member (|>>) (a: string, b: int) = a\n        member s.``member`` = 1\n        member s.``type`` () = 2\n",
        ),
        // Declines.
        one(
            "hash_nowarn",
            "namespace HashR\n#nowarn \"40\"\ntype T = int\n",
        ),
    ];
    // Reference environments that route an attribute name to a marker, or
    // away from one.
    // The same failing type-provider producer, with a project reference:
    // its references are not the framework set, so FCS's `Unavailable` may
    // be a provider's (a reference may alias the attribute), and the oracle
    // grades nothing.
    cells.push(with_ref(
        one(
            "type_provider_assembly_failing_referenced",
            "namespace TpFailRef\n[<assembly: Microsoft.FSharp.Core.CompilerServices.TypeProviderAssembly>]\ndo ()\nmodule M =\n    let x: int = \"s\"\n",
        ),
        "TpFailRefLib",
        "namespace TpFailRefLib\ntype T = int\n",
        Certificate::BySpelling,
    ));
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
            "route_shadow_auto_open",
            "namespace RouteShadow\nopen RefShadow\n[<AutoOpen>]\nmodule M =\n    let x = 1\n",
        ),
        "RefShadowLib",
        "namespace RefShadow\ntype AutoOpenAttribute() =\n    inherit System.Attribute()\n",
        Certificate::Override(vec![("AutoOpen", vec![])]),
    ));
    // A's own type at `Microsoft.FSharp.Core.AutoOpenAttribute`: FCS's
    // in-memory list takes an assembly attribute for `AutoOpen` by its
    // owner's identity, its reader of a DLL by the owner's name.
    cells.push(Cell::new(
        "assembly_auto_open_local_namesake",
        &[
            (
                "Attr.fs",
                "namespace Microsoft.FSharp.Core
type AutoOpenAttribute(path: string) =
    inherit System.Attribute()
    member _.Path = path
",
            ),
            (
                "Lib.fs",
                "namespace N
[<assembly: Microsoft.FSharp.Core.AutoOpen(\"N\")>]
do ()
type T = { X: int }
",
            ),
        ],
    ));
    cells.extend(local_marker_aliases());
    cells
}

/// A marker abbreviated by a type of A's own, under every name `[<X>]` may
/// denote (`X`, `XAttribute`, and an `Attribute` the name already ends in
/// doubled), written every way: the certificate by spelling must leave each
/// such name to `Unknown`.
fn local_marker_aliases() -> Vec<Cell> {
    let mut cells = Vec::new();
    for (marker, full, carrier) in [
        (
            "auto_open",
            "Microsoft.FSharp.Core.AutoOpenAttribute",
            "module M =\n    let x = 1\n",
        ),
        (
            "extension",
            "System.Runtime.CompilerServices.ExtensionAttribute",
            "type S = string\n",
        ),
    ] {
        for alias in ["Foo", "FooAttribute", "FooAttributeAttribute"] {
            for written in ["Foo", "FooAttribute"] {
                cells.push(one(
                    &format!("local_alias_{marker}_{alias}_{written}"),
                    &format!(
                        "namespace LocalAlias\ntype {alias} = {full}\n[<{written}>]\n{carrier}"
                    ),
                ));
            }
        }
    }
    cells
}

/// Every raw scan the walk makes has its cell in the grid.
#[test]
fn every_raw_scan_has_a_cell() {
    let names: Vec<String> = cells().into_iter().map(|c| c.name).collect();
    for (scan, cell) in borzoi_sema::RAW_SCANS {
        assert!(
            names.iter().any(|n| n == cell),
            "the raw scan \"{scan}\" names no grid cell {cell}"
        );
    }
}
