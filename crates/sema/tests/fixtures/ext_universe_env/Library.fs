// Extension members that reach a project file only through an `open` or a
// type abbreviation. Every extension here returns `int64` where the intrinsic
// member of its name returns `bool`, and takes an `int` where the intrinsic
// takes `obj`, so FCS binds it over the intrinsic and a wrong commit is a
// type mismatch rather than a silent agreement.

namespace ExtUniverse

/// An F# optional extension, in scope only after `open ExtUniverse.FsExts`
/// (a module open).
module FsExts =
    type System.Collections.Hashtable with
        member h.ContainsKey(i: int) = 0L

/// An F# optional extension in a nested `[<AutoOpen>]` module, in scope after
/// `open ExtUniverse.Outer` (a module open that auto-opens `Inner`).
module Outer =
    [<AutoOpen>]
    module Inner =
        type System.Collections.Hashtable with
            member h.ContainsKey(i: int) = 0L

namespace ExtUniverse.Cs

open System.Runtime.CompilerServices

/// A C#-style extension container, in scope after `open ExtUniverse.Cs` (a
/// namespace open) or `open type ExtUniverse.Cs.CsExts`.
[<Extension>]
type CsExts =
    [<Extension>]
    static member ContainsKey(h: System.Collections.Hashtable, i: int) = 0L

namespace ExtUniverse.Renamed

open System.Runtime.CompilerServices

/// A C#-style extension whose IL name (`Zap`) is not its logical name.
[<Extension>]
type CsRenamed =
    [<Extension; CompiledName("Zap")>]
    static member ContainsValue(h: System.Collections.Hashtable, i: int) = 0L

namespace ExtUniverse.Ab

/// An `[<Extension>]` abbreviation of `CsExts`: opening this namespace brings
/// `CsExts`'s extensions into scope, though `CsExts` is declared elsewhere.
[<System.Runtime.CompilerServices.Extension>]
type Alias = ExtUniverse.Cs.CsExts

namespace ExtUniverse.Ao

/// An `[<AutoOpen>]` abbreviation of `CsExts`: opening this namespace opens
/// `CsExts`'s static content, its extensions included.
[<AutoOpen>]
type AoAlias = ExtUniverse.Cs.CsExts

namespace ExtUniverse.Plain

/// An abbreviation of `CsExts` with no attribute: opening this namespace brings
/// no extension.
type PlainAlias = ExtUniverse.Cs.CsExts

namespace ExtUniverse.Prop

/// An indexed extension *property* named like the intrinsic method.
module PropExts =
    type System.Collections.Hashtable with
        member h.ContainsValue
            with get (i: int) = 0L

namespace ExtUniverse.Str

open System.Runtime.CompilerServices

/// A C#-style extension of `string` named `Equals`, which a literal receiver
/// reaches with no resolution of its own: `"abc".Equals(1)`.
[<Extension>]
type StrExts =
    [<Extension>]
    static member Equals(s: string, i: int) = 0L

namespace ExtUniverse.StrAb

/// An `[<Extension>]` abbreviation of `StrExts`.
[<System.Runtime.CompilerServices.Extension>]
type Alias = ExtUniverse.Str.StrExts

namespace ExtUniverse.StrAo

/// An `[<AutoOpen>]` abbreviation of `StrExts`.
[<AutoOpen>]
type AoAlias = ExtUniverse.Str.StrExts

namespace ExtUniverse.StrPlain

/// An abbreviation of `StrExts` with no attribute.
type PlainAlias = ExtUniverse.Str.StrExts

namespace ExtUniverse.StrAoAliased

/// An abbreviation of `AutoOpenAttribute`, in the same assembly as its use.
type AO = AutoOpenAttribute

/// An abbreviation of `StrExts` under the aliased `[<AutoOpen>]`.
[<AO>]
type AoAlias = ExtUniverse.Str.StrExts

namespace ExtUniverse.StrAbAliased

/// An abbreviation of `ExtensionAttribute`, in the same assembly as its use.
type Ext = System.Runtime.CompilerServices.ExtensionAttribute

/// An abbreviation of `StrExts` under the aliased `[<Extension>]`.
[<Ext>]
type Alias = ExtUniverse.Str.StrExts
