// An attribute whose compiled name, not its logical name, is
// `Microsoft.FSharp.Core.AutoOpenAttribute`: FCS reads an attribute by its
// logical identity, so `ByCompiledNameOnly` is no auto-open module.
namespace Microsoft.FSharp.Core

[<CompiledName("AutoOpenAttribute")>]
type OtherAttribute() =
    inherit System.Attribute()

namespace Existence.Markers

[<Microsoft.FSharp.Core.Other>]
module ByCompiledNameOnly =
    let b = 0

[<AutoOpen>]
module ReallyAutoOpen =
    let r = 0

namespace Existence.Targets

open System.Runtime.CompilerServices

type Receiver() =
    member _.Plain = 0

type Methods =
    [<Extension>]
    static member Ext(r: Receiver, i: int) = 0L

module Extensions =
    type Receiver with
        member r.Opt(i: int) = 0L

    type Holder = { H: int }

// Only internal abbreviations live in this namespace.
namespace Existence.AliasOnly

[<System.Runtime.CompilerServices.Extension>]
type internal HiddenAlias = Existence.Targets.Methods

[<AutoOpen>]
type internal HiddenAutoAlias = Existence.Targets.Extensions.Holder

namespace Existence.Kinds

type PublicType() = class end
type internal InternalType() = class end
type private PrivateType() = class end

type PublicAbbrev = int
type internal InternalAbbrev = string
type private PrivateAbbrev = float

exception PublicExn of string
exception internal InternalExn of int
exception internal InternalExnAbbrev = PublicExn

[<Measure>]
type m

[<Measure>]
type internal hidden

[<Measure>]
type internal mAbbrev = m

type Generic<'T> = { Value: 'T }

type internal Union =
    | A
    | B of int

module Public =
    let v = 1
    type Nested = { X: int }

    module internal Inner =
        type private Deep() = class end

[<AutoOpen>]
module internal Auto =
    module Lent =
        let w = 2

[<RequireQualifiedAccess>]
module private Private =
    let p = 3

module Suffixed =
    let s = 4

type Suffixed = { S: int }
