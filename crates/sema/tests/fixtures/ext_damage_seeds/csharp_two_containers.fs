module M
open System.Runtime.CompilerServices
let pre = 1
[<Extension>]
type E =
    [<Extension>]
    static member Shout(s: string, i: int) = 0L
let mid = 1
let mid2 = 2
[<Extension>]
type F() =
    [<Extension>]
    static member Third(s: string, i: int) = 0L
    member _.Other() = 1
let a1 = "abc".Shout(1)
let a2 = "abc".Third(1)
