module M
open System.Runtime.CompilerServices
[<Extension>]
type E =
    [<Extension>]
    static member Shout(s: string, i: int) = 0L
    [<Extension>]
    static member Loud(s: string) = 1
    static member Plain(s: string) = 2
let a1 = "abc".Shout(1)
let a2 = "abc".Loud()
