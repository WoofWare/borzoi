module M
open System.Runtime.CompilerServices
type E =
    [<Extension>]
    static member Shout(s: string, i: int) = 0L
    static member P1(s: string) = 2
    static member P2(s: string) = 2
    static member P3(s: string) = (2)
let g x = (x + 1)
let a1 = "abc".Shout(1)
