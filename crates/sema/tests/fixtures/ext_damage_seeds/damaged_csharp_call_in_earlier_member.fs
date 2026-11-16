module M
open System.Runtime.CompilerServices
type E =
    static member Use() = "abc".Shout(1)
    static member Mid1() = 1
    static member Mid2() = 2
    [<Extension>]
    static  Shout(s: string, i: int) = 0L
let a1 = "abc".Shout(1)
