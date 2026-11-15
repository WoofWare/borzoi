namespace A
type System.String with
    member s.Shout(i: int) = 0L
namespace A.Cs
open System.Runtime.CompilerServices
[<Extension>]
type E =
    [<Extension>]
    static member Loud(s: string) = 1
namespace B
open A
open type A.Cs.E
module Use =
    let a1 = "abc".Shout(1)
    let a2 = "abc".Loud()
