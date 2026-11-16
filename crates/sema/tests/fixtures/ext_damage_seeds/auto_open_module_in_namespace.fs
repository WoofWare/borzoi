namespace N
[<AutoOpen>]
module Exts =
    type System.String with
        member s.Shout(i: int) = 0L
        static member Make(i: int) = "x"
module Use =
    let pre = 1
    let a1 = "abc".Shout(1)
    let a2 = System.String.Make(1)
