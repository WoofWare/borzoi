namespace N
module Outer =
    type System.String with
        member s.Shout(i: int) = 0L
        member s.Loud = 1
    let mid = 1
    module Inner =
        let a1 = "abc".Shout(1)
        let a2 = "abc".Loud
    let a3 = "abc".Shout(1)
