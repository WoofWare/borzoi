module M
type U() =
    member _.F() = "abc".Shout(1)
and V() =
    member _.G() = 1
and W() =
    member _.H() = 2
and System.String with
    member s.Shout(i: int) = 0L
let a2 = "abc".Shout(1)
