module M
type T() =
    member _.Base() = 1
let f0 = 1
type T with
    member _.Extra(i: int) = 0L
type U() =
    member _.F() = "abc".Shout(1)
and System.String with
    member s.Shout(i: int) = 0L
let a1 = T().Extra(1)
let a2 = "abc".Shout(1)
