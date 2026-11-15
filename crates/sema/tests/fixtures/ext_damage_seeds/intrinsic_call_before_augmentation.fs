module M
type T() =
    member _.Base() = T().Extra(1)
let f0 = 1
let f1 = T().Extra(1)
let f2 = 2
type T with
    member _.Extra(i: int) = 0L
let a1 = T().Extra(1)
