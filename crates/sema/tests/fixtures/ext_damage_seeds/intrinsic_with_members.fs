module M
exception MyEx of string with
    member e.Shout(i: int) = 0L
type R = { A: int } with
    member r.Third(i: int) = 0L
type D = | X | Y with
    member d.Fourth(i: int) = 0L
let mid = 1
let a1 = (MyEx "a" :?> MyEx).Shout(1)
let a2 = { A = 1 }.Third(1)
let a3 = X.Fourth(1)
