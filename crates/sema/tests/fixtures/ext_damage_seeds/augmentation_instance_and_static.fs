module M
let before = "abc".Shout(1)
type System.String with
    member s.Shout(i: int) = 0L
    member s.Loud = 1
    static member Make(i: int) = "x"
let mid = 1
type System.Int32 with
    member i.Twice() = i * 2
let a1 = "abc".Shout(1)
let a2 = "abc".Loud
let a3 = System.String.Make(1)
let a4 = (3).Twice()
