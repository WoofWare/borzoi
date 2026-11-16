module M
type System.Int32 with
    member s.Third(i: int) = 0L
let mid = 1
type System.String with
    member s.(|Big|_|) (x: int) = Some 0L
let mid2 = 1
let a6 = "abc".``|Big|_|``(1)
let a7 = (1).Third(1)
