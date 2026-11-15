module M
let broken = (1 + 2)
let gap1 = 1
let gap2 = [ 2 ]
let gap3 = "3"
type System.String with
    member s.Shout(i: int) = 0L
let a1 = "abc".Shout(1)
