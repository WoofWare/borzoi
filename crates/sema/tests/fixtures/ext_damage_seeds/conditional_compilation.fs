module M
#if FOO
let x = 1
#else
type System.String with
    member s.Shout(i: int) = 0L
#endif
let mid = 1
#if BAR
type System.Int32 with
    member s.Third(i: int) = 0L
#endif
let a1 = "abc".Shout(1)
let a2 = (1).Third(1)
