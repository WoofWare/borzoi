module M
module A =
    let pre = (1 + 2)
    type System.String with
        member s.Shout(i: int) = 0L
        member s.Third(i: int) = 0L
    let a0 = "abc".Shout(1)
module B =
    open A
    let a1 = "abc".Shout(1)
    let a2 = "abc".Third(1)
