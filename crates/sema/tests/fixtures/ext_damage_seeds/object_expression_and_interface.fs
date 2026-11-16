module M
type I =
    abstract Run: int -> int
type System.String with
    member s.Shout(i: int) : int64 =
        let o = { new I with member _.Run(x) = x }
        int64 (o.Run i)
    member s.Third(i: int) = 0L
type C() =
    interface I with
        member _.Run(x) = x
    member _.Go() = "abc".Shout(1)
let a1 = "abc".Shout(1)
let a2 = "abc".Third(1)
