module M
type System.String with
    member s.``my name``(i: int) = 0L
    static member (+.) (a: string, b: int) = 0L
    member s.Prop with get () = 1 and set (v: int) = ()
let a1 = "abc".``my name``(1)
let a2 = System.String.op_PlusDot("a", 1)
let a3 = "abc".Prop
