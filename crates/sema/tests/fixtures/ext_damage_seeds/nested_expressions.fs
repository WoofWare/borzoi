module M
let f x =
    let y = (x + 1)
    y
type System.String with
    member s.Shout(i: int) =
        let z = [ i; i ]
        0L
    member s.Third(i: int) = if i > 0 then 0L else 1L
let g (x: int) = { new System.Object() with member _.ToString() = "" }
type R = { A: int; B: string }
type System.Int32 with
    member i.Fourth(j: int) = match j with | 0 -> 0L | _ -> 1L
let a1 = "abc".Shout(1)
let a2 = "abc".Third(1)
let a3 = (3).Fourth(1)
