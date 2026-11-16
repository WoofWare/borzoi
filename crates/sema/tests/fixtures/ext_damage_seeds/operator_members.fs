module M
type System.String with
    static member (*) (a: string, b: int) = 0L
    static member ( .. .. ) (a: string, b: int, c: int) = 0L
    static member (~-) (a: string) = 0L
    static member (?<-) (a: string, b: string, c: int) = 0L
    static member (>>=) (a: string, b: int) = 0L
    static member (<|>) (a: string, b: int) = 0L
    static member (!) (a: string) = 0L
    static member (%) (a: string, b: int) = 0L
let mid = 1
let a1 = System.String.op_Multiply("a", 1)
let a2 = System.String.op_RangeStep("a", 1, 2)
let a3 = System.String.op_UnaryNegation("a")
let a4 = System.String.op_DynamicAssignment("a", "b", 1)
let a5 = System.String.op_GreaterGreaterEquals("a", 1)
let a6 = System.String.op_LessBarGreater("a", 1)
let a7 = System.String.op_Dereference("a")
let a8 = System.String.op_Modulus("a", 1)
