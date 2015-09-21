module expression

type Expression = 
    | Const of float
    | Var of string
    | Neg of Expression
    | Pow of Expression * Expression
    | Mul of Expression * Expression
    | Add of Expression * Expression
    | Sub of Expression * Expression
    | Div of Expression * Expression
    | Exp of Expression
    | Log of Expression
    | Sin of Expression
    | Cos of Expression
    static member ( ~+ ) x = x
    static member ( ~- ) x = Neg(x)
    static member ( + ) (x, y) = Add(x, y)
    static member ( - ) (x, y) = Sub(x, y)
    static member ( * ) (x, y) = Mul(x, y)
    static member ( / ) (x, y) = Div(x, y)


let (|Op|_|) (x : Expression) =
    match x with
    | Add(e1, e2) -> Some(Add, e1, e2)
    | Sub(e1, e2) -> Some(Sub, e1, e2)
    | Mul(e1, e2) -> Some(Mul, e1, e2)
    | Div(e1, e2) -> Some(Div, e1, e2)
    | Pow(e1, e2) -> Some(Pow, e1, e2)
    | _ -> None

let (|CommutativeOp|_|) (x : Expression) =
    match x with
    | Add(e1, e2) -> Some(Add, e1, e2)
    | Mul(e1, e2) -> Some(Mul, e1, e2)
    | _ -> None

let (|Func|_|) (x : Expression) =
    match x with
    | Exp(e) -> Some(Exp, e)
    | Log(e) -> Some(Log, e)
    | Sin(e) -> Some(Sin, e)
    | Cos(e) -> Some(Cos, e)
    | _ -> None

let (|Linear|_|) (x : Expression) = 
    match x with
    | Add(e1, e2) -> Some(Add, e1, e2)
    | Sub(e1, e2) -> Some(Sub, e1, e2)
    | Mul(e1, e2) -> Some(Mul, e1, e2)
    | _ -> None


let IsPrimitive (x : Expression) : bool = 
    match x with
    | Var(v) -> true
    | Const(n) -> true
    | _ -> false

let rec Dismantle x = 
    match x with
    | Mul(Const(n), e) -> 
        let (n1, e1) = Dismantle e in
        n * n1, e1
    | Mul(e, Const(n)) -> 
        let (n1, e1) = Dismantle e in
        n * n1, e1
    | Mul(e1, e2) -> 
        let (n1, y1) = Dismantle e1 in
        let (n2, y2) = Dismantle e2 in
        n1 * n2, y1 * y2
    | _ -> 1., x

let LargerThan x y = 
    let (n1, e1) = Dismantle x in
    let (n2, e2) = Dismantle y in
    if e1 > e2 then
        true
    else
        false

let rec FactorsImpl x lst = 
    match x with
    | Mul(e1, e2) -> FactorsImpl e2 ( FactorsImpl e1 lst)
    | _ -> x::lst

let Factors x = 
    FactorsImpl x []

let HasSameFactor x y =
    not (Set.intersect (set (Factors x)) (set (Factors y))).IsEmpty

let RemoveSameFactors lst1 lst2 =
    let intersect = Set.intersect (set lst1) (set lst2) in
    Set.toList ((set lst1) - intersect), Set.toList ((set lst2) - intersect)

let rec Muln lst = 
    match lst with
    | [] -> Const(1.)
    | x::xs -> x * (Muln xs)


//-------------------------------------------------------------------------------------------------
// Format
//-------------------------------------------------------------------------------------------------
let OpName (e: Expression) : string =
    match e with
    | Add(e1, e2) -> "+"
    | Sub(e1, e2) -> "-"
    | Mul(e1, e2) -> "*"
    | Div(e1, e2) -> "/"
    | Pow(e1, e2) -> "^"
    | _ -> failwith(sprintf "Unrecoginized function [%A]" e)

let FunName (e: Expression) (a: string) : string =
    match e with
    | Exp(x) -> sprintf "e^(%s)" a
    | Log(x) -> sprintf "log(%s)" a
    | Sin(x) -> sprintf "sin(%s)" a
    | Cos(x) -> sprintf "cos(%s)" a
    | _ -> failwith(sprintf "Unrecoginized function [%A]" e)


let Format e : string = 
    let requireParenthesis x : bool =
        match x with
        | Mul(e1, e2) -> true
        | Div(e1, e2) -> true
        | _ -> false
    let rec FormatImpl higher needParenthesis x : string =
        match x with
        | Var(s) -> s
        | Const(n) -> sprintf "%f" n
        | Neg(x) -> sprintf "-%s" (FormatImpl "neg" true x)
        | Op(op, e1, e2) -> 
            let t = (requireParenthesis x)
            let s = sprintf "%s %s %s" (FormatImpl (OpName x) t e1) (OpName x) (FormatImpl (OpName x) t e2)
            if needParenthesis && higher <> "" && (OpName x) <> higher then
                "(" + s + ")"
            else
                s
        | _ -> failwith(sprintf "unrecognized expression [%A]" x)
    FormatImpl "" false e
    
    
//-------------------------------------------------------------------------------------------------
// Sort
//-------------------------------------------------------------------------------------------------
let rec SortImpl isSorted x = 
    match x with 
    | CommutativeOp(op, e1, e2) when LargerThan e1 e2 -> op(e2, e1) |> SortImpl true
    // add
    | Add(e1, Add(e2, e3)) when LargerThan e1 e2 -> Add(e2, Add(e1, e3)) |> SortImpl true
    | Add(Add(e1, e2), Add(e3, e4)) when LargerThan e2 e3 -> Add(Add(e1, e3), Add(e2, e4)) |> SortImpl true
    // subtract
    | Sub(Add(e1, e2), e3) when LargerThan e2 e3 -> Add(Sub(e1, e3), e2) |> SortImpl true
    // multiply
    | Mul(e1, Mul(e2, e3)) when LargerThan e1 e2 -> Mul(e2, Mul(e1, e3))|> SortImpl true
    | Mul(Mul(e1, e2), Mul(e3, e4)) when LargerThan e2 e3 -> Mul(Mul(e1, e3), Mul(e2, e4))|> SortImpl true
    // binary operator
    | Op(op, e1, e2) -> 
        let (isSorted1, a1) = SortImpl false e1
        let (isSorted2, a2) = SortImpl false e2
        if isSorted1 || isSorted2 then
            op(a1, a2) |> SortImpl true
        else
            (isSorted, x)
    // other
    | _ -> (isSorted, x)


let Sort x = 
    let (isSorted, e) = SortImpl false x in e


//-------------------------------------------------------------------------------------------------
// Expand
//-------------------------------------------------------------------------------------------------
let rec ExpandImpl isExpanded x = 
    match x with
    | Mul(e1, Add(e2, e3)) -> Add(e1 * e2, e1 * e3) |> Sort |> ExpandImpl true
    | Mul(e1, Sub(e2, e3)) -> Sub(e1 * e2, e1 * e3) |> Sort |> ExpandImpl true
    | Sub(e1, Add(e2, e3)) -> e1 - e2 - e3  |> Sort |> ExpandImpl true
    | Op(op, e1, e2) -> 
        let (isExpanded1, a1) = ExpandImpl false e1
        let (isExpanded2, a2) = ExpandImpl false e2
        if isExpanded1 || isExpanded2 then
            op(a1, a2) |> Sort |> ExpandImpl true
        else
            (isExpanded, x)
    | _ -> (isExpanded, x)

let Expand x =
    let (isExpand, e) = Sort x |> ExpandImpl false in e




//-------------------------------------------------------------------------------------------------
// Simplify
//-------------------------------------------------------------------------------------------------
let rec SimplifyImpl isSimplified x = 
    match x with
    // constant
    | Add(Const(n1), Const(n2)) -> true, Const(n1 + n2)
    | Sub(Const(n1), Const(n2)) -> true, Const(n1 - n2)
    | Mul(Const(n1), Const(n2)) -> true, Const(n1 * n2)
    | Div(Const(n1), Const(n2)) -> true, Const(n1 / n2)
    | Neg(Const(n)) -> true, Const(-1.0 * n)
    // neg
    | Neg(Neg(e)) -> e |> Expand |> SimplifyImpl true
    // add
    | Add(e1, Neg(e2)) -> Sub(e1, e2) |> Expand |> SimplifyImpl true
    | Add(e1, e2) when
        let (n1, x1) = Dismantle e1 in
        let (n2, x2) = Dismantle e2 in
        x1 = x2
        -> 
        let (n1, x1) = Dismantle e1 in
        let (n2, x2) = Dismantle e2 in
        Const(n1 + n2) * x1 |> Expand |> SimplifyImpl true
    | Add(e1, Add(e2, e3)) when
        let (n1, x1) = Dismantle e1 in
        let (n2, x2) = Dismantle e2 in
        x1 = x2
        -> 
        let (n1, x1) = Dismantle e1 in
        let (n2, x2) = Dismantle e2 in
        Const(n1 + n2) * x1 + e3|> Expand |> SimplifyImpl true
    // multiply
    | Mul(e1, e2) when e1 = e2 -> Pow(e1, Const(2.)) |> SimplifyImpl true
    | Mul(Const(n), e) when n = 1. -> e |> Expand |> SimplifyImpl true
    | Mul(Const(n1), Mul(Const(n2), e)) -> Const(n1 * n2) * e |> Expand |> SimplifyImpl true
    // subtract
    | Sub(e1, e2) when e1 = e2 -> true, Const(0.)
    | Sub(e1, Neg(e2)) -> Add(e1, e2) |> Expand |> SimplifyImpl true
    // divide
    | Div(e, Const(n)) when n = 1. -> e |> Expand |> SimplifyImpl true
    | Div(e1, e2) when HasSameFactor e1 e2
        ->
        let (n1, x1) = Dismantle e1 in
        let (n2, x2) = Dismantle e2 in
        let (y1, y2) = RemoveSameFactors (Factors x1) (Factors x2) in
        Const(n1 / n2) * (Muln y1) / (Muln y2) |> Expand |> SimplifyImpl true
    // binary operator
    | Op(op, e1, e2) -> 
        let (isSimplified1, a1) = SimplifyImpl false e1 in
        let (isSimplified2, a2) = SimplifyImpl false e2 in
        if isSimplified1 || isSimplified2 then
            op(a1, a2) |> Expand |> SimplifyImpl true
        else
            (isSimplified, x)
    // other
    | _ -> isSimplified, x


let Simplify x =
    let (isSimplified, e) = Expand x |> SimplifyImpl false in e
    


let Tokenize (value: System.String) = 
    let value = value.Replace(" ", "")
    let value = value.Replace("e^(", "e(")
    let value = value.Replace("(", " ( ")
    let value = value.Replace(")", " ) ")
    let value = value.Replace("+", " + ")
    let value = value.Replace("-", " - ")
    let value = value.Replace("*", " * ")
    let value = value.Replace("/", " / ")
    let value = value.Replace("^", " ^ ")
    value.Trim().Split([|' '|]) |> Seq.toList |> List.filter(fun e -> e.Length > 0)
