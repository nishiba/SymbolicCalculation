#load "Library1.fs"
open expression

let x = Var "x"
let y = Var "y"
let z = Var "z"

let c1 = Const(1.)
let c2 = Const(2.)
let c3 = Const(3.)

;;

printfn "1"
Format(Sort((x + y * x + c3) + (x + c1)));;
printfn "2"
Format(Sort((x + c1) + (x + c1)));;
printfn "3"
Format(Expand(y * (x + c1)));;
printfn "4"
Format(Expand((x + c1) * y));;
printfn "5"
Format(Expand((x + c1) * (x - y)));;
printfn "6"
Format(Expand((x + c1) - (x + c1)));;
printfn "7"
Format(Simplify((x + c1) - (x + c1)));;
printfn "8"
Format(Simplify(x + x));;
printfn "9"
Format(Simplify(c2 * x +  c2 * x));;
printfn "10"
Format(Simplify(x +  c3 * x));;
printfn "11"
Format(Simplify(c2 * x +  c3 * x));;
printfn "12"
Format(Simplify(c2 * x * y +  c3 * x * y));;
printfn "13"
Format(Sort(z + c2 * x));;
printfn "14"
Format(Simplify(c2 * x + (x * y + c2 * x + z)));;
printfn "15"
Format(Simplify((x + x)/ x));;
printfn "16"
Format(Simplify((x * y)/ x));;
printfn "17"
Format(Simplify( (x + (-y)) ));;
printfn "18"
Format((x + c1) * (y + c1) * z);;
printfn "19"
Format(Simplify(Pow(x, c1) * Pow(x, c2)));;
printfn "20"
Format(Simplify(Pow(x, c1)));;
printfn "21"
Elements(c2 * x + (x * y + c2 * x + z));;
printfn "22"
Format(Differentiate(3. * x * x + 2. * x, x, 1));;
printfn "22"
Format(Differentiate(4. * x * x + 2. * x, x, 2));;
printfn "23"
Format(Integrate(4. * x * x + 2. * y + 3., x));;
printfn "24"
Format(Differentiate(1. / x, x, 1));;


Format(Simplify(Const(1.) / Const(2.)));;

printfn "-- end -- "
