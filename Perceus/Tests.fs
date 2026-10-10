module Tests

module S = Source
module T = Target

open Elaborator

let run name expr =
    try
        let result = elaborateOpen expr
        printfn "%s:" name
        printfn "%A" result
        printfn ""
    with ElaborationError msg ->
        printfn "%s FAILED: %s" name msg

let x = S.Varr "x"
let y = S.Varr "y"
let f = S.Varr "f"

let testVar = S.Var x

let testLambdaUsed = S.Lambda(x, S.Var x)

let testLambdaUnused = S.Lambda(x, S.Lambda(y, S.Var y))

let testApp = S.App(S.Var f, S.Var x)
