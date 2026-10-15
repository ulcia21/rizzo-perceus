module Tests

module S = Source
module T = Target
module H = heap

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

let unitValue = S.Cons(S.Constructor "Unit", [])
let value reference memory = (H.lookup reference memory).Value

let expect condition message =
    if not condition then
        failwith message

let testVar = S.Var x

let testLambdaUsed = S.Lambda(x, S.Var x)

let testLambdaUnused = S.Lambda(x, S.Lambda(y, S.Var y))

let testApp = S.App(S.Var f, S.Var x)

let runIdentityFunctionTest () =
    let identity = S.Lambda(S.Varr "x", S.Var(S.Varr "x"))
    let functions: T.FunctionContext = Map.ofList [ "identity", elaborate identity ]

    let source = S.App(S.Function "identity", unitValue)

    let result, memory, now, _ =
        Interpreter.run 100 (elaborate source) H.empty 0 Set.empty functions

    let reference = Interpreter.getReference result
    expect (value reference memory = H.ConstructorValue(T.Constructor "Unit", [])) "Identity test failed"


let mapDefinition =
    let nil = S.Cons(S.Constructor "Nil", [])

    let cons head tail =
        S.Cons(S.Constructor "Cons", [ head; tail ])

    S.Lambda(
        S.Varr "f",
        S.Lambda(
            S.Varr "xs",
            S.Match(
                S.Varr "xs",
                [ { Pattern = S.Pattern(S.Constructor "Nil", [])
                    Body = nil }
                  { Pattern = S.Pattern(S.Constructor "Cons", [ S.Variable(S.Varr "head"); S.Variable(S.Varr "tail") ])
                    Body =
                      cons
                          (S.App(S.Var(S.Varr "f"), S.Var(S.Varr "head")))
                          (S.App(S.App(S.Function "map", S.Var(S.Varr "f")), S.Var(S.Varr "tail"))) } ]
            )
        )
    )

let mapFunctions: T.FunctionContext = Map.ofList [ "map", elaborate mapDefinition ]

let mapTest =
    let zero = S.Cons(S.Constructor "Zero", [])
    let nil = S.Cons(S.Constructor "Nil", [])

    let cons head tail =
        S.Cons(S.Constructor "Cons", [ head; tail ])

    let increment =
        S.Lambda(S.Varr "n", S.Cons(S.Constructor "Succ", [ S.Var(S.Varr "n") ]))

    S.Let(S.Varr "x", cons zero (cons zero nil), S.App(S.App(S.Function "map", increment), S.Var(S.Varr "x")))

let target = elaborate mapTest

let result, memory, heap, _ =
    Interpreter.run 100 target H.empty 0 Set.empty mapFunctions

// Read natural numbers and lists from the resulting heap.
let rec readNat memory reference =
    match (H.lookup reference memory).Value with
    | H.ConstructorValue(T.Constructor "Zero", []) -> 0
    | H.ConstructorValue(T.Constructor "Succ", [ n ]) -> 1 + readNat memory n
    | _ -> failwith "Expected a natural number."

let rec readList memory reference =
    match (H.lookup reference memory).Value with
    | H.ConstructorValue(T.Constructor "Nil", []) -> []
    | H.ConstructorValue(T.Constructor "Cons", [ head; tail ]) -> readNat memory head :: readList memory tail
    | _ -> failwith "Expected a list."

// Execute the test and check the result.
let runMapTest () =
    let target = elaborate mapTest

    let result, memory, _, _ =
        Interpreter.run 10000 target H.empty 0 Set.empty mapFunctions

    let resultReference = Interpreter.getReference result
    let answer = readList memory resultReference

    if answer <> [ 1; 1 ] then
        failwithf "Expected [1; 1], got %A" answer

    printfn "PASS map successor: %A" answer
