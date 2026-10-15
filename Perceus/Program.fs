// For more information see https://aka.ms/fsharp-console-apps
module Perceus


Tests.run "variable" Tests.testVar

Tests.run "lambda used" Tests.testLambdaUsed
// Expected: Lambda (Varr "x", Var (Varr "x"))

Tests.run "lambda unused" Tests.testLambdaUnused
// Expected: Lambda (Varr "x", Drop (Varr "x", Lambda (Varr "y", Var (Varr "y"))))

Tests.run "application" Tests.testApp
// Expected: App (Var (Varr "f"), Var (Varr "x"))

Tests.runIdentityFunctionTest ()
