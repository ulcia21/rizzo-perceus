module FreeAndBoundVars

module S = Source

//bound variables - the variables introduced by pattern as new local bindings
// the functions answers the question which variables the pattern introduced as new local bindings
//so extracts all named variables introduced by a pattern, ignoring wildcards, so that branch-local
// variables are not mistakenly treated as free variables.
// Wildcard says: There is a value in this position, but I do not want to give it a variable name.
let boundVars (S.Pattern(_, binders)) =
    binders
    |> List.choose (function
        | S.Variable x -> Some x
        | S.Wildcard -> None)
    |> Set.ofList

// list.choose requires a function that returns an option and makes a list of Somes (and discards Nones)


// finding free variables of a given expression
// how: x is free when there is no binder around x in the expression.
// we confirm it with Figure 8: the variable rule translates x under an environment containing x,
// which only makes sense because x is the free variable of that expression.
let rec freeVarsExpr expr =
    match expr with
    | S.Var x -> Set.singleton x
    | S.Lambda(x, body) -> Set.remove x (freeVarsExpr body)
    | S.Cons(_, exprl) -> exprl |> List.map freeVarsExpr |> Set.unionMany
    | S.App(e1, e2) -> Set.union (freeVarsExpr e1) (freeVarsExpr e2)
    | S.Let(x, e1, e2) -> Set.union (Set.remove x (freeVarsExpr e2)) (freeVarsExpr e1)
    | S.Match(x, branches) ->
        let branchFreeVars =
            branches
            |> List.map (fun branch -> Set.difference (freeVarsExpr branch.Body) (boundVars branch.Pattern))
            |> Set.unionMany

        Set.add x branchFreeVars

// Match for each branch takes all the free variables of the body minus the variables that are introduced by the pattern
// and later used in that body (so those are bound!) In the end it adds x because it was never binded anywhere (just pattern matched on)
