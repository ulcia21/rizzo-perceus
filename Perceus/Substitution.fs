module Substitution

module T = Target

let rec substitute (replacements: Map<T.Var, T.Var>) expr =
    // find x in the map, else use x (try find returns an option)
    let replace x =
        Map.tryFind x replacements |> Option.defaultValue x

    let visitBranch (branch: T.MatchElem) =
        let (T.Pattern(_, binders)) = branch.Pattern // Pattern is a constructor with a list of binders
        //removes substitutions for variables introduced by the branch’s pattern.
        //Those variables are local to the branch, so an outside substitution must not replace them.
        let localReplacements =
            binders
            |> List.fold
                (fun current binder ->
                    match binder with
                    | T.Variable x -> Map.remove x current
                    | T.Wildcard -> current)
                replacements

        { branch with
            Body = substitute localReplacements branch.Body }

    match expr with
    | T.Var x -> T.Var(replace x)
    | T.Lambda(captures, parameter, body) ->
        T.Lambda(List.map replace captures, parameter, substitute (Map.remove parameter replacements) body)
    | T.App(left, right) -> T.App(substitute replacements left, substitute replacements right)
    | T.Let(x, value, body) -> T.Let(x, substitute replacements value, substitute (Map.remove x replacements) body)
    | T.Cons(name, fields) -> T.Cons(name, List.map (substitute replacements) fields)
    | T.Dup(x, body) -> T.Dup(replace x, substitute replacements body)
    | T.Drop(x, body) -> T.Drop(replace x, substitute replacements body)
    | T.MatchVar(x, branches) -> T.MatchVar(replace x, List.map visitBranch branches)
    | T.MatchExpr(value, branches) -> T.MatchExpr(substitute replacements value, List.map visitBranch branches)
    | T.Function _ -> expr

let substituteOne variable ref expr =
    substitute (Map.ofList [ variable, ref ]) expr
