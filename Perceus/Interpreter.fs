module Interpreter

module T = Target

module H = heap

exception InterpreterError of string


// new Id for my heap, they are strings, because T.Var is a string
let rec newId nextId usedIds =
    let ref = T.Varr(string nextId)

    if Set.contains ref usedIds then
        newId (nextId + 1) usedIds
    else
        ref, (nextId + 1), Set.add ref usedIds

let isReference expr =
    match expr with
    | T.Var _ -> true
    | _ -> false

let getReference expr =
    match expr with
    | T.Var ref -> ref
    | _ -> raise (InterpreterError "expected a reference")

let rec dupMany references body =
    match references with
    | [] -> body
    | x :: rest -> T.Dup(x, dupMany rest body)

let rec dropMany references body =
    match references with
    | [] -> body
    | x :: rest -> T.Drop(x, dropMany rest body)

let rec reduce expr heap nextId usedIds =
    match expr with
    | T.Var reference ->
        H.lookup reference heap |> ignore // we just want to know if the reference is there

        expr, heap, nextId, usedIds
    //lamr - we are allocating the closure
    | T.Lambda(captures, param, body) ->
        let ref, nextId', usedIds' = newId nextId usedIds
        let newHeap = H.allocate ref (H.Closure(captures, param, body)) heap
        T.Var ref, newHeap, nextId', usedIds'
    //conr
    | T.Cons(name, fields) ->
        if List.forall isReference fields then
            let references = List.map getReference fields
            let ref, nextId', usedIds' = newId nextId usedIds
            let newHeap = H.allocate ref (H.ConstructorValue(name, references)) heap
            T.Var ref, newHeap, nextId', usedIds'
        else
            // in case there are fields that are not references - we reduce one field at a time
            let rec reduceField remaining =
                match remaining with
                | T.Var x :: rest ->
                    let rest', heap', nextId', usedIds' = reduceField rest
                    T.Var x :: rest', heap', nextId', usedIds'
                | current :: rest ->
                    let current', heap', nextId', usedIds' = reduce current heap nextId usedIds
                    current' :: rest, heap', nextId', usedIds'
                | [] -> raise (InterpreterError "No constructor field to reduce.")

            let fields', heap', nextId', usedIds' = reduceField fields
            T.Cons(name, fields'), heap', nextId', usedIds'
    //bindr
    | T.Let(x, value, body) ->
        match value with
        | T.Var reference ->
            //do not change the heap, just replace stuff
            let body' = Substitution.substituteOne x reference body
            body', heap, nextId, usedIds
        | _ ->
            let value', heap', nextId', usedIds' = reduce value heap nextId usedIds
            T.Let(x, value', body), heap', nextId', usedIds'
    //appr
    | T.App(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let entry = H.lookup leftRef heap

            match entry.Value with
            | H.Closure(captures, parameter, body) ->
                let body' = Substitution.substituteOne parameter rightRef body
                let expr' = dupMany captures (T.Drop(leftRef, body'))
                expr', heap, nextId, usedIds
            | H.ConstructorValue _ -> raise (InterpreterError "Cannot apply a constructor as a function.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', heap', nextId', usedIds' = reduce right heap nextId usedIds
            T.App(left, right'), heap', nextId', usedIds'
        | _, _ ->
            let left', heap', nextId', usedIds' = reduce left heap nextId usedIds
            T.App(left', right), heap', nextId', usedIds'
    //matchr
    | T.MatchVar(x, branches) ->
        let entry = H.lookup x heap

        match entry.Value with
        | H.ConstructorValue(name, fields) ->
            let selected =
                branches
                |> List.tryFind (fun branch ->
                    let (T.Pattern(patternName, _)) = branch.Pattern
                    patternName = name)

            match selected with
            | None -> raise (InterpreterError "No matching pattern.")
            | Some branch ->
                let (T.Pattern(_, binders)) = branch.Pattern

                let variables =
                    binders
                    |> List.map (function
                        | T.Variable x -> x
                        | T.Wildcard -> raise (InterpreterError "Wildcard."))

                let replacements = List.zip variables fields |> Map.ofList
                let body' = Substitution.substitute replacements branch.Body
                let expr' = dupMany fields (T.Drop(x, body'))
                expr', heap, nextId, usedIds
        | H.Closure _ -> raise (InterpreterError "Cannot match a closure as a constructor.")

    | T.Dup(ref, body) ->
        let heap' = H.dup ref heap
        body, heap', nextId, usedIds

    | T.Drop(ref, body) ->
        let heap', outcome = H.drop ref heap

        match outcome with
        | H.Decrement -> body, heap', nextId, usedIds
        | H.DropLastClosure captures -> dropMany captures body, heap', nextId, usedIds
        | H.DropLastConstructor fields -> dropMany fields body, heap', nextId, usedIds

    | T.MatchExpr _ -> //???
        raise (InterpreterError "Figure 7 uses MatchVar; MatchExpr is not supported.")


let rec run stepleftlimit expr heap nextId usedIds =
    match expr with
    | T.Var ref ->
        H.lookup ref heap |> ignore
        expr, heap, nextId, usedIds
    | _ ->
        if stepleftlimit <= 0 then
            raise (InterpreterError "Step limit reached.")

        let expr', heap', nextId', usedIds' = reduce expr heap nextId usedIds
        run (stepleftlimit - 1) expr' heap' nextId' usedIds'
