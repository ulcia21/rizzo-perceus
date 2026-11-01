module Interpreter

module T = Target

module H = heap

module Sig = signalStore

exception InterpreterError of string

type IncomingEvent = {
    Channel : T.Var
    Value : T.Var
}


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

let isExistential heapVal =
    match heapVal with
    | H.WaitingValue _ -> true
    | H.NeverValue -> true
    | H.ApplyWhenVValue _ -> true
    | H.SyncValue _ -> true
    | H.TailValue _ -> true
    | H.WatchValue _ -> true
    //add sync watch and tail here!!
    | _ -> false

let isUniversal heapVal =
    match heapVal with
    | H.DelayValue _ -> true
    | H.DelayAppValue _ -> true
    | _ -> false

let rec dupMany references body =
    match references with
    | [] -> body
    | x :: rest -> T.Dup(x, dupMany rest body)

let rec dropMany references body =
    match references with
    | [] -> body
    | x :: rest -> T.Drop(x, dropMany rest body)

let rec reduce expr heap heapNow heapEarlier nextId usedIds (functions: T.FunctionContext) =
    match expr with
    | T.Var reference ->
        H.lookup reference heap |> ignore // we just want to know if the reference is there

        expr, heap, heapNow, heapEarlier, nextId, usedIds
    //lamr - we are allocating the closure
    | T.Lambda(captures, param, body) ->
        let ref, nextId', usedIds' = newId nextId usedIds
        let newHeap = H.allocate ref (H.Closure(captures, param, body)) heap
        T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'
    //conr
    | T.Cons(name, fields) ->
        if List.forall isReference fields then
            let references = List.map getReference fields
            let ref, nextId', usedIds' = newId nextId usedIds
            let newHeap = H.allocate ref (H.ConstructorValue(name, references)) heap
            T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'
        else
            // in case there are fields that are not references - we reduce one field at a time
            let rec reduceField remaining =
                match remaining with
                | T.Var x :: rest ->
                    let rest', heap', heapNow', heapEarlier', nextId', usedIds' = reduceField rest
                    T.Var x :: rest', heap', heapNow', heapEarlier', nextId', usedIds'
                | current :: rest ->
                    let current', heap', heapNow', heapEarlier', nextId', usedIds' =
                        reduce current heap heapNow heapEarlier nextId usedIds functions

                    current' :: rest, heap', heapNow', heapEarlier', nextId', usedIds'
                | [] -> raise (InterpreterError "No constructor field to reduce.")

            let fields', heap', heapNow', heapEarlier', nextId', usedIds' = reduceField fields
            T.Cons(name, fields'), heap', heapNow', heapEarlier', nextId', usedIds'
    //bindr
    | T.Let(x, value, body) ->
        match value with
        | T.Var reference ->
            //do not change the heap, just replace stuff
            let body' = Substitution.substituteOne x reference body
            body', heap, heapNow, heapEarlier, nextId, usedIds
        | _ ->
            let value', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce value heap heapNow heapEarlier nextId usedIds functions

            T.Let(x, value', body), heap', heapNow', heapEarlier', nextId', usedIds'
    //appr
    | T.App(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let entry = H.lookup leftRef heap

            match entry.Value with
            | H.Closure(captures, parameter, body) ->
                let body' = Substitution.substituteOne parameter rightRef body
                let expr' = dupMany captures (T.Drop(leftRef, body'))
                expr', heap, heapNow, heapEarlier, nextId, usedIds
            | _ -> raise (InterpreterError "Expected a closure for function application.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce right heap heapNow heapEarlier nextId usedIds functions

            T.App(left, right'), heap', heapNow', heapEarlier', nextId', usedIds'
        | _, _ ->
            let left', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce left heap heapNow heapEarlier nextId usedIds functions

            T.App(left', right), heap', heapNow', heapEarlier', nextId', usedIds'
    //matchr
    | T.MatchExpr(x, branches) ->

        match x with
        | T.Var ref ->
            let entry = H.lookup ref heap

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
                    let expr' = dupMany fields (T.Drop(ref, body'))
                    expr', heap, heapNow, heapEarlier, nextId, usedIds
            | _ -> raise (InterpreterError "Expected a constructor value for pattern matching.")
        | _ ->
            let x', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce x heap heapNow heapEarlier nextId usedIds functions

            T.MatchExpr(x', branches), heap', heapNow', heapEarlier', nextId', usedIds'

    | T.Dup(ref, body) ->
        let heap' = H.dup ref heap
        body, heap', heapNow, heapEarlier, nextId, usedIds

    | T.Drop(ref, body) ->
        let heap', outcome = H.drop ref heap

        match outcome with
        | H.Decrement -> body, heap', heapNow, heapEarlier, nextId, usedIds
        | H.DropLastClosure captures -> dropMany captures body, heap', heapNow, heapEarlier, nextId, usedIds
        | H.DropLastConstructor fields -> dropMany fields body, heap', heapNow, heapEarlier, nextId, usedIds
        | H.DropLastValue chanRef -> T.Drop(chanRef, body), heap', heapNow, heapEarlier, nextId, usedIds
        | H.DropLastDelayedOperation(t, t') -> dropMany [ t; t' ] body, heap', heapNow, heapEarlier, nextId, usedIds
        | H.DropLastSignalValue ->
            let heapNow', outcome = Sig.drop ref heapNow

            match outcome with
            | Sig.DropSignalStoreValue(currentRef, futureRef) ->
                let body' = dropMany [ currentRef; futureRef ] body
                body', heap', heapNow', heapEarlier, nextId, usedIds

        | H.DropLastClean -> body, heap', heapNow, heapEarlier, nextId, usedIds


    | T.Function name ->
        match Map.tryFind name functions with
        | Some definition -> definition, heap, heapNow, heapEarlier, nextId, usedIds
        | None -> raise (InterpreterError "Unknown function looked up in FunctionContext")

    | T.Never ->
        let ref, nextId', usedIds' = newId nextId usedIds
        let newHeap = H.allocate ref (H.NeverValue) heap
        T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'

    | T.Chan name ->
        let ref, nextId', usedIds' = newId nextId usedIds
        let newHeap = H.allocate ref (H.ChannelValue name) heap
        T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'

    | T.Wait t ->
        match t with
        | T.Var chanRef ->
            match (H.lookup chanRef heap).Value with
            | H.ChannelValue _ ->
                let ref, nextId', usedIds' = newId nextId usedIds
                let newHeap = H.allocate ref (H.WaitingValue chanRef) heap
                T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'
            | _ -> raise (InterpreterError "Wait expects a channel")
        | _ ->
            let t', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce t heap heapNow heapEarlier nextId usedIds functions

            T.Wait t', heap', heapNow', heapEarlier', nextId', usedIds'

    | T.Delay(captures, t) ->
        let ref, nextId', usedIds' = newId nextId usedIds
        let newHeap = H.allocate ref (H.DelayValue(captures, t)) heap
        T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'

    | T.ApplyWhenV(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let leftEntry = H.lookup leftRef heap

            match isUniversal leftEntry.Value with
            | true ->
                let rightEntry = H.lookup rightRef heap

                match isExistential rightEntry.Value with
                | true ->
                    let ref, nextId', usedIds' = newId nextId usedIds
                    let newHeap = H.allocate ref (H.ApplyWhenVValue(leftRef, rightRef)) heap
                    T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'
                | _ -> raise (InterpreterError "Expected an existentially delayed operation for ApplyWhenV")
            | _ -> raise (InterpreterError "Expected an universally delayed function for ApplyWhenV.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce right heap heapNow heapEarlier nextId usedIds functions

            T.ApplyWhenV(left, right'), heap', heapNow', heapEarlier', nextId', usedIds'
        | _, _ ->
            let left', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce left heap heapNow heapEarlier nextId usedIds functions

            T.ApplyWhenV(left', right), heap', heapNow', heapEarlier', nextId', usedIds'

    | T.Sync(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let leftEntry = H.lookup leftRef heap

            match isExistential leftEntry.Value with
            | true ->
                let rightEntry = H.lookup rightRef heap

                match isExistential rightEntry.Value with
                | true ->
                    let ref, nextId', usedIds' = newId nextId usedIds
                    let newHeap = H.allocate ref (H.SyncValue(leftRef, rightRef)) heap
                    T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'
                | _ -> raise (InterpreterError "Expected an existentially delayed operation for Sync")
            | _ -> raise (InterpreterError "Expected an existentially delayed value for Sync.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce right heap heapNow heapEarlier nextId usedIds functions

            T.Sync(left, right'), heap', heapNow', heapEarlier', nextId', usedIds'
        | _, _ ->
            let left', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce left heap heapNow heapEarlier nextId usedIds functions

            T.Sync(left', right), heap', heapNow', heapEarlier', nextId', usedIds'
    | T.ApplyLater(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let leftEntry = H.lookup leftRef heap

            match isUniversal leftEntry.Value with
            | true ->
                let rightEntry = H.lookup rightRef heap

                match isUniversal rightEntry.Value with
                | true ->
                    let ref, nextId', usedIds' = newId nextId usedIds
                    let newHeap = H.allocate ref (H.DelayAppValue(leftRef, rightRef)) heap
                    T.Var ref, newHeap, heapNow, heapEarlier, nextId', usedIds'
                | _ -> raise (InterpreterError "Expected an universally delayed operation for ApplyLater")
            | _ -> raise (InterpreterError "Expected an universally delayed function for ApplyLater.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce right heap heapNow heapEarlier nextId usedIds functions

            T.ApplyLater(left, right'), heap', heapNow', heapEarlier', nextId', usedIds'
        | _, _ ->
            let left', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce left heap heapNow heapEarlier nextId usedIds functions

            T.ApplyLater(left', right), heap', heapNow', heapEarlier', nextId', usedIds'

    | T.SignalCons(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let rightEntry = H.lookup rightRef heap

            match isExistential rightEntry.Value with
            | true ->
                let ref, nextId', usedIds' = newId nextId usedIds
                let newHeapNow = Sig.allocate ref leftRef rightRef false heapNow
                let newHeap = H.allocate ref H.SignalValue heap
                T.Var ref, newHeap, newHeapNow, heapEarlier, nextId', usedIds'
            | false -> raise (InterpreterError "Expected an existentially delayed operation for SignalCons")
        | T.Var _, _ ->
            let (right': Target.Expr), heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce right heap heapNow heapEarlier nextId usedIds functions

            T.SignalCons(left, right'), heap', heapNow', heapEarlier', nextId', usedIds'
        | _, _ ->
            let left', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce left heap heapNow heapEarlier nextId usedIds functions

            T.SignalCons(left', right), heap', heapNow', heapEarlier', nextId', usedIds'

    | T.Head t ->
        match t with
        | T.Var ref ->
            match (H.lookup ref heap).Value with
            | H.SignalValue ->
                let x = (Sig.lookup ref heapNow)
                T.Dup(x.Current, T.Drop(ref, T.Var x.Current)), heap, heapNow, heapEarlier, nextId, usedIds
            | _ -> raise (InterpreterError "Argument for Head is supposed to have a reference to signal")
        | _ ->
            let t', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce t heap heapNow heapEarlier nextId usedIds functions

            T.Head t', heap', heapNow', heapEarlier', nextId', usedIds'

    | T.Tail t ->
        match t with
        | T.Var ref ->
            match (H.lookup ref heap).Value with
            | H.SignalValue ->
                let tailRef, nextId', usedIds' = newId nextId usedIds
                let newHeap = H.allocate tailRef (H.TailValue ref) heap
                T.Var tailRef, newHeap, heapNow, heapEarlier, nextId', usedIds'
            | _ -> raise (InterpreterError "Argument for Tail is supposed to have a reference to signal")
        | _ ->
            let t', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce t heap heapNow heapEarlier nextId usedIds functions

            T.Tail t', heap', heapNow', heapEarlier', nextId', usedIds'

    | T.Watch t ->
        match t with
        | T.Var ref ->
            match (H.lookup ref heap).Value with
            | H.SignalValue ->
                let watchRef, nextId', usedIds' = newId nextId usedIds
                let newHeap = H.allocate watchRef (H.WatchValue ref) heap
                T.Var watchRef, newHeap, heapNow, heapEarlier, nextId', usedIds'
            | _ -> raise (InterpreterError "Argument for watch is supposed to have a reference to signal")
        | _ ->
            let t', heap', heapNow', heapEarlier', nextId', usedIds' =
                reduce t heap heapNow heapEarlier nextId usedIds functions

            T.Watch t', heap', heapNow', heapEarlier', nextId', usedIds'






let rec run stepleftlimit expr heap heapNow heapEarlier nextId usedIds (functions: T.FunctionContext) =
    match expr with
    | T.Var ref ->
        H.lookup ref heap |> ignore
        expr, heap, heapNow, heapEarlier, nextId, usedIds
    | _ ->
        if stepleftlimit <= 0 then
            raise (InterpreterError "Step limit reached.")

        let expr', heap', heapNow', heapEarlier', nextId', usedIds' =
            reduce expr heap heapNow heapEarlier nextId usedIds functions

        run (stepleftlimit - 1) expr' heap' heapNow' heapEarlier' nextId' usedIds' functions
