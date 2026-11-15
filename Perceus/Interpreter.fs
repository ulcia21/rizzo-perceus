module Interpreter

module T = Target

module H = heap

module Sig = signalStore

module R = Runtime

exception InterpreterError of string

type IncomingEvent = {
    Channel : T.Var
    Value : T.Var
}


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

let rec reduce expr (state: R.State) =
    match expr with
    | T.Var reference ->
        H.lookup reference state.Heap |> ignore // we just want to know if the reference is there

        expr, state
    //lamr - we are allocating the closure
    | T.Lambda(captures, param, body) ->
        let ref, nextId', usedIds' = newId state.NextId state.UsedIds
        let newHeap = H.allocate ref (H.Closure(captures, param, body)) state.Heap
        T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }
    //conr
    | T.Cons(name, fields) ->
        if List.forall isReference fields then
            let references = List.map getReference fields
            let ref, nextId', usedIds' = newId state.NextId state.UsedIds
            let newHeap = H.allocate ref (H.ConstructorValue(name, references)) state.Heap
            T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }
        else
            // in case there are fields that are not references - we reduce one field at a time
            let rec reduceField remaining =
                match remaining with
                | T.Var x :: rest ->
                    let rest', state' = reduceField rest
                    T.Var x :: rest', state'
                | current :: rest ->
                    let current', state' =
                        reduce current state

                    current' :: rest, state'
                | [] -> raise (InterpreterError "No constructor field to reduce.")

            let fields', state' = reduceField fields
            T.Cons(name, fields'), state'
    //bindr
    | T.Let(x, value, body) ->
        match value with
        | T.Var reference ->
            //do not change the heap, just replace stuff
            let body' = Substitution.substituteOne x reference body
            body', state
        | _ ->
            let value', state' =
                reduce value state

            T.Let(x, value', body), state'
    //appr
    | T.App(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let entry = H.lookup leftRef state.Heap

            match entry.Value with
            | H.Closure(captures, parameter, body) ->
                let body' = Substitution.substituteOne parameter rightRef body
                let expr' = dupMany captures (T.Drop(leftRef, body'))
                expr', state
            | _ -> raise (InterpreterError "Expected a closure for function application.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', state' =
                reduce right state

            T.App(left, right'), state'
        | _, _ ->
            let left', state' =
                reduce left state

            T.App(left', right), state'
    //matchr
    | T.MatchExpr(x, branches) ->

        match x with
        | T.Var ref ->
            let entry = H.lookup ref state.Heap

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
                    expr', state
            | _ -> raise (InterpreterError "Expected a constructor value for pattern matching.")
        | _ ->
            let x', state' =
                reduce x state

            T.MatchExpr(x', branches), state'

    | T.Dup(ref, body) ->
        let heap' = H.dup ref state.Heap
        body, { state with Heap = heap' }

    | T.Drop(ref, body) ->
        let heap', outcome = H.drop ref state.Heap

        match outcome with
        | H.Decrement -> body, { state with Heap = heap' }
        | H.DropLastClosure captures -> dropMany captures body, { state with Heap = heap' }
        | H.DropLastConstructor fields -> dropMany fields body, { state with Heap = heap' }
        | H.DropLastValue chanRef -> T.Drop(chanRef, body), { state with Heap = heap' }
        | H.DropLastDelayedOperation(t, t') -> dropMany [ t; t' ] body, { state with Heap = heap' }
        | H.DropLastSignalValue ->
            let heapNow', outcome = Sig.drop ref state.HeapNow

            match outcome with
            | Sig.DropSignalStoreValue(currentRef, futureRef) ->
                let body' = dropMany [ currentRef; futureRef ] body
                body', { state with Heap = heap'; HeapNow = heapNow' }

        | H.DropLastClean -> body, { state with Heap = heap' }


    | T.Function name ->
        match Map.tryFind name state.Functions with
        | Some definition -> definition, state
        | None -> raise (InterpreterError "Unknown function looked up in FunctionContext")

    | T.Never ->
        let ref, nextId', usedIds' = newId state.NextId state.UsedIds
        let newHeap = H.allocate ref (H.NeverValue) state.Heap
        T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }

    | T.Chan name ->
        let ref, nextId', usedIds' = newId state.NextId state.UsedIds
        let newHeap = H.allocate ref (H.ChannelValue name) state.Heap
        T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }

    | T.Wait t ->
        match t with
        | T.Var chanRef ->
            match (H.lookup chanRef state.Heap).Value with
            | H.ChannelValue _ ->
                let ref, nextId', usedIds' = newId state.NextId state.UsedIds
                let newHeap = H.allocate ref (H.WaitingValue chanRef) state.Heap
                T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }
            | _ -> raise (InterpreterError "Wait expects a channel")
        | _ ->
            let t', state' =
                reduce t state

            T.Wait t', state'

    | T.Delay(captures, t) ->
        let ref, nextId', usedIds' = newId state.NextId state.UsedIds
        let newHeap = H.allocate ref (H.DelayValue(captures, t)) state.Heap
        T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }

    | T.ApplyWhenV(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let leftEntry = H.lookup leftRef state.Heap

            match isUniversal leftEntry.Value with
            | true ->
                let rightEntry = H.lookup rightRef state.Heap

                match isExistential rightEntry.Value with
                | true ->
                    let ref, nextId', usedIds' = newId state.NextId state.UsedIds
                    let newHeap = H.allocate ref (H.ApplyWhenVValue(leftRef, rightRef)) state.Heap
                    T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }
                | _ -> raise (InterpreterError "Expected an existentially delayed operation for ApplyWhenV")
            | _ -> raise (InterpreterError "Expected an universally delayed function for ApplyWhenV.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', state' =
                reduce right state

            T.ApplyWhenV(left, right'), state'
        | _, _ ->
            let left', state' =
                reduce left state

            T.ApplyWhenV(left', right), state'

    | T.Sync(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let leftEntry = H.lookup leftRef state.Heap

            match isExistential leftEntry.Value with
            | true ->
                let rightEntry = H.lookup rightRef state.Heap

                match isExistential rightEntry.Value with
                | true ->
                    let ref, nextId', usedIds' = newId state.NextId state.UsedIds
                    let newHeap = H.allocate ref (H.SyncValue(leftRef, rightRef)) state.Heap
                    T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }
                | _ -> raise (InterpreterError "Expected an existentially delayed operation for Sync")
            | _ -> raise (InterpreterError "Expected an existentially delayed value for Sync.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', state' =
                reduce right state

            T.Sync(left, right'), state'
        | _, _ ->
            let left', state' =
                reduce left state

            T.Sync(left', right), state'
    | T.ApplyLater(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let leftEntry = H.lookup leftRef state.Heap

            match isUniversal leftEntry.Value with
            | true ->
                let rightEntry = H.lookup rightRef state.Heap

                match isUniversal rightEntry.Value with
                | true ->
                    let ref, nextId', usedIds' = newId state.NextId state.UsedIds
                    let newHeap = H.allocate ref (H.DelayAppValue(leftRef, rightRef)) state.Heap
                    T.Var ref, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }
                | _ -> raise (InterpreterError "Expected an universally delayed operation for ApplyLater")
            | _ -> raise (InterpreterError "Expected an universally delayed function for ApplyLater.")
        | T.Var _, _ -> //left side ready, right not yet
            let right', state' =
                reduce right state

            T.ApplyLater(left, right'), state'
        | _, _ ->
            let left', state' =
                reduce left state

            T.ApplyLater(left', right), state'

    | T.SignalCons(left, right) ->
        match left, right with
        | T.Var leftRef, T.Var rightRef ->
            let rightEntry = H.lookup rightRef state.Heap

            match isExistential rightEntry.Value with
            | true ->
                let ref, nextId', usedIds' = newId state.NextId state.UsedIds
                let newHeapNow = Sig.allocate ref leftRef rightRef false state.HeapNow
                let newHeap = H.allocate ref H.SignalValue state.Heap
                T.Var ref, { state with Heap = newHeap; HeapNow = newHeapNow; NextId = nextId'; UsedIds = usedIds' }
            | false -> raise (InterpreterError "Expected an existentially delayed operation for SignalCons")
        | T.Var _, _ ->
            let (right': Target.Expr), state' =
                reduce right state

            T.SignalCons(left, right'), state'
        | _, _ ->
            let left', state' =
                reduce left state

            T.SignalCons(left', right), state'

    | T.Head t ->
        match t with
        | T.Var ref ->
            match (H.lookup ref state.Heap).Value with
            | H.SignalValue ->
                let x = (Sig.lookup ref state.HeapNow)
                T.Dup(x.Current, T.Drop(ref, T.Var x.Current)), state
            | _ -> raise (InterpreterError "Argument for Head is supposed to have a reference to signal")
        | _ ->
            let t', state' =
                reduce t state

            T.Head t', state'

    | T.Tail t ->
        match t with
        | T.Var ref ->
            match (H.lookup ref state.Heap).Value with
            | H.SignalValue ->
                let tailRef, nextId', usedIds' = newId state.NextId state.UsedIds
                let newHeap = H.allocate tailRef (H.TailValue ref) state.Heap
                T.Var tailRef, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }
            | _ -> raise (InterpreterError "Argument for Tail is supposed to have a reference to signal")
        | _ ->
            let t', state' =
                reduce t state

            T.Tail t', state'

    | T.Watch t ->
        match t with
        | T.Var ref ->
            match (H.lookup ref state.Heap).Value with
            | H.SignalValue ->
                let watchRef, nextId', usedIds' = newId state.NextId state.UsedIds
                let newHeap = H.allocate watchRef (H.WatchValue ref) state.Heap
                T.Var watchRef, { state with Heap = newHeap; NextId = nextId'; UsedIds = usedIds' }
            | _ -> raise (InterpreterError "Argument for watch is supposed to have a reference to signal")
        | _ ->
            let t', state' =
                reduce t state

            T.Watch t', state'






let rec run stepleftlimit expr (state: R.State) =
    match expr with
    | T.Var ref ->
        H.lookup ref state.Heap |> ignore
        ref, state 
    | _ ->
        if stepleftlimit <= 0 then
            raise (InterpreterError "Step limit reached.")

        let expr', state' =
            reduce expr state

        run (stepleftlimit - 1) expr' state'
