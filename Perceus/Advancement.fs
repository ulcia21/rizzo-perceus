module Advancement

module T = Target

module H = heap

module Sig = signalStore

module Inter = Interpreter

module R = Runtime

module tic = Ticking

exception AdvanceError of string

//helper to evaluate universally delayed computations referenced inside some cases 
let rec evaluateUniversal delayedRef stepleftlimit (state: R.State) =
    match (H.lookup delayedRef state.Heap).Value with
    | H.DelayValue(captures, body) ->
        let expr = Interpreter.dupMany captures (T.Drop(delayedRef, body))

        Interpreter.run stepleftlimit expr state
        
    | H.DelayAppValue(left, right) ->
        let expr' = Interpreter.dupMany [left; right] (T.Drop(delayedRef, T.Var left))
        let _, newState = Interpreter.run stepleftlimit expr' state
        let funLeft, state' = evaluateUniversal left stepleftlimit newState
        let argRight, finalState = evaluateUniversal right stepleftlimit state'
        
        Interpreter.run stepleftlimit (T.App(T.Var funLeft, T.Var argRight)) finalState

    | _ ->
        raise (
            AdvanceError
                "Expected a universal delayed computation"
        )



let rec advance ref (event:Inter.IncomingEvent) stepleftlimit (state: R.State) =
    match (H.lookup ref (state.Heap)).Value with 
    | H.WaitingValue chanRef -> 
        match event.Channel = chanRef with
        | true -> 
            let newExpr = T.Dup (event.Value, T.Drop(ref, T.Var event.Value))
            let resultRef, state'  = Interpreter.run stepleftlimit newExpr state
            resultRef, state'
        | false -> raise (AdvanceError "Provided wrong channel reference")
    | H.TailValue sigRef -> 
        let newExpr = T.Dup(sigRef, T.Drop(ref, T.Var sigRef))
        let resultRef, state' = Interpreter.run stepleftlimit newExpr state
        resultRef, state'
    | H.WatchValue sigRef ->    
        let x = Sig.lookup sigRef state.HeapNow
        match (H.lookup x.Current state.Heap).Value with
        | H.ConstructorValue(T.Constructor "Inl", [inlRef]) -> 
            let newExpr = T.Dup(inlRef, T.Drop(ref, T.Var inlRef))
            let resultRef, state' = Interpreter.run stepleftlimit newExpr state
            resultRef, state'
        | _ -> raise (AdvanceError "Watch expected Inl value with one field")
    | H.ApplyWhenVValue(functionRef, argRef) -> 
        let _, state' = Interpreter.run stepleftlimit (T.Dup(argRef, T.Var argRef )) state
        let argAdvancedRef, state'' = advance argRef event stepleftlimit state'

        let _, state''' = Interpreter.run stepleftlimit (T.Dup(functionRef,T.Drop(ref, T.Var functionRef))) state''
        let realFunctionRef, state'''' = evaluateUniversal functionRef stepleftlimit state'''

        Interpreter.run stepleftlimit (T.App(T.Var realFunctionRef, T.Var argAdvancedRef)) state''''

    | H.SyncValue(left, right) -> 
        let leftTicked =  tic.ticked event.Channel left state.Heap state.HeapNow
        let rightTicked =  tic.ticked event.Channel right state.Heap state.HeapNow
        match leftTicked, rightTicked with
        | true, true ->
            let expr = Interpreter.dupMany [left; right] (T.Drop(ref, T.Var left))
            let _, state' = Interpreter.run stepleftlimit expr state
            let advancedLeftValueRef, state'' = advance left event stepleftlimit state'
            let advancedRightValueRef, state''' = advance right event stepleftlimit state''
            Interpreter.run stepleftlimit (T.Cons(T.Constructor "Inr",[ T.Cons(T.Constructor "Pair",[ T.Var advancedLeftValueRef; T.Var advancedRightValueRef ]) ])) state'''

        | true, false -> 
            let newExpr = T.Dup(left, T.Drop(ref, T.Var left))
            let _, state' = Interpreter.run stepleftlimit newExpr state
            let advancedValueRef, state'' = advance left event stepleftlimit state'
            Interpreter.run stepleftlimit (T.Cons(T.Constructor "Inl",[ T.Cons(T.Constructor "Inl",[ T.Var advancedValueRef ]) ])) state''
        | false, true -> 
            let newExpr = T.Dup(right, T.Drop(ref, T.Var right))
            let _, state' = Interpreter.run stepleftlimit newExpr state
            let advancedValueRef, state'' = advance right event stepleftlimit state'
            Interpreter.run stepleftlimit (T.Cons(T.Constructor "Inl",[ T.Cons(T.Constructor "Inr",[ T.Var advancedValueRef ]) ])) state''
        | _ -> raise (AdvanceError "Nothing ticked!") 

    | _ -> raise (AdvanceError "bad")


