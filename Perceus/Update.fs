module Update

module T = Target
module I = Interpreter
module R = Runtime
module tic = Ticking
module A = Advancement
module Sig = signalStore

exception UpdateError of string


let updateOne (event: Interpreter.IncomingEvent) stepleftlimit (state:Runtime.State) = 
    match state.HeapEarlier with
    | heapEntry::rest -> 
        match tic.ticked event.Channel heapEntry.Future state.Heap state.HeapNow with
        | false -> 
            let updated = {heapEntry with Updated = false}
            {state with HeapEarlier = rest; HeapNow = state.HeapNow @ [updated]  }
        | true -> 
            let _ , state' = Interpreter.run stepleftlimit (T.Dup(heapEntry.Future, T.Var heapEntry.Future)) state
            let ref', state'' = A.advance heapEntry.Future event stepleftlimit state'
            let newSignal = Sig.lookup  ref' state''.HeapNow
            
            // Duplicating references because for a while we have 2 signals pointing to the same reference
            let protectFields = Interpreter.dupMany [newSignal.Current; newSignal.Future] (T.Var ref')
            let _, state''' = Interpreter.run stepleftlimit protectFields state''
            let updated = {heapEntry with Updated = true; Future = newSignal.Future; Current = newSignal.Current}
            let updatedState = {state''' with HeapEarlier = rest; HeapNow = state'''.HeapNow @ [updated]  } 
            
            // Release the old fields and our ownership of the returned signal.
            let cleanUp = Interpreter.dropMany [ heapEntry.Current; heapEntry.Future; ref' ](T.Var event.Value)
            let _, finalState = Interpreter.run stepleftlimit cleanUp updatedState
            finalState
    
    | [] -> state


let rec updateAll event stepleftlimit (state: Runtime.State) = 
    match state.HeapEarlier with 
    | [] -> state
    | _ -> 
        let newState = updateOne event stepleftlimit state
        updateAll event stepleftlimit newState

// helper function to release the reference where it might be  the last reference to something (cant do T.Drop(event.Value, T.Var event.Value) because the reference might not be in a heap anymore)
let releaseReference reference stepleftlimit (state: Runtime.State) =
    let rec finishCleanup stepsLeft expr (state: Runtime.State) =
        match expr with
        | T.Var _ ->
            state
        | _ ->
            if stepsLeft <= 0 then
                raise (Interpreter.InterpreterError "Step limit reached during cleanup.")
            let expr', state' =
                Interpreter.reduce expr state
            finishCleanup (stepsLeft - 1) expr' state'

    finishCleanup stepleftlimit
        (T.Drop(reference, T.Var reference))
        state



let reactToEvent event stepleftlimit (state: Runtime.State) =
    match state.HeapEarlier with
    | [] -> 
        let newState = {state with HeapEarlier = state.HeapNow; HeapNow = Sig.empty}
        let updatedState = updateAll event stepleftlimit newState
        releaseReference event.Value stepleftlimit updatedState

    | _ -> raise (UpdateError "Cannot start an event while earlier signals remain")