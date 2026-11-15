module Update

module T = Target
module I = Interpreter
module R = Runtime
module tic = Ticking
module A = Advancement
module Sig = signalStore


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

