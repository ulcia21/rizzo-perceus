module Ticking

module T = Target
module H = heap
module Sig = signalStore

exception TickError of string

let rec ticked channelRef delayedRef heap heapNow= 
    match (H.lookup delayedRef heap).Value with 
    | H.WaitingValue chanRef -> if channelRef = chanRef then true else false
    | H.ApplyWhenVValue ( _ , ref2) -> ticked channelRef ref2 heap heapNow
    | H.SyncValue (ref1, ref2) -> ticked channelRef ref1 heap heapNow || ticked channelRef ref2 heap heapNow
    | H.TailValue sigRef -> 
        match List.tryFind (fun (entry: Sig.SignalStoreEntry) -> entry.Reference = sigRef) heapNow with
        | Some x -> x.Updated = true
        | None -> false
    | H.WatchValue sigRef ->
        match List.tryFind (fun (entry: Sig.SignalStoreEntry) -> entry.Reference = sigRef) heapNow with
        | Some x -> 
            if x.Updated = true then 
                match (H.lookup x.Current heap).Value with
                    | H.ConstructorValue(T.Constructor "Inl", [_]) -> true
                    | _ -> false
            else false
        | None -> false
    | H.NeverValue -> false
    | _ -> raise (TickError "Ticked function used with a reference pointing to wrong value")
     
