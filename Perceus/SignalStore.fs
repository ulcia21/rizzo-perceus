module signalStore

module T = Target

type SignalStoreEntry =
    { Current: T.Var
      Future: T.Var
      Updated: bool }

type SignalStore = Map<T.Var, SignalStoreEntry>

type DropOption = DropSignalStoreValue of T.Var * T.Var

exception SignalStoreError of string

let empty: SignalStore = Map.empty

let lookup ref (heap: SignalStore) =
    match Map.tryFind ref heap with
    | Some x -> x
    | None -> raise (SignalStoreError(sprintf "Missing heap reference %A" ref))

let allocate ref current future updated (heap: SignalStore) =
    if Map.containsKey ref heap then
        raise (SignalStoreError(sprintf "Reference already allocated: %A" ref))

    Map.add
        ref
        { Current = current
          Future = future
          Updated = updated }
        heap

let drop ref heap =
    let x = lookup ref heap
    let newHeap = Map.remove ref heap
    newHeap, DropSignalStoreValue(x.Current, x.Future)
