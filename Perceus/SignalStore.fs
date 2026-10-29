module signalStore

module T = Target

type SignalStoreEntry =
    { Reference: T.Var
      Current: T.Var
      Future: T.Var
      Updated: bool }

type SignalStore = List<SignalStoreEntry>

type DropOption = DropSignalStoreValue of T.Var * T.Var

exception SignalStoreError of string

let empty: SignalStore = List.empty

let lookup ref (heap: SignalStore) =
    match List.tryFind (fun entry -> entry.Reference = ref) heap with
    | Some x -> x
    | None -> raise (SignalStoreError(sprintf "Missing heap reference %A" ref))

let allocate ref current future updated (heap: SignalStore) =
    if List.exists(fun entry -> entry.Reference = ref) heap then
        raise (SignalStoreError(sprintf "Reference already allocated: %A" ref))

    List.append
        heap
        [{ 
          Reference =ref
          Current = current
          Future = future
          Updated = updated }]
        

let drop ref heap =
    let x = lookup ref heap
    let newHeap = List.filter (fun entry -> entry.Reference <> ref) heap
    newHeap, DropSignalStoreValue(x.Current, x.Future)
