module heap

module T = Target

type HeapValue =
    | Closure of captures: T.Var list * parameter: T.Var * body: T.Expr
    | ConstructorValue of T.Constructor * T.Var list

type HeapEntry = { RefCount: int; Value: HeapValue }

type Heap = Map<T.Var, HeapEntry>

exception HeapError of string

//dup has only one possible outcome, but for Drop there are 3 options
type DropOption =
    | Decrement
    | DropLastClosure of T.Var list
    | DropLastConstructor of T.Var list

let empty: Heap = Map.empty

let lookup ref (heap: Heap) =
    match Map.tryFind ref heap with
    | Some x -> x
    | None -> raise (HeapError(sprintf "Missing heap reference %A" ref))

let allocate ref value (heap: Heap) =
    if Map.containsKey ref heap then
        raise (HeapError(sprintf "Reference already allocated: %A" ref))

    Map.add ref { RefCount = 1; Value = value } heap

let dup ref heap =
    let entry = lookup ref heap

    Map.add
        ref
        { RefCount = entry.RefCount + 1
          Value = entry.Value }
        heap

let drop ref heap =
    let entry = lookup ref heap

    if entry.RefCount > 1 then
        Map.add
            ref
            { RefCount = entry.RefCount - 1
              Value = entry.Value }
            heap,
        Decrement
    elif entry.RefCount = 1 then
        let newHeap = Map.remove ref heap

        match entry.Value with
        | Closure(captures, _, _) -> newHeap, DropLastClosure captures
        | ConstructorValue(_, valList) -> newHeap, DropLastConstructor valList
    else
        raise (HeapError "Heap entries must have positive reference counts.")
