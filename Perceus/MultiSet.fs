module MultiSet

type MultiSet<'a when 'a: comparison> = Map<'a, int>

// corresponds to the elaborator's empty set
let empty: MultiSet<'a> = Map.empty

let singleton x : MultiSet<'a> = Map.ofList [ x, 1 ]

let count x (m: MultiSet<'a>) =
    Map.tryFind x m |> Option.defaultValue 0

let addnCopies x n (m: MultiSet<'a>) =
    if n <= 0 then m else Map.add x ((count x m) + n) m

let sum (first: MultiSet<'a>) (second: MultiSet<'a>) =
    Map.fold (fun acc key value -> addnCopies key value acc) first second

let sumMany (sets: MultiSet<'a> list) = List.fold sum empty sets

// for Gamma - Gamma1, for multisets it's different than normal set operations, because the count counts
let difference (first: MultiSet<'a>) (second: MultiSet<'a>) =
    Map.fold
        (fun acc k v ->
            let remaining = v - count k second
            if remaining > 0 then Map.add k remaining acc else acc)
        Map.empty
        first

let intersection (first: MultiSet<'a>) (second: MultiSet<'a>) =
    Map.fold
        (fun acc k v ->
            let common = min v (count k second)
            if common > 0 then Map.add k common acc else acc)
        Map.empty
        first

//Converts an ordinary set into a multiset, giving every element multiplicity 1.
let setToMultiSet (xs: Set<'a>) : MultiSet<'a> =
    xs |> Seq.map (fun x -> x, 1) |> Map.ofSeq

//converts a multiset to a normal set
let toSet (m: MultiSet<'a>) =
    m |> Map.toSeq |> Seq.map fst |> Set.ofSeq

//toList - to do later, needed for one function in the elaborator

let isEmpty (m: MultiSet<'a>) = Map.isEmpty m

let contains x (m: MultiSet<'a>) = count x m > 0

//Checks that every element occurs exactly once.
let allMultiplicityOne (m: MultiSet<'a>) = Map.forall (fun _ n -> n = 1) m

let toList (m: MultiSet<'a>) =
    m |> Map.toList |> List.collect (fun (x, n) -> List.replicate n x)
