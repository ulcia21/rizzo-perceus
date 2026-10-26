module Elaborator

module S = Source
module T = Target

open FreeAndBoundVars


// --------------------------------------------------------
// converting source types to target types
// --------------------------------------------------------
let toTargetVar (S.Varr x) = T.Varr x

let toTargetConstructor (S.Constructor c) = T.Constructor c

let toTargetBinder binder =
    match binder with
    | S.Variable x -> T.Variable(toTargetVar x)

    | S.Wildcard -> T.Wildcard

let toTargetPattern (S.Pattern(constructor, binders)) =
    T.Pattern(toTargetConstructor constructor, binders |> List.map toTargetBinder)

// --------------------------------------------------------
// DUP and DROP HELPERS
//
// dupMany {x,y} becomes
//
// dup x;
// dup y;
// e
// --------------------------------------------------------

let dupMany (variables: Set<S.Var>) (expr: T.Expr) : T.Expr =

    List.foldBack (fun x acc -> T.Dup(toTargetVar x, acc)) (Set.toList variables) expr

let dropMany (variables: Set<S.Var>) (expr: T.Expr) : T.Expr =

    List.foldBack (fun x acc -> T.Drop(toTargetVar x, acc)) (Set.toList variables) expr


// --------------------------------------------------------
// Error messages and assumption checking
// --------------------------------------------------------
exception ElaborationError of string

let private fail message = raise (ElaborationError message)

let private unionDisjoint (left: Set<S.Var>) (right: Set<S.Var>) : Set<S.Var> =
    if not (Set.isEmpty (Set.intersect left right)) then
        fail "The sets are not disjoint!"

    Set.union left right

let private checkAssumptionsFigure8 Delta Gamma expr =
    let fv = freeVarsExpr expr


    if not (Set.isEmpty (Set.intersect Delta Gamma)) then
        fail "Figure 8 requires Delta and Gamma to be disjoint."

    if not (Set.isSubset Gamma fv) then
        fail "Figure 8 requires Gamma to be a subset of fv(e)."

    if not (Set.isSubset fv (Set.union Delta Gamma)) then
        fail "Figure 8 requires every free variable to occur in Delta or Gamma."


// --------------------------------------------------------
// Figure 8
// --------------------------------------------------------


let rec translate (Delta: Set<S.Var>) (Gamma: Set<S.Var>) (expr: S.Expr) : T.Expr =
    //checkAssumptionsFigure8 Delta Gamma expr // for debugging
    //helper for translating Rizzo operations (similar to constructor)
    let transformed values =
        let rec goThrough values =
            match values with
            | [] -> [], Set.empty
            | value :: rest ->
                let rest', laterOwned = goThrough rest

                let owned = Set.intersect (Set.difference Gamma laterOwned) (freeVarsExpr value)

                let value' = translate (unionDisjoint Delta laterOwned) owned value
                value' :: rest', (unionDisjoint owned laterOwned)

        goThrough values |> fst

    let transformInOrder rizzoOperation left right =
        match transformed [ left; right ] with
        | [ left'; right' ] -> rizzoOperation (left', right')
        | _ -> fail "Expected two operands."

    match expr with
    //Rizzo specific operations with just one argument behaving like the constructor from Perceus
    | S.Chan name -> T.Chan name
    | S.Never -> T.Never
    | S.Head t -> T.Head(translate Delta Gamma t)
    | S.Tail t -> T.Tail(translate Delta Gamma t)
    | S.Wait t -> T.Wait(translate Delta Gamma t)
    | S.Watch t -> T.Watch(translate Delta Gamma t)
    //Rizzo specific operations with two arguments also behaving like the constructor from Perceus
    | S.SignalCons(s, t) -> transformInOrder T.SignalCons s t
    | S.Sync(s, t) -> transformInOrder T.Sync s t
    | S.ApplyWhenV(s, t) -> transformInOrder T.ApplyWhenV s t
    | S.ApplyLater(s, t) -> transformInOrder T.ApplyLater s t
    // Delay copies the values that might not be there in the future
    | S.Delay body ->
        let captures = freeVarsExpr body
        let body' = translate Set.empty captures body
        let borrowed = Set.difference captures Gamma
        dupMany borrowed (T.Delay(Set.toList captures |> List.map toTargetVar, body'))
    // [SVAR] and [SVAR-DUP]
    | S.Var x ->
        if Gamma = Set.singleton x then
            T.Var(toTargetVar x)
        elif Set.contains x Delta && Set.isEmpty Gamma then
            T.Dup(toTargetVar x, T.Var(toTargetVar x))
        else
            fail "No variable rule from Figure 8 applies."

    // [SAPP]
    | S.App(e1, e2) ->
        let Gamma2 = Set.intersect Gamma (freeVarsExpr e2)

        let e1' = translate (unionDisjoint Delta Gamma2) (Set.difference Gamma Gamma2) e1

        let e2' = translate Delta Gamma2 e2

        T.App(e1', e2')

    // [SLAM] and [SLAM-D]
    | S.Lambda(x, body) ->
        let bodyFreeVars = freeVarsExpr body
        let ys = freeVarsExpr (S.Lambda(x, body))
        let captures = ys |> Set.toList |> List.map toTargetVar
        let Delta1 = Set.difference ys Gamma

        if Set.contains x bodyFreeVars then
            let e' = translate Set.empty (unionDisjoint ys (Set.singleton x)) body
            dupMany Delta1 (T.Lambda(captures, toTargetVar x, e'))
        else
            let e' = translate Set.empty ys body
            dupMany Delta1 (T.Lambda(captures, toTargetVar x, T.Drop(toTargetVar x, e')))

    // [SBIND] and [SBIND-D]
    | S.Let(x, e1, e2) ->

        if Set.contains x Delta || Set.contains x Gamma then
            fail "[SBIND] requires the binder to be fresh for Delta and Gamma."

        let e2FreeVars = freeVarsExpr e2

        if Set.contains x e2FreeVars then
            let Gamma2 = Set.intersect Gamma (Set.difference e2FreeVars (Set.singleton x))

            let e1' = translate (unionDisjoint Delta Gamma2) (Set.difference Gamma Gamma2) e1
            let e2' = translate Delta (unionDisjoint Gamma2 (Set.singleton x)) e2

            T.Let(toTargetVar x, e1', e2')
        else
            let Gamma2 = Set.intersect Gamma e2FreeVars
            let e1' = translate (unionDisjoint Delta Gamma2) (Set.difference Gamma Gamma2) e1
            let e2' = translate Delta Gamma2 e2

            T.Let(toTargetVar x, e1', T.Drop(toTargetVar x, e2'))

    //[SMATCH]
    | S.Match(x, branches) ->
        let GammaWithoutX = Set.difference Gamma (Set.singleton x) //???

        let branches' =

            branches
            |> List.map (fun branch ->
                let patternBoundVars = boundVars branch.Pattern

                let branchOwned = unionDisjoint GammaWithoutX patternBoundVars

                let GammaI = Set.intersect branchOwned (freeVarsExpr branch.Body)

                let GammaI' = Set.difference branchOwned GammaI

                let body' = dropMany GammaI' (translate Delta GammaI branch.Body)

                { T.Pattern = toTargetPattern branch.Pattern
                  T.Body = body' })

        let scrutineeOwned = Set.intersect Gamma (Set.singleton x)

        let scrutinee' = translate Delta scrutineeOwned (S.Var x)

        T.MatchExpr(scrutinee', branches')

    //[SCON]
    | S.Cons(constructor: Source.Constructor, vals) ->

        let rec translateValues values =
            match values with
            | [] -> ([], Set.empty)
            | vi :: rest ->
                let rest', laterOwned = translateValues rest

                let GammaI = Set.intersect (Set.difference Gamma laterOwned) (freeVarsExpr vi)

                let vi' = translate (unionDisjoint Delta laterOwned) GammaI vi

                let allOwned = unionDisjoint GammaI laterOwned

                vi' :: rest', allOwned

        let values', _ = translateValues vals

        T.Cons(toTargetConstructor constructor, values')

    | S.Function name -> T.Function name


let elaborate expr = translate Set.empty Set.empty expr

//for examples where all free variables start owned.
let elaborateOpen expr =
    translate Set.empty (freeVarsExpr expr) expr

let x = S.Varr "x"

let test1 = S.Var x

let result1 = elaborateOpen test1

printfn "%A" result1
