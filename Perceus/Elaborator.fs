module Elaborator

module S = Source
module T = Target

open MultiSet
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

let dupMany (variables: MultiSet<S.Var>) (expr: T.Expr) : T.Expr =

    List.foldBack (fun x acc -> T.Dup(toTargetVar x, acc)) (toList variables) expr

let dropMany (variables: MultiSet<S.Var>) (expr: T.Expr) : T.Expr =

    List.foldBack (fun x acc -> T.Drop(toTargetVar x, acc)) (toList variables) expr


// --------------------------------------------------------
// Error messages and assumption checking
// --------------------------------------------------------
exception ElaborationError of string

let private fail message = raise (ElaborationError message)

let private checkAssumptionsFigure8 delta gamma expr =
    let fv = freeVarsExpr expr
    let deltaVars = MultiSet.toSet delta
    let gammaVars = MultiSet.toSet gamma

    if not (MultiSet.allMultiplicityOne delta && MultiSet.allMultiplicityOne gamma) then
        fail "Figure 8 requires multiplicity 1 in Delta and Gamma."

    if not (MultiSet.isEmpty (MultiSet.intersection delta gamma)) then
        fail "Figure 8 requires Delta and Gamma to be disjoint."

    if not (Set.isSubset gammaVars fv) then
        fail "Figure 8 requires Gamma to be a subset of fv(e)."

    if not (Set.isSubset fv (Set.union deltaVars gammaVars)) then
        fail "Figure 8 requires every free variable to occur in Delta or Gamma."


// --------------------------------------------------------
// Figure 8
// --------------------------------------------------------


let rec translate (Delta: MultiSet<S.Var>) (Gamma: MultiSet<S.Var>) (expr: S.Expr) : T.Expr =
    //checkAssumptionsFigure8 delta gamma expr // for debugging
    //helper for translating Rizzo operations (similar to constructor)
    let transformed values =
        let rec goThrough values =
            match values with
            | [] -> [], empty
            | value :: rest ->
                let rest', laterOwned = goThrough rest

                let owned =
                    intersection (difference Gamma laterOwned) (setToMultiSet (freeVarsExpr value))

                let value' = translate (sum Delta laterOwned) owned value
                value' :: rest', (sum owned laterOwned)

        goThrough values |> fst

    let transformInOrder rizzoOperation left right =
        match transformed [ left; right ] with
        | [ left'; right' ] -> rizzoOperation (left', right')
        | _ -> fail "Expected two operands."

    match expr with
    //Rizzo specific operations with just one argument behaving like the constructor from Perceus
    | S.Chan name -> T.Chan name
    | S.Never -> T.Never
    | S.Head t -> T.Head(translate Gamma Delta t)
    | S.Tail t -> T.Tail(translate Delta Gamma t)
    | S.Wait t -> T.Wait(translate Delta Gamma t)
    | S.Watch t -> T.Watch(translate Delta Gamma t)
    //Rizzo specific operations with two argument behaving like the constructor from Perceus
    | S.SignalCons(s, t) -> transformInOrder T.SignalCons s t
    | S.Sync(s, t) -> transformInOrder T.Sync s t
    | S.ApplyWhenV(s, t) -> transformInOrder T.ApplyWhenV s t
    | S.ApplyLater(s, t) -> transformInOrder T.ApplyLater s t
    | S.Delay body ->
        let captures = setToMultiSet (freeVarsExpr body)
        let body' = translate empty captures body
        let borrowed = difference captures Gamma
        dupMany borrowed (T.Delay(toList captures |> List.map toTargetVar, body'))
    // [SVAR] and [SVAR-DUP]
    | S.Var x ->
        if Gamma = MultiSet.singleton x then
            T.Var(toTargetVar x)
        elif MultiSet.contains x Delta && MultiSet.isEmpty Gamma then
            T.Dup(toTargetVar x, T.Var(toTargetVar x))
        else
            fail "No variable rule from Figure 8 applies."

    // [SAPP]
    | S.App(e1, e2) ->
        let Gamma2 = MultiSet.intersection Gamma (setToMultiSet (freeVarsExpr e2))

        let e1' =
            translate (MultiSet.sum Delta Gamma2) (MultiSet.difference Gamma Gamma2) e1

        let e2' = translate Delta Gamma2 e2

        T.App(e1', e2')

    // [SLAM] and [SLAM-D]
    | S.Lambda(x, body) ->
        let bodyFreeVars = freeVarsExpr body
        let ys = freeVarsExpr (S.Lambda(x, body))
        let captures = ys |> Set.toList |> List.map toTargetVar
        let Delta1 = MultiSet.difference (MultiSet.setToMultiSet ys) Gamma

        if Set.contains x bodyFreeVars then
            let e' = translate empty (sum (setToMultiSet ys) (singleton x)) body
            dupMany Delta1 (T.Lambda(captures, toTargetVar x, e'))
        else
            let e' = translate empty (setToMultiSet ys) body
            dupMany Delta1 (T.Lambda(captures, toTargetVar x, T.Drop(toTargetVar x, e')))

    // [SBIND] and [SBIND-D]
    | S.Let(x, e1, e2) ->

        if contains x Delta || contains x Gamma then
            fail "[SBIND] requires the binder to be fresh for Delta and Gamma."

        let e2FreeVars = freeVarsExpr e2

        if Set.contains x e2FreeVars then
            let Gamma2 =
                intersection Gamma (setToMultiSet (Set.difference e2FreeVars (Set.singleton x)))

            let e1' = translate (sum Delta Gamma2) (difference Gamma Gamma2) e1
            let e2' = translate Delta (sum Gamma2 (singleton x)) e2

            T.Let(toTargetVar x, e1', e2')
        else
            let Gamma2 = intersection Gamma (setToMultiSet e2FreeVars)
            let e1' = translate (sum Delta Gamma2) (difference Gamma Gamma2) e1
            let e2' = translate Delta Gamma2 e2

            T.Let(toTargetVar x, e1', T.Drop(toTargetVar x, e2'))

    //[SMATCH]
    | S.Match(x, branches) ->
        let GammaWithoutX = difference Gamma (singleton x) //???

        let branches' =

            branches
            |> List.map (fun branch ->
                let patternBoundVars = setToMultiSet (boundVars branch.Pattern)

                let branchOwned = sum GammaWithoutX patternBoundVars

                let GammaI = intersection branchOwned (setToMultiSet (freeVarsExpr branch.Body))

                let GammaI' = difference branchOwned GammaI

                let body' = dropMany GammaI' (translate Delta GammaI branch.Body)

                { T.Pattern = toTargetPattern branch.Pattern
                  T.Body = body' })

        T.MatchVar(toTargetVar x, branches')

    //[SCON]
    | S.Cons(constructor, vals) ->

        let rec translateValues values =
            match values with
            | [] -> ([], empty)
            | vi :: rest ->
                let rest', laterOwned = translateValues rest

                let GammaI =
                    intersection (difference Gamma laterOwned) (setToMultiSet (freeVarsExpr vi))

                let vi' = translate (sum Delta laterOwned) GammaI vi

                let allOwned = sum GammaI laterOwned

                vi' :: rest', allOwned

        let values', _ = translateValues vals

        T.Cons(toTargetConstructor constructor, values')

    | S.Function name -> T.Function name


let elaborate expr = translate empty empty expr

//for examples where all free variables start owned.
let elaborateOpen expr =
    translate empty (setToMultiSet (freeVarsExpr expr)) expr

let x = S.Varr "x"

let test1 = S.Var x

let result1 = elaborateOpen test1

printfn "%A" result1
