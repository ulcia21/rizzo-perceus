module Target

type Var = Varr of string

type Constructor = Constructor of string

type Binder =
    | Variable of Var
    | Wildcard

type Pattern = Pattern of Constructor * Binder list

type MatchElem = { Pattern: Pattern; Body: Expr }

and Expr =
    | App of Expr * Expr
    | Let of Var * Expr * Expr
    | MatchVar of Var * MatchElem list
    | Dup of Var * Expr
    | Drop of Var * Expr
    | MatchExpr of Expr * MatchElem list
    | Var of Var
    | Lambda of captures: Var list * Var * Expr // captures are the references captioned by a function (ys)
    | Cons of Constructor * Expr list
