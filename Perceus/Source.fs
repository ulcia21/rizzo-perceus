//Source

module Source

type Var = Varr of string

type Constructor = Constructor of string

type Binder =
    | Variable of Var
    | Wildcard

type Pattern = Pattern of Constructor * Binder list

type MatchElem = { Pattern: Pattern; Body: Expr }

// Val and expr joined together
and Expr =
    | Var of Var
    | Lambda of Var * Expr
    | Cons of Constructor * Expr list
    | App of Expr * Expr
    | Let of Var * Expr * Expr
    | Match of Var * MatchElem list
