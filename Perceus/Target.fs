module Target

type Var = Varr of string

type Constructor = Constructor of string

type Binder =
    | Variable of Var
    | Wildcard

type Pattern = Pattern of Constructor * Binder list

type MatchElem = { Pattern: Pattern; Body: Expr }

and Expr =
    | Chan of string
    | Never
    | Head of Expr
    | Tail of Expr
    | Wait of Expr
    | Watch of Expr
    | SignalCons of Expr * Expr
    | Sync of Expr * Expr
    | ApplyWhenV of Expr * Expr
    | ApplyLater of Expr * Expr
    | Delay of captures: Var list * body: Expr
    | App of Expr * Expr
    | Let of Var * Expr * Expr
    | Dup of Var * Expr
    | Drop of Var * Expr
    | MatchExpr of Expr * MatchElem list
    | Var of Var
    | Lambda of captures: Var list * Var * Expr // captures are the references captioned by a function (ys)
    | Cons of Constructor * Expr list
    | Function of string // for map context

type FunctionContext = Map<string, Expr>
