open! Core

exception RuntimeError of Error.t

exception HitRecursionLimit

type closure [@@deriving sexp]

type ctx = closure Ast.evalue Ctx.t

val eval : ?recursion_limit:int -> ctx -> Expr.t -> closure Ast.evalue

val ctx_of_alist : (Name.t * Expr.t) list -> ctx

val partial_eval :
  ?recursion_limit:int -> ?ctx:ExprValue.t Mutctx.t -> ExprValue.t -> ExprValue.t
