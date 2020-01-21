open! Core

exception RuntimeError of Error.t

exception HitRecursionLimit

val eval : ?recursion_limit:int -> Ast.evalue Ctx.t -> Expr.t -> Ast.evalue

val partial_eval :
  ?recursion_limit:int -> ?ctx:ExprValue.t Mutctx.t -> ExprValue.t -> ExprValue.t
