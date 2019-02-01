open Core
open Collections

exception RuntimeError of Error.t

exception HitRecursionLimit

val eval : ?recursion_limit:int -> Value.t Ctx.t -> Expr.t -> Value.t

val partial_eval :
  ?recursion_limit:int -> ?ctx:ExprValue.t Ctx.t -> ExprValue.t -> ExprValue.t
