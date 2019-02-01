open Core
open Collections
open Infer

val default_init : TypedExpr.t List.t

val extended_init : TypedExpr.t List.t

val default_operators : Expr.Op.t List.t

val timer : Timer.t

val counter : Counter.t

val solve :
     ?config:Config.t
  -> ?bk:(String.t * Expr.t) List.t
  -> ?init:TypedExpr.t List.t
  -> Example.t List.t
  -> Expr.t Ctx.t
