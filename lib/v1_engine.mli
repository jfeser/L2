open Core
open Collections
open Infer

type config =
  { verbosity: int
  ; untyped: bool
  ; deduction: bool
  ; infer_base: bool
  ; max_exhaustive_depth: int
  ; flat_cost: bool }

val default_init : TypedExpr.t List.t

(* val extended_init : TypedExpr.t List.t *)
(* val default_operators : Expr.Op.t List.t *)

(* val timer : Timer.t *)
(* val counter : Counter.t *)

val solve :
     ?config:config
  -> ?bk:(String.t * Expr.t) List.t
  -> ?init:TypedExpr.t List.t
  -> Example.t List.t
  -> Expr.t Ctx.t
