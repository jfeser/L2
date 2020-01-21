open! Core
open Ast

type t = {
  exprs : (id * Expr.t) list;
  expr_ctx : Expr.t Map.M(Name).t;
  value_ctx : Eval.closure Ast.evalue Map.M(Name).t;
  exprvalue_ctx : ExprValue.t Map.M(Name).t;
  type_ctx : Infer.Type.t Map.M(Name).t;
  builtins : Expr.Op.t list;
}

val empty : t

val from_channel_exn : file:string -> In_channel.t -> t

val from_channel : file:string -> In_channel.t -> t Or_error.t

val from_file_exn : string -> t

val from_file : string -> t Or_error.t

val filter_keys : t -> f:(id -> bool) -> t
