open Core

type t =
  { exprs: (string * Expr.t) list
  ; expr_ctx: Expr.t String.Map.t
  ; value_ctx: Value.t String.Map.t
  ; exprvalue_ctx: ExprValue.t String.Map.t
  ; type_ctx: Infer.Type.t String.Map.t
  ; builtins: Expr.Op.t list }

val empty : t

val from_channel_exn : file:string -> In_channel.t -> t

val from_channel : file:string -> In_channel.t -> t Or_error.t

val from_file_exn : string -> t

val from_file : string -> t Or_error.t

val filter_keys : t -> f:(string -> bool) -> t
