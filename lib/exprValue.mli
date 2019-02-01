open Core
open Collections

type t =
  [ `Apply of t * t list
  | `Bool of bool
  | `Closure of t * t Ctx.t
  | `Id of Expr.id
  | `Lambda of Expr.id list * t
  | `Let of Expr.id * t * t
  | `List of t list
  | `Num of int
  | `Op of Expr.Op.t * t list
  | `Tree of t Tree.t
  | `Unit ]

include Binable.S with type t := t

include Sexpable.S with type t := t

include Comparable.S with type t := t

val compare : t -> t -> int

val to_string : t -> String.t

val of_expr : Expr.t -> t

val of_value : Value.t -> t

val to_expr_exn : t -> Expr.t

val to_value_exn : t -> Value.t

val to_value : t -> Value.t Or_error.t
