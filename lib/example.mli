open Core
open Collections

type t = Expr.t * Expr.t

include Sexpable.S with type t := t

val compare : t -> t -> int

val of_string_exn : string -> t

val of_string : string -> t Or_error.t

val to_string : t -> string

val to_triple : t -> Ast.id * Ast.expr list * Expr.t

val name : t list -> Ast.id

val split : t list -> (string * t list) list

val signature : ?ctx:Infer.Type.t Ctx.t -> t list -> Infer.Type.t

val to_vctx : t -> string list -> Expr.t Ctx.t

val check : (t * Expr.t Ctx.t) list -> bool
