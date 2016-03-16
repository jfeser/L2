open Core.Std

type t = Ast.value

include Sexpable.S with type t := t

val compare : t -> t -> int
