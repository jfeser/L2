open Core

type t = Ast.value

val compare : t -> t -> int
val to_string : t -> string

include Comparable.S with type t := t
include Sexpable.S with type t := t
