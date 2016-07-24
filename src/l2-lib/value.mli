open Core.Std

type t = Ast.value

val sexp_of_t : t -> Sexp.t
val compare : t -> t -> int

val to_string : t -> string
