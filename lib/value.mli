open Core

type t = Ast.ivalue

val to_string : t -> string

val of_evalue_exn : Ast.evalue -> Ast.ivalue

val to_evalue : Ast.ivalue -> Ast.evalue

include Comparable.S with type t := t

include Sexpable.S with type t := t
