open Core
open Synthesis_common
open Collections

type example = ExprValue.t list * ExprValue.t [@@deriving sexp]

val examples_of_file : string -> example list

val examples_of_channel : In_channel.t -> example list

val timer : Timer.t

val push_specs : Deduction.t
