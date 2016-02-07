open Core.Std

open Hypothesis
open Synthesis_common

module Rule : sig
  type t = Symbol.t * Component.Specification.t * Symbol.t list

  include Sexpable.S with type t := t
    
  val compare : t -> t -> int
    
  val start_state : t -> Symbol.t
  val spec : t -> Component.Specification.t
  val end_states : t -> Symbol.t list
  val arity : t -> int
  val is_terminal : t -> bool
end

module Constrained : sig
  type t = {
    states : Symbol.Set.t;
    initial_states : Symbol.Set.t;
    components : Component.Set.t;
    rules : Rule.t list;
  }

  include Sexpable.S with type t := t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string

  val create :
    String.Set.t
    -> String.Set.t
    -> Component.Set.t
    -> (string * Component.Specification.t * string list) list
    -> t

  val reduce : Z3.context -> t -> t Or_error.t
  val is_empty : Z3.context -> t -> (bool * t) Or_error.t
  val to_generalizer : Z3.context -> t -> CostModel.t -> Generalizer.t Or_error.t
  val intersect : t -> t -> t
end

module Conflict : sig
  type t = {
    automaton : Constrained.t;
    any_state : Symbol.t;
  }

  val complement : t -> t
end
