open Core.Std

open Hypothesis
open Infer
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
  val invariants : t -> unit

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
  val mk_any : Component.Set.t -> (Symbol.t * t)
end

module Conflict : sig
  type t = {
    automaton : Constrained.t;
    any_state : Symbol.t;
  }

  include Sexpable.S with type t := t

  val invariants : t -> unit

  val complement : t -> t
  val of_skeleton :
    Z3.context
    -> Component.Set.t
    -> Specification.t Skeleton.t
    -> Component.Specification.t
    -> t Option.t Or_error.t
end

module Synthesizer : sig
  val synthesize :
    max_cost:int
    -> Component.Set.t
    -> Component.Specification.t
    -> Type.t
    -> Hypothesis.t Option.t Or_error.t

  val synthesize_from_examples :
    max_cost:int
    -> Component.Set.t
    -> Example.t list
    -> Hypothesis.t Option.t Or_error.t
end
