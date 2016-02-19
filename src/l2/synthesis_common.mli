open Core.Std
       
open Hypothesis

module Generalizer : sig
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Infer.Unifier.t) list
  val generalize_all : t -> CostModel.t -> Hypothesis.t -> Hypothesis.t list
  val compose : t -> t -> t
  val compose_all_exn : t list -> t
end

module Memoizer : sig
  type t
  val create : Generalizer.t -> CostModel.t -> t
  val to_string : t -> string
  val fill_holes_in_hypothesis : t -> Hypothesis.t -> int -> (Hypothesis.t * Infer.Unifier.t) list
  val get : t -> Hole.t -> Specification.t -> cost:int -> (Hypothesis.t * Infer.Unifier.t) list

  val to_sequence : t -> Hypothesis.t -> int -> (Hypothesis.t * Infer.Unifier.t) list Sequence.t
  val to_flat_sequence : t -> Hypothesis.t -> int -> (Hypothesis.t * Infer.Unifier.t) Sequence.t
end

module Synthesizer : sig
  module type S = sig
    val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t Or_error.t
  end
end
