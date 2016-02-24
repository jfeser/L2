open Core.Std
       
open Hypothesis
open Infer

module Generalizer : sig
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list
  val generalize_all : t -> CostModel.t -> Hypothesis.t -> Hypothesis.t list
  val compose : t -> t -> t
  val compose_all_exn : t list -> t
end

module Memoizer : sig
  type t
  val create : Generalizer.t -> CostModel.t -> t
  val to_string : t -> string
  val fill_holes_in_hypothesis : t -> Hypothesis.t -> int -> (Hypothesis.t * Unifier.t) list
  val get : t -> Hole.t -> Specification.t -> cost:int -> (Hypothesis.t * Unifier.t) list

  val to_sequence : t -> ?min_cost:int -> ?max_cost:int -> Hypothesis.t -> (Hypothesis.t * Unifier.t) list Sequence.t
  val to_flat_sequence : t -> ?min_cost:int -> ?max_cost:int -> Hypothesis.t -> (Hypothesis.t * Unifier.t) Sequence.t
end

module Synthesizer : sig
  module type S = sig
    val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t Or_error.t
  end
end

module Deduction : sig
  module type S = sig
    val push_specs : Specification.t Skeleton.t -> Specification.t Skeleton.t Option.t
  end

  module Compose : functor (D1: S) -> functor (D2: S) -> S
end
