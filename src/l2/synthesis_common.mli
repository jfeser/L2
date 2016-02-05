open Core.Std
       
open Hypothesis

module Generalizer : sig
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Infer.Unifier.t) list
  val generalize_all : t -> Hypothesis.t -> Hypothesis.t list
end

module Memoizer : sig
  type t
  val create : Generalizer.t -> t
  val fill_holes_in_hypothesis : t -> Hypothesis.t -> int -> (Hypothesis.t * Infer.Unifier.t) list
  val get : t -> Hole.t -> Specification.t -> cost:int -> (Hypothesis.t * Infer.Unifier.t) list
end
