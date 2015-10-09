open Core.Std

open Hypothesis
open Infer

module type Generalizer_intf = sig
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list
  val generalize : t
  val generalize_all : generalize:t -> Hypothesis.t -> Hypothesis.t list
end

module Generalizer_impl : sig
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list
  val generalize_all : generalize:t -> Hypothesis.t -> Hypothesis.t list  
end
  
module type Synthesizer_intf = sig
  val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t
end

module type Deduction_intf = sig
  (** Attempt to push all specifications towards the leaves of the
      skeleton. If, in the process, any specification goes to bottom,
      return None. *)
  val push_specifications : Specification.t Skeleton.t -> Specification.t Skeleton.t Option.t
  val push_specifications_unification : Specification.t Skeleton.t -> Specification.t Skeleton.t Option.t
end

module Memoizer : sig
  module type S = sig
    type t
    val create : unit -> t
    val get : t -> Hole.t -> Specification.t -> int -> (Hypothesis.t * Unifier.t) list
  end

  module Make : functor (G: Generalizer_intf) -> functor (D: Deduction_intf) -> S
end  

module L2_Synthesizer : sig
  include Synthesizer_intf
  val initial_hypothesis : Example.t list -> Hypothesis.t
end
