open Core.Std

open Collections
open Hypothesis
open Infer

val counter : Collections.Counter.t  

module type Deduction_intf = sig
  (** Attempt to push all specifications towards the leaves of the
      skeleton. If, in the process, any specification goes to bottom,
      return None. *)
  val push_specifications : Specification.t Skeleton.t -> Specification.t Skeleton.t Option.t
  val push_specifications_unification : Specification.t Skeleton.t -> Specification.t Skeleton.t Option.t
end

module L2_Deduction : Deduction_intf

module L2_Generalizer : sig
  module type S = sig
    type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list
    val generalize : t
    val generalize_all : Hypothesis.t -> Hypothesis.t list

    val generate_constants : t
    val generate_identifiers : t
    val generate_expressions : t
    val generate_lambdas : t
    val generate_combinators : t

    val lambda : Symbol.t
    val combinator : Symbol.t
    val expression : Symbol.t
    val constant : Symbol.t
    val identifier : Symbol.t
    val base_case : Symbol.t
  end

  module Symbols : sig
    val lambda : Symbol.t
    val combinator : Symbol.t
    val expression : Symbol.t
    val constant : Symbol.t
    val identifier : Symbol.t
    val base_case : Symbol.t
  end
  
  module With_components : S
  module No_components : S
  module No_lambdas : S
end

module Memoizer : sig
  module type S = sig
    type t
    val create : unit -> t
    val get : t -> Hole.t -> Specification.t -> int -> (Hypothesis.t * Unifier.t) list
  end

  module Make : functor (G: L2_Generalizer.S) -> functor (D: Deduction_intf) -> S
end

module L2_Memoizer : Memoizer.S

module type Synthesizer_intf = sig
  val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t
end

module L2_Synthesizer : sig
  include Synthesizer_intf
  val initial_hypothesis : Example.t list -> Hypothesis.t
end
