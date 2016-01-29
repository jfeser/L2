open Core.Std

open Synthesis_common

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
    include Generalizer.S
              
    val generate_constants : Generalizer.t
    val generate_identifiers : Generalizer.t
    val generate_expressions : Generalizer.t
    val generate_lambdas : Generalizer.t
    val generate_combinators : Generalizer.t

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

module L2_Memoizer : Memoizer.S

module type Synthesizer_intf = sig
  val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t
end

module L2_Synthesizer : sig
  include Synthesizer_intf
  val initial_hypothesis : Example.t list -> Hypothesis.t
end
