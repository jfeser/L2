open Core.Std

open Synthesis_common

open Hypothesis
open Infer

val cost_model : CostModel.t

module L2_Generalizer : sig
  module type S = sig
    val generalize : Generalizer.t
              
    val generate_constants : Generalizer.t
    val generate_identifiers : Generalizer.t
    val generate_expressions : Generalizer.t
    val generate_lambdas : Generalizer.t
    val generate_combinators : Generalizer.t
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

module L2_Synthesizer : sig
  val synthesize : cost:int -> Deduction.t -> Hypothesis.t -> Hypothesis.t Option.t Or_error.t
  val initial_hypothesis : Example.t list -> Hypothesis.t
end
