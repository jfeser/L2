open Core
open Collections
open Hypothesis
open Infer

module Generalizer : sig
  type t =
       Type.t StaticDistance.Map.t
    -> Type.t
    -> Symbol.t
    -> Specification.t
    -> (Hypothesis.t * Unifier.t) list

  type params = {cost_model: CostModel.t; library: Library.t}

  val generalize_single : params -> t -> Hypothesis.t -> Hypothesis.t list

  val generalize_all : params -> t -> Hypothesis.t -> Hypothesis.t list

  val compose : t -> t -> t

  val compose_all_exn : t list -> t
end

module Deduction : sig
  type t = Skeleton.t -> Skeleton.t Option.t

  val no_op : t

  val bottom : t

  val compose : t -> t -> t
end

val counter : Counter.t

val timer : Timer.t

val sexp_log : SexpLog.t

module Memoizer : sig
  type t

  module Config : sig
    type t =
      { generalize: Generalizer.t
      ; cost_model: CostModel.t
      ; deduction: Deduction.t
      ; library: Library.t
      ; search_space_out: Out_channel.t Option.t }
  end

  val create : Config.t -> t

  val to_string : t -> string

  val fill_holes_in_hypothesis :
    t -> Hypothesis.t -> int -> (Hypothesis.t * Unifier.t) Sequence.t

  val get :
    t -> Hole.t -> Specification.t -> cost:int -> (Hypothesis.t * Unifier.t) list

  val to_sequence :
       t
    -> ?min_cost:int
    -> ?max_cost:int
    -> Hypothesis.t
    -> (Hypothesis.t * Unifier.t) Sequence.t Sequence.t

  val to_flat_sequence :
       t
    -> ?min_cost:int
    -> ?max_cost:int
    -> Hypothesis.t
    -> (Hypothesis.t * Unifier.t) Sequence.t
end

module Synthesizer : sig
  module type S = sig
    val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t Or_error.t
  end
end
