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

module Make_BFS_Synthesizer : functor (G : Generalizer_intf) -> Synthesizer_intf
module L2_BFS_Synthesizer : Synthesizer_intf

module type Prune_intf = sig
  val should_prune : Hypothesis.t -> bool
end

module Memoizer : sig
  module type S = sig
    type t
    val create : unit -> t
    val get : t -> Hole.t -> Specification.t -> int -> (Hypothesis.t * Unifier.t) list
  end

  module Make : functor (G: Generalizer_intf) -> functor (P: Prune_intf) -> S
end  

module L2_Synthesizer : sig
  include Synthesizer_intf
  val initial_hypothesis : Example.t list -> Hypothesis.t
end
