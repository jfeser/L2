open Core.Std
       
open Hypothesis

module Generalizer : sig
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Infer.Unifier.t) list
      
  module type S = sig
    val generalize : t
    val generalize_all : Hypothesis.t -> Hypothesis.t list
  end
  
  module Make : functor (G : sig val generalize : t end) -> S
end

module Memoizer : sig
  module type S = sig
    type t
    val create : unit -> t
    val get : t -> Hole.t -> Specification.t -> cost:int -> (Hypothesis.t * Infer.Unifier.t) list
  end
  
  module Make : functor (G : Generalizer.S) -> S
end
