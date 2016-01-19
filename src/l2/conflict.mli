open Core.Std

open Hypothesis

module KTree : sig
  type 'a t =
    | Leaf of 'a
    | Node of 'a * 'a t list
  with sexp

  val value : 'a t -> 'a
  val fold : f:('a -> 'b List.t -> 'b) -> 'a t -> 'b
  val map : f:('a -> 'b) -> 'a t -> 'b t
end

type t = {
  input_spec : Component.Predicate.t list;
  body_spec : Component.Predicate.t list KTree.t;
  sorts : Component.Sort.t Component.Variable.Map.t;
} with sexp

include Equal.S with type t := t

val of_hypothesis_unpruned : (Component.t String.Map.t) -> Hypothesis.t -> t Or_error.t

val of_hypothesis :
  ?components:(Component.t String.Map.t) -> Hypothesis.t -> [`Conflict of t | `NoConflict] Or_error.t
