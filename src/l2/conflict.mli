open Core.Std

open Hypothesis

(* type t = { *)
(*   input_spec : Component.Predicate.t list; *)
(*   body_spec : Component.Predicate.t list KTree.t; *)
(*   sorts : Component.Sort.t Component.Variable.Map.t; *)
(* } with sexp *)

(* include Equal.S with type t := t *)

(* val of_hypothesis_unpruned : (Component.t String.Map.t) -> Hypothesis.t -> t Or_error.t *)

(* val of_hypothesis : *)
(*   ?components:(Component.t String.Map.t) -> Hypothesis.t -> [`Conflict of t | `NoConflict] Or_error.t *)
