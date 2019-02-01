open Core

(** Contains runtime configuration for L2. *)
type t = {
  (** The logging verbosity. (deprecated) *)
  verbosity : int;

  (** Whether to use type-based expression pruning. *)
  untyped : bool;

  (** Whether to prune expressions using deduction rules. *)
  deduction : bool;

  (** Whether to infer the base cases of folds. *)
  infer_base : bool;

  (** Whether to use Z3 to prune expressions. *)
  use_solver : bool;

  (** The largest expression that can be used to fill a hole in a hypothesis. *)
  max_exhaustive_depth : int;

  check_prob : float;

  flat_cost : bool;
}

(** The default configuration. *)
val default : t

include Sexpable.S with type t := t
include Stringable.S with type t := t

(** The current configuration. *)
val config : t ref
