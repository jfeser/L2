open Core

type t = {
  verbosity : int;  (** The logging verbosity. (deprecated) *)
  untyped : bool;  (** Whether to use type-based expression pruning. *)
  deduction : bool;  (** Whether to prune expressions using deduction rules. *)
  infer_base : bool;  (** Whether to infer the base cases of folds. *)
  use_solver : bool;  (** Whether to use Z3 to prune expressions. *)
  max_exhaustive_depth : int;
      (** The largest expression that can be used to fill a hole in a hypothesis. *)
  check_prob : float;
  flat_cost : bool;
}
(** Contains runtime configuration for L2. *)

val default : t
(** The default configuration. *)

include Sexpable.S with type t := t

include Stringable.S with type t := t

val config : t ref
(** The current configuration. *)
