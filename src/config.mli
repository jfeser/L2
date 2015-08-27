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
}

(** The default configuration. *)
val default : t

val t_of_sexp : Sexplib.Type.t -> t
val sexp_of_t : t -> Sexplib.Type.t

val of_string : bytes -> t
val to_string : t -> bytes
