(** Write the performance counters to the log at level INFO. *)
val log_summary : unit -> unit

val assert_of_expr : Z3.context -> Infer.TypedExpr.t -> Z3.Expr.expr

val z3_to_string : Z3.Expr.expr -> string
                                                          
val infer_length_constraint : Z3.context -> Ast.example list -> Z3.Expr.expr

val memoized_check_constraints :
  bool Expr.Map.t ref ->
  Z3.context ->
  Ast.example list ->
  Infer.TypedExpr.t -> bool
