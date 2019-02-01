open Core

open Ast
open Collections
open Infer
open Structure
open Util

module TypMemoizer = Sstream.Memoizer (Type) (TypedExpr)

module SimpleMemoizer =
  Sstream.Memoizer (struct type t = TypedExpr.t list [@@deriving sexp, compare] end) (Expr)

let default_init =
  ["0"; "1"; "inf"; "[]"; "#f"]
  |> List.map ~f:(fun str -> Expr.of_string_exn str |> infer_exn (Ctx.empty ()))

let extended_init =
  default_init @
  (["sort"; "merge"; "dedup"; "take"; "drop"; "append"; "reverse";
    "intersperse"; "concat"; "zip"]
   |> List.map ~f:(fun str -> Expr.of_string_exn str |> infer_exn stdlib_tctx))

let default_operators = List.filter ~f:((<>) Cons) Expr.Op.all

(* Create an empty timing object and register some timing fields. *)
let timer = Timer.empty ()
let () =
  let n = Timer.add_zero timer in
  n "check" "Total time spent checking expressions";
  n "deduction" "Total time spent in Deduction";
  n "partial_eval" "Total time spent in partial evaluation";
  n "unify" "Total time spent in unification"
let run_with_time (name: string) (thunk: unit -> 'a) : 'a =
  Timer.run_with_time timer name thunk

(* Create a counter and register counter fields. *)
let counter = Counter.empty ()
let () =
  let n = Counter.add_zero counter in
  n "verify" "Number of expressions verified against the specification";
  n "num_checks" "Number of times the expression checker was called";
  n "num_checks_run" "Number of times the expression checker actually ran"

let matrix_of_texpr_list ~size (texprs: TypedExpr.t list) : TypedExpr.t Sstream.matrix =
  let init_sizes = List.map texprs ~f:(fun e -> e, size e) in
  let max_size =
    List.fold_left init_sizes ~init:0 ~f:(fun x (_, y) -> if x > y then x else y)
  in
  List.range ~stop:`inclusive 1 max_size
  |> List.map ~f:(fun s ->
      List.filter_map init_sizes ~f:(fun (e, s') ->
          if s = s' then Some e else None))
  |> Sstream.of_list

let arrow_error () = failwith "Operator is not of type Arrow_t."

let rec simple_enumerate ?(memo=SimpleMemoizer.empty ()) init : expr Sstream.matrix =
  let open Sstream in
  let init_matrix =
    matrix_of_texpr_list ~size:(fun e -> Expr.cost (TypedExpr.to_expr e)) init
    |> map_matrix ~f:(TypedExpr.to_expr)
  in

  let args_matrix num_args =
    let choose prev_args =
      slazy (fun () ->
          map_matrix (SimpleMemoizer.get memo init (fun () -> simple_enumerate ~memo:memo init))
            ~f:(fun arg -> prev_args @ [arg]))
    in
    match List.range 0 num_args with
    | _::xs -> (List.fold_left xs ~init:choose ~f:(fun acc _ -> compose acc choose)) []
    | [] -> failwith "Cannot generate args matrix with no arguments."
  in

  let callable_matrix cost apply_callable callable_typ = match callable_typ with
    | Arrow_t (arg_typs, _) ->
      let num_args = List.length arg_typs in
      let prefix = repeat_n (num_args + cost - 1) [] in
      let matrix = slazy (fun () -> map_matrix (args_matrix num_args) ~f:apply_callable) in
      concat prefix matrix
    | _ -> arrow_error ()
  in
  let op_matrix op op_typ =
    callable_matrix (Expr.Op.cost op) (fun args -> `Op (op, args)) op_typ
  in
  let apply_matrix func func_typ =
    callable_matrix 1 (fun args -> `Apply (func, args)) func_typ
  in

  let (op_matrices : expr matrix list) =
    List.map Expr.Op.all ~f:(fun op ->
        let meta = Expr.Op.meta op in
        op_matrix op meta.Expr.Op.typ)
  in

  let (apply_matrices : expr matrix list) =
    List.filter init ~f:(fun texpr ->
        match TypedExpr.to_type texpr with
        | Arrow_t _ -> true
        | _ -> false)
    |> List.map ~f:(fun func -> apply_matrix (TypedExpr.to_expr func) (TypedExpr.to_type func))
  in
  merge (init_matrix::(op_matrices @ apply_matrices))

let rec enumerate
    ?(ops=default_operators)
    ?(memo=TypMemoizer.empty ())
    config
    init
    typ
    (check: TypedExpr.t -> bool)
  : TypedExpr.t Sstream.matrix =
  let open Sstream in

  (* Init is finite, so we can construct an init stream by breaking
     init into a list of size classes and returning that list as a
     stream. *)
  let init_matrix =
    List.filter init ~f:(fun e -> is_unifiable typ (TypedExpr.to_type e))
    |> matrix_of_texpr_list ~size:(fun e -> Expr.cost (TypedExpr.to_expr e))
  in

  (* Generate an argument list matrix that conforms to the provided list of types. *)
  let args_matrix (check: TypedExpr.t list -> bool) (arg_typs: typ list) =
    let dummy_args = List.map ~f:(fun t ->
        TypedExpr.Id (Fresh.name "d", (generalize 0 t))) arg_typs
    in
    let choose (prev_args: TypedExpr.t list) : (TypedExpr.t list) matrix =
      let prev_args_len = List.length prev_args in

      (* Instantiate the argument types in the same context. Free
         type variables should be shared across arguments. For example,
         when instantiating the argument types for equals: (a, a) ->
         bool, both a's should map to the same free type. *)
      let arg_typs' =
        let ctx = Ctx.empty () in
        List.map arg_typs ~f:(instantiate ~ctx:ctx 0)
      in
      
      (* Split the argument type list into the types of the
         arguments that have already been selected and the head of
         the list of remaining types (which will be the type of the
         current argument). *)
      let prev_arg_typs, current_typ =
        match List.split_n arg_typs' (List.length prev_args) with
        | pt, (ct::_) -> pt, ct
        | _ -> failwith "BUG: Should never happen."
      in

      (* Unify the types of the previous arguments with the actual
         selected types. By the size effects of unify, this should fill
         in any type variables in the current type that have already been
         bound. *)
      let prev_selected_typs =
        let ctx = Ctx.empty () in
        List.map prev_args ~f:(fun arg -> instantiate ~ctx:ctx 0 (TypedExpr.to_type arg))
      in
      List.iter2_exn prev_arg_typs prev_selected_typs ~f:unify_exn;

      let current_typ' = normalize (generalize (-1) current_typ) in

      let check' e =
        check (prev_args @ [e] @ (List.drop dummy_args (prev_args_len + 1)))
      in

      (* Generate the argument matrix lazily so that it will not be
         created until the prefix classes are exhausted. *)
      slazy (fun () ->
          let should_prune_branch =
            if config.Config.use_solver then
              let dummy_arg_list =
                prev_args @ (List.drop dummy_args prev_args_len)
              in
              not (run_with_time "check" (fun () -> check dummy_arg_list))
            else false
          in

          if should_prune_branch then Sstream.repeat [] else
            map_matrix
              (enumerate config ~memo:memo init current_typ' check')
              ~f:(fun arg -> prev_args @ [arg]))
    in
    match arg_typs with
    | _::xs -> (List.fold_left xs ~init:choose ~f:(fun acc _ -> compose acc choose)) []
    | [] -> failwith "Cannot generate args matrix with no arguments."
  in

  let callable_matrix check cost apply_callable callable_typ =
    match callable_typ with
    | Arrow_t (arg_typs, ret_typ) ->
      let num_args = List.length arg_typs in
      let prefix = repeat_n (cost + num_args - 1) [] in
      let matrix = slazy (fun () -> map_matrix (args_matrix check arg_typs) ~f:(apply_callable ret_typ)) in
      concat prefix matrix
    | _ -> arrow_error ()
  in
  let op_matrix op op_typ =
    callable_matrix
      (fun args ->
         match op_typ with
         | Arrow_t (_, ret_t) -> check (TypedExpr.Op ((op, args), ret_t))
         | _ -> failwiths "Operator type is not an arrow." op_typ [%sexp_of:Type.t])
      (Expr.Op.cost op)
      (fun ret_typ args -> TypedExpr.Op ((op, args), ret_typ))
      op_typ
  in
  let apply_matrix func func_typ =
    callable_matrix
      (fun args ->
         match func_typ with
         | Arrow_t (_, ret_t) -> check (TypedExpr.Apply ((func, args), ret_t))
         | _ -> failwiths "Function type is not an arrow." func_typ [%sexp_of:Type.t])
      1
      (fun ret_typ args -> TypedExpr.Apply ((func, args), ret_typ))
      func_typ
  in

  (* The op stream is infinite, so it needs more careful handling. *)
  let op_matrices =
    List.map ops ~f:(fun op -> op, Expr.Op.meta op)
    (* Filter all non operators that would not be redundant in the
       current hypothesis. *)
    (* |> List.filter ~f:(fun (op, meta) -> *)
    (*   let h = *)
    (*     let dummy_args = *)
    (*       match meta.Expr.Op.typ with *)
    (*       | Arrow_t (arg_typs, _) -> *)
    (*         Fresh.names "d" (List.length arg_typs) |> List.map ~f:(fun n -> `Id n) *)
    (*       | _ -> arrow_error () *)
    (*     in hypo (`Op (op, dummy_args)) *)
    (*   in not (Rewrite.is_redundant base_terms h)) *)

    (* Filter all operators that can return the correct type. *)
    |> List.filter ~f:(fun (_, meta) ->
        match meta.Expr.Op.typ with
        | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
        | _ -> arrow_error ())

    (* Unify the return type of the operator with the input type. By
       the side effects of unify, all the other free type variables in
       the operator type will reflect the substitution. Now we have
       correct types for the arguments. *)
    |> List.map ~f:(fun (op, meta) ->
        match instantiate 0 typ, instantiate 0 meta.Expr.Op.typ with
        | typ', (Arrow_t (_, ret_typ) as op_typ) ->
          unify_exn typ' ret_typ;
          op, normalize (generalize (-1) op_typ)
        | _ -> arrow_error ())

    (* Generate a matrix for each operator. *)
    |> List.map ~f:(fun (op, op_typ) -> op_matrix op op_typ)
  in

  let apply_matrices =
    init
    |> List.filter ~f:(fun texpr ->
        match TypedExpr.to_type texpr with
        | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
        | _ -> false)
    |> List.map ~f:(fun texpr ->
        match instantiate 0 typ, instantiate 0 (TypedExpr.to_type texpr) with
        | typ', (Arrow_t (_, ret_typ) as func_typ) ->
          unify_exn typ' ret_typ;
          texpr, normalize (generalize (-1) func_typ)
        | _ -> arrow_error ())
    |> List.map ~f:(fun (func, func_typ) -> apply_matrix func func_typ)
  in

  merge (init_matrix::(op_matrices @ apply_matrices))
  (* |> map ~f:(fun row -> List.iter ~f:(fun x -> printf "Examined: %s\n" (Expr.to_string (TypedExpr.to_expr x))) row; row) *)
  |> map ~f:(List.filter ~f:(fun x ->
      let e = TypedExpr.to_expr x in
      if config.Config.deduction then
        match Rewrite.simplify (List.map init ~f:TypedExpr.to_expr) e with
        | Some e' -> Expr.cost e' >= Expr.cost e
        | None -> false
      else true))

type hypothesis = {
  skel : Spec.t;
  max_exh_cost : int;
  generalized : bool;
}

(** TODO: Remove me! Needed so that the check method can run randomly,
    with a probability that depends on the current search depth. *)
let current_cost = ref 0

let () = Random.self_init ()

(** Run a thunk with a probability p. If the thunk is not run, return
    the default value. *)
let run_with_probability ~default ~f p =
  if (Random.float 1.0) <= p then f () else default

let solve_single
    ?(init=[])
    ?(verify=Verify.verify_examples ~ctx:(Ctx.empty ()))
    ~config
    (examples: example list) =
  let initial_spec =
    let target_name = Example.name examples in
    let target ctx expr =
      let body = Ctx.lookup_exn ctx target_name in
      `Let (target_name, body, expr)
    in
    { Spec.target;
      Spec.holes =
        Ctx.of_alist_exn [
          target_name,
          { examples = List.map examples ~f:(fun ex -> ex, Ctx.empty ());
            signature = Example.signature examples;
            tctx = Ctx.empty ();
          };
        ];
      Spec.cost = 0;
    }
  in

  (* let zctx = Z3.mk_context [] in *)
  (* let z3_memoizer = ref Expr.Map.empty in *)
  (* let lemmas = Deduction.infer_length_constraint zctx examples in *)

  let result_sterms = List.map examples ~f:(fun (_, r) -> Unify.sterm_of_expr r) in

  let generate_specs (specs: Spec.t list) : Spec.t list =
    List.concat_map specs ~f:(fun parent ->
        (Spec.map_bodies ~deduce_examples:config.Config.deduction parent)
        @ (Spec.filter_bodies ~deduce_examples:config.Config.deduction parent)
        @ (Spec.fold_bodies ~deduce_examples:config.Config.deduction ~infer_base:config.Config.infer_base parent)
        @ (Spec.foldt_bodies ~deduce_examples:config.Config.deduction ~infer_base:config.Config.infer_base parent)
        @ (Spec.recurs_bodies ~deduce_examples:config.Config.deduction parent)
      )
  in

  (** Given a hole, create a matrix of expressions that can fill the hole. *)
  let matrix_of_hole (check: TypedExpr.t -> bool) (hole: hole) : expr Sstream.matrix =
    let init' =
      (Ctx.to_alist hole.tctx
       |> List.map ~f:(fun (name, typ) -> TypedExpr.Id (name, typ)))
      @ init
    in
    match hole.signature with
    | Arrow_t (arg_typs, ret_typ) ->
      let args = List.map arg_typs ~f:(fun typ -> Fresh.name "x", typ) in
      let arg_names, _ = List.unzip args in
      let init'' = init' @ (List.map args ~f:(fun (name, typ) ->
          TypedExpr.Id (name, typ)))
      in

      if config.Config.untyped then
        simple_enumerate init''
        |> Sstream.map_matrix ~f:(fun expr -> `Lambda (arg_names, expr))
      else
        enumerate config init'' ret_typ
          (fun e -> check (TypedExpr.Lambda ((arg_names, e), hole.signature)))
        |> Sstream.map_matrix ~f:(fun e -> `Lambda (arg_names, TypedExpr.to_expr e))
    | typ ->
      if config.Config.untyped then
        simple_enumerate init'
      else
        enumerate config init' typ check
        |> Sstream.map_matrix ~f:TypedExpr.to_expr
  in

  let total_cost (hypo_cost: int) (enum_cost: int) : int =
    hypo_cost + (Int.of_float (1.5 ** (Float.of_int enum_cost)))
  in

  (** Given a specification, create a stream of options. Any
      expression that verifies correctly will be a Some variant. *)
  let solver_of_spec (spec: Spec.t) : (expr -> expr) option Sstream.matrix =
    let choose
        (check: TypedExpr.t -> bool)
        (name: string)
        (hole: hole)
        (ctx: expr Ctx.t) : (expr Ctx.t) Sstream.matrix =
      Sstream.map_matrix (matrix_of_hole check hole) ~f:(Ctx.bind ctx name)
    in

    let matrix =
      let named_holes = Ctx.to_alist spec.Spec.holes in
      (* The initial context binds each hole to an identifier. This
         allows the context to be used to generate a target function even
         when some of the holes are not filled by an expression. *)
      let init_ctx =
        Ctx.mapi ~f:(fun ~key ~data:_ -> `Id key) spec.Spec.holes
      in
          
      let check' (name: string) (e: TypedExpr.t) : bool =
        (* let nesting_depth_cap = 2 in *)
        (* let tctx = Ctx.merge_right init_tctx (free e |> Ctx.of_alist_exn) in *)
        (* let max_depth = max (Ctx.data tctx |> List.map ~f:type_nesting_depth) in *)
        (* if max_depth > nesting_depth_cap then false else *)

        let ctx = Ctx.bind init_ctx name (TypedExpr.to_expr e) in
        let target = (spec.Spec.target ctx) (`Id "_") in

        match target with
        | `Let _ ->
          (* if Expr.all_abstract body then true else *)
          (* If the example output does not pass the
             postcondition of the outermost function, discard this
             candidate. *)
          (* if not (check_outermost_application body examples) then false else *)
          (* Attempt partial evaluation and unification. *)
          List.for_all (List.zip_exn examples result_sterms)
            ~f:(fun ((input, _), result_sterm) ->
                let expr =
                  ExprValue.of_expr ((spec.Spec.target ctx) input)
                in
                try
                  let lhs : ExprValue.t =
                    run_with_time "partial_eval" (fun () ->
                        Eval.partial_eval
                          ~recursion_limit:100
                          ~ctx:(failwith "TODO: Replace with library.")
                          expr)
                  in
                  match Unify.sterm_of_expr_value lhs, result_sterm with
                  | (Some lhs_term, Some result_term) ->
                    let r =
                      (try
                         let _ =
                           run_with_time "unify" (fun () ->
                               Unify.unify_one
                                 (Unify.translate lhs_term)
                                 (Unify.translate result_term))
                         in true
                       with Unify.Non_unifiable -> false)
                    in
                    r
                  | _ -> true
                with
                | Eval.HitRecursionLimit -> true
                | Eval.RuntimeError _ -> false)
        | _ -> failwith "Bad result from solve_single."
      in

      let check (name: string) (e: TypedExpr.t) : bool =
        let open Float in
        Counter.incr counter "num_checks";
        run_with_probability ~default:true ~f:(fun () ->
            Counter.incr counter "num_checks_run"; check' name e)
          (1.0 / (config.Config.check_prob ** (of_int !current_cost)))
      in

      match named_holes with
      | [] -> failwith "Specification has no holes."
      | (name, hole)::hs ->
        (List.fold_left hs
           ~init:(choose (check name) name hole)
           ~f:(fun matrix (name', hole') ->
               Sstream.compose matrix (choose (check name') name' hole')))
          (Ctx.empty ())
    in

    Sstream.map_matrix matrix ~f:(fun ctx ->
        let target = spec.Spec.target ctx in
        if verify target examples then Some target else None)
  in

  (* Search a spec up to a specified maximum cost. The amount of
     exhaustive search that this involves depends on the cost of the
     hypothesis. *)
  let search max_cost spec : (expr -> expr) option =
    let solver = solver_of_spec spec in
    let rec search' (exh_cost: int) : (expr -> expr) option =
      let cost = total_cost spec.Spec.cost exh_cost in
      (* If the cost of searching this level exceeds the max cost, end the search. *)
      if cost >= max_cost then None

      (* Otherwise, examine the next row in the search tree. *)
      else begin
        current_cost := cost;
        let row = Sstream.next solver in
        match List.find_map row ~f:ident with
        | Some result -> Some result
        | None -> search' (exh_cost + 1)
      end
    in search' 0
  in

  let rec search_unbounded (cost: int) (hypos: hypothesis list) =    
    let can_search hypo =
      total_cost hypo.skel.Spec.cost (hypo.max_exh_cost + 1) <= cost
    in
    let m_result = List.find_map hypos ~f:(fun hypo ->
        (* Check whether it is possible to search more than has been
           searched with the current cost. Since the total cost can be
           non-linear, this must be explicitly checked. *)
        if can_search hypo then search cost hypo.skel else None)
    in
    match m_result with
    | Some result -> result
    | None ->
      let hypos = List.map hypos ~f:(fun h ->
          if can_search h
          then {h with max_exh_cost = h.max_exh_cost + 1}
          else h)
      in
      let generalizable, rest = List.partition_tf hypos ~f:(fun h ->
          (not h.generalized) && (total_cost h.skel.Spec.cost 0 < cost))
      in
      let new_hypos =
        List.map generalizable ~f:(fun h -> h.skel)
        |> generate_specs
        |> List.map ~f:(fun s -> { skel = s; max_exh_cost = 0; generalized = false; })
      in
      search_unbounded (cost + 1)
        (new_hypos @ rest
         @ List.map generalizable ~f:(fun h -> { h with generalized = true; }))
  in
  search_unbounded 1 [{ skel = initial_spec; max_exh_cost = 0; generalized = false; }]

let solve ?(config=Config.default) ?(bk=[]) ?(init=default_init) examples =
  (* Check examples. *)
  (if not (List.map examples ~f:(fun ex -> ex, Ctx.empty ()) |> Example.check)
   then failwith "Examples do not represent a function.");

  let tctx =
    List.fold_left bk ~init:(Ctx.empty ()) ~f:(fun ctx (name, impl) ->
        Ctx.bind ctx name (TypedExpr.to_type (infer_exn ctx impl)))
  in
  let vctx =
    List.fold_left bk ~init:(failwith "TODO: Replace with library.")
      ~f:(fun ctx (name, impl) ->
          Ctx.bind ctx name (`Closure (impl, ctx)))
  in

  let init =
    init @ (Ctx.to_alist tctx
            |> List.map ~f:(fun (name, typ) -> TypedExpr.Id (name, typ)))
  in

  let verify ?(limit=100) target examples =
    Counter.incr counter "verify";
    try
      match target (`Id "_") with
      | `Let (name, body, _) ->
        let _ = infer_exn (Ctx.bind tctx name (fresh_free 0)) body in
        Verify.verify_examples ~limit ~ctx:vctx target examples
      | _ -> failwith "Bad result from solve_single."
    with
    | TypeError _ -> false
    | Ctx.UnboundError _ -> false
  in

  Ctx.bind (Ctx.empty ()) (Example.name examples)
      ((solve_single ~init ~verify ~config examples) (`Id "_"))
