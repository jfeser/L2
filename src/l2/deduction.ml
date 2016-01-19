open Core.Std

open Ast
open Collections
open Infer
open Util

module FormulaII =
  Collections.InvertedIndex (Int) (struct type t = Z3.Solver.status end)

let counter = Counter.empty ()
let () =
  let n = Counter.add_zero counter in
  n "expr_memoizer" "Number of expressions caught by memoizer";
  n "formula_memoizer" "Number of formulas caught by memoizer";
  n "solver_call" "Number of solver calls";
  n "solver_unsat" "Number of times solver returned UNSAT";
  n "solver_sat" "Number of times solver returned SAT";
  n "solver_unknown" "Number of times solver returned UNKNOWN";
  n "check_true" "Number of times abstract hypothesis checker returned true";
  n "check_false" "Number of times abstract hypothesis checker returned false";
  n "fuzzy_match" "Number of formulas caught by fuzzy matching"
let counter_incr = Counter.incr counter

let timer = Timer.empty ()
let () =
  let n = Timer.add_zero timer in
  n "z3_string" "Time spent converting Z3 exprs to strings";
  n "memoizer" "Time spent in memoizer lookups";
  n "lemma_gen" "Time spent generating lemmas";
  n "solve" "Time spent in solver"
let run_with_time (name: string) (thunk: unit -> 'a) : 'a =
  Timer.run_with_time timer name thunk

let max_solve_time = ref Time.Span.zero

let (formula_memoizer: FormulaII.t) = FormulaII.create ()

(* let (formula_memoizer: (String.Set.t * Z3.Solver.status) list ref) = ref [] *)

let int_sort ctx = Z3.Arithmetic.Integer.mk_sort ctx
let list_sort ctx = Z3.Sort.mk_uninterpreted_s ctx "Lst"
let tree_sort ctx = Z3.Sort.mk_uninterpreted_s ctx "Tree"
    
let len_fun ctx =
  Z3.FuncDecl.mk_func_decl_s ctx "len" [list_sort ctx] (int_sort ctx)
let height_fun ctx =
  Z3.FuncDecl.mk_func_decl_s ctx "height" [tree_sort ctx] (int_sort ctx)

let z3_int = Z3.Arithmetic.Integer.mk_numeral_i
let z3_app = Z3.FuncDecl.apply
let z3_eq = Z3.Boolean.mk_eq
let z3_and = Z3.Boolean.mk_and
let z3_ge = Z3.Arithmetic.mk_ge
let z3_le = Z3.Arithmetic.mk_le
let z3_sub = Z3.Arithmetic.mk_sub
let z3_add = Z3.Arithmetic.mk_add

let z3_to_string e = run_with_time "z3_string" (fun () -> Z3.Expr.to_string e)

(** Convert a type into a Z3 sort. For integers and booleans, this
    uses Z3's built in sorts. For lists, it returns Lst, which is an
    uninterpreted sort that does not depend on the type parameter. For
    all other types, it returns an uninterpreted sort created from the
    string representation of the type. *)
let sort_of_type (ctx: Z3.context) (typ: typ) : Z3.Sort.sort =
  match typ with
  | Const_t Num_t -> Z3.Arithmetic.Integer.mk_sort ctx
  | Const_t Bool_t -> Z3.Boolean.mk_sort ctx
  | App_t ("list", _) -> list_sort ctx
  | App_t ("tree", _) -> tree_sort ctx
  | _ -> Z3.Sort.mk_uninterpreted_s ctx (Type.to_string typ)

(** Same as sort_of_type, but uses the built in Z3 list type. *)
let rec sort_of_type' (ctx: Z3.context) (typ: typ) : Z3.Sort.sort =
  match typ with
  | Const_t Num_t -> Z3.Arithmetic.Integer.mk_sort ctx
  | Const_t Bool_t -> Z3.Boolean.mk_sort ctx
  | App_t ("list", [t]) ->
    Z3.Z3List.mk_list_s ctx (Type.to_string typ) (sort_of_type' ctx t)
  | App_t ("tree", _) -> tree_sort ctx
  | Var_t ({contents = Free _}) -> failwith "Cannot convert free type variable to Z3 sort."
  | _ -> Z3.Sort.mk_uninterpreted_s ctx (Type.to_string typ)

(** Generate a Z3 assertion from a boolean expression. *)
let rec assert_of_expr (zctx: Z3.context) (expr: TypedExpr.t) : Z3.Expr.expr =
  let open TypedExpr in
  let aoe = assert_of_expr zctx in
  match expr with
  | Id (name, t) -> Z3.Expr.mk_const_s zctx name (sort_of_type' zctx t)
  | Num (x, _) -> z3_int zctx x
  | List ([], t) -> Z3.Z3List.nil (sort_of_type' zctx t)
  | List (xs, t) ->
    (* Convert to cons expression, instead of duplicating logic. *)
    let cons_expr = List.fold_right xs ~init:(List ([], t)) ~f:(fun elem rest ->
        Op ((Cons, [elem; rest]), t))
    in
    aoe cons_expr
  | Apply ((Id (name, Arrow_t (args_t, _)), args), ret_t) ->
    let args_z3 = List.map ~f:aoe args in
    let args_sorts = List.map ~f:(Z3.Expr.get_sort) args_z3 in
    let func_decl =
      Z3.FuncDecl.mk_func_decl_s zctx name args_sorts (sort_of_type' zctx ret_t)
    in
    z3_app func_decl (List.map ~f:aoe args)
  | Op ((Eq, [a1; a2]), _) -> z3_eq zctx (aoe a1) (aoe a2)
  | Op ((Neq, [a1; a2]), _) ->
    Z3.Boolean.mk_not zctx (z3_eq zctx (aoe a1) (aoe a2))
  | Op ((Lt, [a1; a2]), _) -> Z3.Arithmetic.mk_lt zctx (aoe a1) (aoe a2)
  | Op ((Gt, [a1; a2]), _) -> Z3.Arithmetic.mk_gt zctx (aoe a1) (aoe a2)
  | Op ((Leq, [a1; a2]), _) -> Z3.Arithmetic.mk_le zctx (aoe a1) (aoe a2)
  | Op ((Geq, [a1; a2]), _) -> Z3.Arithmetic.mk_ge zctx (aoe a1) (aoe a2)
  | Op ((And, [a1; a2]), _) -> Z3.Boolean.mk_and zctx [aoe a1; aoe a2]
  | Op ((Or, [a1; a2]), _) -> Z3.Boolean.mk_or zctx [aoe a1; aoe a2]
  | Op ((Not, [a]), _) -> Z3.Boolean.mk_not zctx (aoe a)
  | Op ((If, [a1; a2; a3]), _) ->
    Z3.Boolean.mk_ite zctx (aoe a1) (aoe a2) (aoe a3)
  | Op ((Car, [a]), t) ->
    let z3_a = aoe a in
    let sort = Z3.Expr.get_sort z3_a in
    z3_app (Z3.Z3List.get_head_decl sort) [z3_a]
  | Op ((Cdr, [a]), t) ->
    let z3_a = aoe a in
    let sort = Z3.Expr.get_sort z3_a in
    z3_app (Z3.Z3List.get_tail_decl sort) [z3_a]
  | Op ((Cons, [a1; a2]), t) ->
    let a1_z3 = aoe a1 in
    let sort =
      let a1_sort = Z3.Expr.get_sort a1_z3 in
      let name = Z3.Symbol.get_string (Z3.Sort.get_name a1_sort) in
      Z3.Z3List.mk_list_s zctx name a1_sort
    in
    (* Make sure that nil gets assigned a concrete sort if possible. *)
    let a2_z3 = (match a2 with
        | List ([], _) -> Z3.Z3List.nil sort
        | _ -> aoe a2)
    in
    z3_app (Z3.Z3List.get_cons_decl sort) [a1_z3; a2_z3]
  | _ -> failwith (sprintf "Unsupported expression: %s" (to_string expr))

let assert_of_string (zctx: Z3.context) (s: string) : Z3.Expr.expr =
  typed_expr_of_string s |> assert_of_expr zctx

(** Infer a constraint about the length of the list returned by the
    target function in terms of the length of the input list(s). *)
let infer_length_constraint
    (zctx: Z3.context)
    (examples: example list) : Z3.Expr.expr =
  let check_predicate (p: int -> int -> bool) =
    List.for_all ~f:(fun e -> match e with
        | (`Apply (_, [`List i]), `List o) -> p (List.length i) (List.length o)
        | _ -> failwith (sprintf "Unsupported example: %s" (Example.to_string e)))
      examples
  in
  let i_len = z3_app (len_fun zctx)
      [Z3.Expr.mk_const_s zctx "i0" (list_sort zctx)] in
  let o_len = z3_app (len_fun zctx)
      [Z3.Expr.mk_const_s zctx "o" (list_sort zctx)] in
  let lemmas = [
    (>), Z3.Arithmetic.mk_gt zctx i_len o_len;
    (<), Z3.Arithmetic.mk_lt zctx i_len o_len;
    (=), z3_eq zctx i_len o_len;
    (>=), Z3.Arithmetic.mk_ge zctx i_len o_len;
    (<=), Z3.Arithmetic.mk_le zctx i_len o_len;
  ] in
  let matching_lemma =
    List.find_map
      ~f:(fun (p, l) -> if check_predicate p then Some l else None) lemmas
  in
  match matching_lemma with
  | Some l -> l
  | None -> failwith "Failed to find valid length constraint."

(** Generate lemmas about the candidate program. We are using the
    theory of uninterpreted functions, so we assign the expression a name
    to use in its lemmas. Return a tuple, (name, lemmas). *)
let generate_lemmas
    (fresh_name: unit -> string)
    (ctx: Z3.Expr.expr TypedExprMap.t ref)
    (zctx: Z3.context)
    (expr: TypedExpr.t) : Z3.Expr.expr * (Z3.Expr.expr list) =
  let name_of_expr e =
    let name = fresh_name () in
    let msg = sprintf "Mapped %s to %s." (TypedExpr.to_string e) name in
    LOG msg NAME "l2.solver" LEVEL DEBUG;
    Z3.Expr.mk_const_s
      zctx
      name
      (* (TypedExpr.to_string e) *)
      (sort_of_type zctx (TypedExpr.to_type e))
  in

  let rec g ctx zctx expr =
    let name =
      match TypedExprMap.find !ctx expr with
      | Some n -> n
      | None ->
        let z3_name = name_of_expr expr in
        ctx := TypedExprMap.add !ctx ~key:expr ~data:z3_name; z3_name
    in

    let open TypedExpr in
    let lemmas =
      match expr with
      | Num (x, _) -> [
          z3_eq zctx (z3_int zctx x) name;
        ]

      | List (l, _) -> [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (z3_int zctx (List.length l))
        ]

      (* len(map f x) = len(x) *)
      (* len(reverse x) = len(x) *)
      (* len(sort x) = len(x) *)
      | Apply ((Id ("reverse", _), [l]), _)
      | Apply ((Id ("sort", _), [l]), _)
      | Apply ((Id ("map", _), [l; _]), _) ->
        let l_name, l_lemmas = g ctx zctx l in
        [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (z3_app (len_fun zctx) [l_name]);
        ] @ l_lemmas

      (* len(dedup x) <= len(x) *)
      | Apply ((Id ("dedup", _), [l; _]), _) ->
        let l_name, l_lemmas = g ctx zctx l in
        [
          z3_le zctx
            (z3_app (len_fun zctx) [name])
            (z3_app (len_fun zctx) [l_name]);
        ] @ l_lemmas

      (* len(take l x) = x & len(l) >= x *)
      | Apply ((Id ("take", _), [l; x]), _) ->
        let l_name, l_lemmas = g ctx zctx l in
        let x_name, x_lemmas = g ctx zctx x in
        [
          z3_and zctx [
            z3_eq zctx
              (z3_app (len_fun zctx) [name])
              x_name;

            z3_ge zctx
              (z3_app (len_fun zctx) [l_name])
              x_name;
          ];
        ] @ l_lemmas @ x_lemmas

      (* len(drop l x) = len(l) - x & len(l) >= x *)
      | Apply ((Id ("drop", _), [l; x]), _) ->
        let l_name, l_lemmas = g ctx zctx l in
        let x_name, x_lemmas = g ctx zctx x in
        [
          z3_and zctx [
            z3_eq zctx
              (z3_app (len_fun zctx) [name])
              (z3_sub zctx [
                  (z3_app (len_fun zctx) [l_name]);
                  x_name
                ]);

            z3_ge zctx
              (z3_app (len_fun zctx) [l_name])
              x_name;
          ];
        ] @ l_lemmas @ x_lemmas

      (* len(merge l1 l2) = len(l1) + len(l2) *)
      | Apply ((Id ("merge", _), [l1; l2]), _) ->
        let l1_name, l1_lemmas = g ctx zctx l1 in
        let l2_name, l2_lemmas = g ctx zctx l2 in
        [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (z3_add zctx [
                z3_app (len_fun zctx) [l1_name];
                z3_app (len_fun zctx) [l2_name];
              ]);
        ] @ l1_lemmas @ l2_lemmas

      (* len(intersperse(x, y)) = if len(y) = 0 then 0 else 2 * len(y) - 1 *)
      | Apply ((Id ("intersperse", _), [_; l]), _) ->
        let l_name, l_lemmas = g ctx zctx l in
        [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (Z3.Boolean.mk_ite zctx
               (z3_eq zctx
                  (z3_app (len_fun zctx) [l_name])
                  (z3_int zctx 0))
               (z3_int zctx 0)
               (z3_sub zctx [
                   Z3.Arithmetic.mk_mul zctx [
                     z3_int zctx 2;
                     z3_app (len_fun zctx) [l_name];
                   ];
                   z3_int zctx 1;
                 ]))
        ] @ l_lemmas

      (* len(zip(l1, l2)) = len(l1) && len(zip(l1, l2)) = len(l2) *)
      | Apply ((Id ("zip", _), [l1; l2]), _) ->
        let l1_name, l1_lemmas = g ctx zctx l1 in
        let l2_name, l2_lemmas = g ctx zctx l2 in
        [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (z3_app (len_fun zctx) [l1_name]);
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (z3_app (len_fun zctx) [l2_name]);
        ] @ l1_lemmas @ l2_lemmas

      | Op ((Cons, [_; x]), _)
      | Op ((RCons, [x; _]), _) ->
        (* Generate any lemmas about the child expressions. *)
        let x_name, x_lemmas = g ctx zctx x in

        (* Generate any lemmas for this expression. In this case, len(cons
           x y) = len(y) + 1 *)
        [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (Z3.Arithmetic.mk_add zctx [
                z3_app (len_fun zctx) [x_name];
                z3_int zctx 1;
              ]);
        ] @ x_lemmas

      | Op ((Cdr, [x]), _) ->
        let x_name, x_lemmas = g ctx zctx x in
        [
          Z3.Arithmetic.mk_gt zctx
            (z3_app (len_fun zctx) [x_name])
            (z3_int zctx 0);

          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (z3_sub zctx [
                z3_app (len_fun zctx) [x_name];
                z3_int zctx 1;
              ]);
        ] @ x_lemmas

      (* len(x) > 0 *)
      | Apply ((Id ("last", _), [x]), _)
      | Op ((Car, [x]), _) ->
        let x_name, x_lemmas = g ctx zctx x in
        [
          Z3.Arithmetic.mk_gt zctx
            (z3_app (len_fun zctx) [x_name])
            (z3_int zctx 0);
        ] @ x_lemmas

      | Op ((Value, [x]), _) ->
        let x_name, x_lemmas = g ctx zctx x in
        [
          Z3.Arithmetic.mk_gt zctx
            (z3_app (height_fun zctx) [x_name])
            (z3_int zctx 0);
        ] @ x_lemmas

      (* | Op ((If, [test; case1; case2]), _) -> *)
      (*   let name = name_of_expr expr in *)
      (*   let case1_name, case1_lemmas = g ctx zctx case1 in *)
      (*   let case2_name, case2_lemmas = g ctx zctx case2 in *)
      (*   List.map ~f:(fun l -> Z3.Boolean.mk_ite ) *)
      (*     case1_lemmas *)
      (*   let lemmas = [ *)
      (*     Z3.Boolean.mk_ite zctx *)

      (*     Z3.Arithmetic.mk_gt zctx *)
      (*       (z3_app (len_fun zctx) [x_name]) *)
      (*       (z3_int zctx 0); *)
      (*   ] in name, (lemmas @ x_lemmas) *)

      | Apply ((Id ("filter", _), [l; _]), _) ->
        let l_name, l_lemmas = g ctx zctx l in
        [
          Z3.Arithmetic.mk_le zctx
            (z3_app (len_fun zctx) [name])
            (z3_app (len_fun zctx) [l_name]);
        ] @ l_lemmas

      | Apply ((Id ("foldl", _),
                [l; Lambda (([a1; _], Op ((Cons, [_; Id (a2, _)]), _)), _); i]), _)
      | Apply ((Id ("foldr", _),
                [l; Lambda (([a1; _], Op ((Cons, [_; Id (a2, _)]), _)), _); i]), _)
      | Apply ((Id ("foldl", _),
                [l; Lambda (([a1; _], Op ((RCons, [Id (a2, _); _]), _)), _); i]), _)
      | Apply ((Id ("foldr", _),
                [l; Lambda (([a1; _], Op ((RCons, [Id (a2, _); _]), _)), _); i]), _)
        when a1 = a2 ->
        let i_name, i_lemmas = g ctx zctx i in
        let l_name, l_lemmas = g ctx zctx l in
        [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (Z3.Arithmetic.mk_add zctx [
                z3_app (len_fun zctx) [l_name];
                z3_app (len_fun zctx) [i_name];
              ]);
        ] @ l_lemmas @ i_lemmas

      | Apply ((Id ("foldl", _),
                [_; Lambda (([a1; _], ((Op ((Cons, [_; Id (a2, _)]), _)) as f)), _); _]), _)
      | Apply ((Id ("foldr", _),
                [_; Lambda (([a1; _], ((Op ((Cons, [_; Id (a2, _)]), _)) as f)), _); _]), _)
      | Apply ((Id ("foldl", _),
                [_; Lambda (([a1; _], ((Op ((RCons, [Id (a2, _); _]), _)) as f)), _); _]), _)
      | Apply ((Id ("foldr", _),
                [_; Lambda (([a1; _], ((Op ((RCons, [Id (a2, _); _]), _)) as f)), _); _]), _)
        when a1 <> a2 ->
        let f_name, f_lemmas = g ctx zctx f in
        [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (z3_app (len_fun zctx) [f_name]);
        ] @ f_lemmas

      | Apply ((Id ("foldl", _), [_; Lambda ((_, Op ((Cons, [_; List ([], _)]), _)), _); _]), _)
      | Apply ((Id ("foldr", _), [_; Lambda ((_, Op ((Cons, [_; List ([], _)]), _)), _); _]), _)
      | Apply ((Id ("foldl", _), [_; Lambda ((_, Op ((RCons, [List ([], _); _]), _)), _); _]), _)
      | Apply ((Id ("foldr", _), [_; Lambda ((_, Op ((RCons, [List ([], _); _]), _)), _); _]), _) ->
        [
          z3_eq zctx
            (z3_app (len_fun zctx) [name])
            (z3_int zctx 0);
        ]

      | _ -> []
    in
    name, lemmas
  in
  run_with_time "lemma_gen" (fun () -> g ctx zctx expr)

let memoized_check
    (solver: Z3.Solver.solver)
    (asserts: Z3.Expr.expr list) : Z3.Solver.status =
  let memoizer = formula_memoizer in
  let asserts' =
    List.map ~f:(fun (Z3.Expr.Expr e) -> Z3.AST.hash e) asserts
    |> FormulaII.KSet.of_list
  in

  let m_result = run_with_time "memoizer_time" (fun () ->
      FormulaII.exists_subset_or_superset
        memoizer asserts' Z3.Solver.UNSATISFIABLE Z3.Solver.SATISFIABLE)
  in

  match m_result with
  | Some x -> counter_incr "formula_memoizer"; x
  | None ->
    counter_incr "solver_call";
    let (x, run_time) =
      Util.with_runtime
        (fun () ->
           Z3.Solver.add solver asserts;
           Z3.Solver.check solver [])
    in
    (* let () = *)
    (*   let msg = *)
    (*     Z3.Solver.get_statistics solver |> Z3.Solver.Statistics.to_string *)
    (*   in LOG msg NAME "l2.solver.stats" LEVEL INFO *)
    (* in *)
    (match x with
     | Z3.Solver.UNSATISFIABLE -> counter_incr "solver_unsat"
     | Z3.Solver.SATISFIABLE -> counter_incr "solver_sat"
     | Z3.Solver.UNKNOWN -> counter_incr "solver_unknown");
    Timer.add timer "solve" run_time;
    max_solve_time := Time.Span.max !max_solve_time run_time;
    FormulaII.add memoizer asserts' x;
    x

(** Given a candidate expression and some constraints on the
    expression's input and output, check those constraints using an
    SMT solver. The constraints should refer to the inputs to the
    target function using 'i1' ... 'in' and to the output using
    'o'. *)
let check_constraints
    (zctx: Z3.context)
    (examples: example list)
    (expr: TypedExpr.t) : bool =
  let solver = Z3.Solver.mk_solver zctx None in

  let open TypedExpr in
  match expr with
  | Lambda ((args, body), Arrow_t (args_t, _)) ->
    (try
       let fresh_name = Fresh.mk_fresh_name_fun () in

       (* Store mappings between the constants used in the examples and
          Z3 names in a shared table. *)
       let example_expr_to_z3 = ref TypedExprMap.empty in

       let assertions = List.concat_map examples ~f:(fun (ex: example) ->
           let _, input_args, output = Example.to_triple ex in

           (* Collect any relevant assertions about the inputs in this
              example. *)
           let named_input_asserts =
             List.map input_args ~f:(fun e ->
                 let te = infer (Ctx.empty ()) e in
                 generate_lemmas fresh_name example_expr_to_z3 zctx te
               )
           in

           (* Collect any relevant assertions about the example output. *)
           let output_name, output_asserts =
             generate_lemmas fresh_name example_expr_to_z3 zctx
               (infer (Ctx.empty ()) output)
           in

           (* Generate a context that binds the lambda argument names to
              the Z3 names that we generated when getting constraints for
              the inputs. *)
           let ctx =
             ref (List.fold_left
                    ~f:(fun ctx (arg, t, (z3arg, _)) ->
                        TypedExprMap.add ctx ~key:(Id (arg, t)) ~data:z3arg)
                    ~init:!example_expr_to_z3
                    (zip3_exn args args_t named_input_asserts))
           in

           let body_name, body_asserts =
             generate_lemmas fresh_name ctx zctx body
           in

           (z3_eq zctx output_name body_name)
           :: output_asserts
           @ body_asserts
           @ (List.concat_map named_input_asserts ~f:(Tuple.T2.get2))
         )
       in

       if List.length assertions = 0 then true else
         (* let () = *)
         (*   let msg = *)
         (*     ((sprintf "SMT generated from %s:\n" (TypedExpr.to_string expr)) ^ *)
         (*      (List.map ~f:z3_to_string assertions *)
         (*       |> String.concat ~sep:"\n")) *)
         (*   in LOG msg NAME "l2.solver" LEVEL INFO *)
         (* in *)

         (match memoized_check solver assertions with
          | Z3.Solver.UNSATISFIABLE -> counter_incr "check_false"; false
          | Z3.Solver.SATISFIABLE -> counter_incr "check_true"; true
          | Z3.Solver.UNKNOWN ->
            let msg =
              sprintf "Solver returned UNKNOWN on %s." (TypedExpr.to_string expr)
            in
            counter_incr "check_true";
            LOG msg NAME "l2.solver" LEVEL WARN;
            true)
     with Z3native.Exception _ -> false)
  | _ -> failwith (sprintf "Unsupported expression: %s" (to_string expr))

let memoized_check_constraints
    (memoizer: bool Expr.Map.t ref)
    (zctx: Z3.context)
    (examples: example list)
    (expr: TypedExpr.t) : bool =
  let normal_expr =
    Expr.normalize ~bound:stdlib_names (TypedExpr.to_expr expr)
  in

  LOG "Looking up %s in memoizer." (Expr.to_string normal_expr)
    NAME "l2.solver.memo" LEVEL INFO;

  match Expr.Map.find !memoizer normal_expr with
  | Some ret -> counter_incr "expr_memoizer"; ret
  | None ->
    let ret = check_constraints zctx examples expr in
    memoizer := Expr.Map.add !memoizer ~key:normal_expr ~data:ret; ret

let log_summary () =
  let open Time.Span in
  let log_strs = List.iter ~f:(fun s -> LOG s LEVEL INFO) in

  log_strs (Timer.to_strings timer);
  log_strs (Counter.to_strings counter);

  LOG "Maximum time in solver: %s" (to_short_string !max_solve_time)
    LEVEL INFO;

  (try
     LOG "Average time in solver: %s"
       (to_short_string
          ((Timer.find_exn timer "solve") /
           (float (Counter.find_exn counter "solver_call"))))
       LEVEL INFO
   with Invalid_argument _ -> ());

  (let msg = FormulaII.log_summary formula_memoizer in
   LOG msg LEVEL INFO);


