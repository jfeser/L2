open Core.Std

open Ast
open Infer
open Util

let (memoizer: bool TypedExprMap.t ref) = ref TypedExprMap.empty
let default_timeout = 1000

let int_sort ctx = Z3.Arithmetic.Integer.mk_sort ctx
let list_sort ctx = Z3.Sort.mk_uninterpreted_s ctx "Lst"
let tree_sort ctx = Z3.Sort.mk_uninterpreted_s ctx "Tree"
let len_fun ctx =
  Z3.FuncDecl.mk_func_decl_s ctx "len" [list_sort ctx] (int_sort ctx)
let height_fun ctx =
  Z3.FuncDecl.mk_func_decl_s ctx "height" [tree_sort ctx] (int_sort ctx)

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
  | _ -> Z3.Sort.mk_uninterpreted_s ctx (Expr.typ_to_string typ)

(** Generate a Z3 assertion from a boolean expression. *)
let rec assert_of_expr (zctx: Z3.context) (expr: TypedExpr.t) : Z3.Expr.expr =
  let open TypedExpr in
  let aoe = assert_of_expr zctx in
  match expr with
  | Id (name, t) -> Z3.Expr.mk_const_s zctx name (sort_of_type zctx t)
  | Num (x, _) -> Z3.Arithmetic.Integer.mk_numeral_i zctx x
  | Apply ((Id (name, _), args), ret_t) ->
    let args_t = List.map ~f:to_type args in
    let func_decl =
      Z3.FuncDecl.mk_func_decl_s zctx name
        (List.map ~f:(sort_of_type zctx) args_t) (sort_of_type zctx ret_t)
    in Z3.FuncDecl.apply func_decl (List.map ~f:aoe args)
  | Op ((Eq, [a1; a2]), _) -> Z3.Boolean.mk_eq zctx (aoe a1) (aoe a2)
  | Op ((Neq, [a1; a2]), _) ->
    Z3.Boolean.mk_not zctx (Z3.Boolean.mk_eq zctx (aoe a1) (aoe a2))
  | Op ((Lt, [a1; a2]), _) -> Z3.Arithmetic.mk_lt zctx (aoe a1) (aoe a2)
  | Op ((Gt, [a1; a2]), _) -> Z3.Arithmetic.mk_gt zctx (aoe a1) (aoe a2)
  | Op ((Leq, [a1; a2]), _) -> Z3.Arithmetic.mk_le zctx (aoe a1) (aoe a2)
  | Op ((Geq, [a1; a2]), _) -> Z3.Arithmetic.mk_ge zctx (aoe a1) (aoe a2)
  | Op ((And, [a1; a2]), _) -> Z3.Boolean.mk_and zctx [aoe a1; aoe a2]
  | Op ((Or, [a1; a2]), _) -> Z3.Boolean.mk_or zctx [aoe a1; aoe a2]
  | Op ((Not, [a]), _) -> Z3.Boolean.mk_not zctx (aoe a)
  | Op ((If, [a1; a2; a3]), _) -> Z3.Boolean.mk_ite zctx (aoe a1) (aoe a2) (aoe a3)
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
  let i_len = Z3.FuncDecl.apply (len_fun zctx)
      [Z3.Expr.mk_const_s zctx "i0" (list_sort zctx)] in
  let o_len = Z3.FuncDecl.apply (len_fun zctx)
      [Z3.Expr.mk_const_s zctx "o" (list_sort zctx)] in
  let lemmas = [
    (>), Z3.Arithmetic.mk_gt zctx i_len o_len;
    (<), Z3.Arithmetic.mk_lt zctx i_len o_len;
    (=), Z3.Boolean.mk_eq zctx i_len o_len;
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
let rec generate_lemmas
    (ctx: Z3.Expr.expr TypedExprMap.t ref)
    (zctx: Z3.context)
    (expr: TypedExpr.t) : Z3.Expr.expr * (Z3.Expr.expr list) =
  let name_of_expr e =
    Z3.Expr.mk_fresh_const
      zctx
      (TypedExpr.to_string e)
      (sort_of_type zctx (TypedExpr.to_type e))
  in

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
    | List (l, _) -> [
        Z3.Boolean.mk_eq zctx
          (Z3.FuncDecl.apply (len_fun zctx) [name])
          (Z3.Arithmetic.Integer.mk_numeral_i zctx (List.length l))
      ]

    | Op ((Cons, [_; x]), _)
    | Op ((RCons, [x; _]), _) ->
      (* Generate any lemmas about the child expressions. *)
      let x_name, x_lemmas = generate_lemmas ctx zctx x in

      (* Generate any lemmas for this expression. In this case, len(cons
         x y) = len(y) + 1 *)
      [
        Z3.Boolean.mk_eq zctx
          (Z3.FuncDecl.apply (len_fun zctx) [name])
          (Z3.Arithmetic.mk_add zctx [
              Z3.FuncDecl.apply (len_fun zctx) [x_name];
              Z3.Arithmetic.Integer.mk_numeral_i zctx 1;
            ]);
      ] @ x_lemmas

    | Op ((Cdr, [x]), _) ->
      let x_name, x_lemmas = generate_lemmas ctx zctx x in
      [
        Z3.Arithmetic.mk_gt zctx
          (Z3.FuncDecl.apply (len_fun zctx) [x_name])
          (Z3.Arithmetic.Integer.mk_numeral_i zctx 0);

        Z3.Boolean.mk_eq zctx
          (Z3.FuncDecl.apply (len_fun zctx) [name])
          (Z3.Arithmetic.mk_sub zctx [
              Z3.FuncDecl.apply (len_fun zctx) [x_name];
              Z3.Arithmetic.Integer.mk_numeral_i zctx 1;
            ]);
      ] @ x_lemmas

    | Op ((Car, [x]), _) ->
      let x_name, x_lemmas = generate_lemmas ctx zctx x in
      [
        Z3.Arithmetic.mk_gt zctx
          (Z3.FuncDecl.apply (len_fun zctx) [x_name])
          (Z3.Arithmetic.Integer.mk_numeral_i zctx 0);
      ] @ x_lemmas

    | Op ((Value, [x]), _) ->
      let x_name, x_lemmas = generate_lemmas ctx zctx x in
      [
        Z3.Arithmetic.mk_gt zctx
          (Z3.FuncDecl.apply (height_fun zctx) [x_name])
          (Z3.Arithmetic.Integer.mk_numeral_i zctx 0);
      ] @ x_lemmas

    (* | Op ((If, [test; case1; case2]), _) -> *)
    (*   let name = name_of_expr expr in *)
    (*   let case1_name, case1_lemmas = generate_lemmas ctx zctx case1 in *)
    (*   let case2_name, case2_lemmas = generate_lemmas ctx zctx case2 in *)
    (*   List.map ~f:(fun l -> Z3.Boolean.mk_ite ) *)
    (*     case1_lemmas *)
    (*   let lemmas = [ *)
    (*     Z3.Boolean.mk_ite zctx *)

    (*     Z3.Arithmetic.mk_gt zctx *)
    (*       (Z3.FuncDecl.apply (len_fun zctx) [x_name]) *)
    (*       (Z3.Arithmetic.Integer.mk_numeral_i zctx 0); *)
    (*   ] in name, (lemmas @ x_lemmas) *)

    | Apply ((Id ("map", _), [l; _]), _) ->
      let l_name, l_lemmas = generate_lemmas ctx zctx l in
      [
        Z3.Boolean.mk_eq zctx
          (Z3.FuncDecl.apply (len_fun zctx) [name])
          (Z3.FuncDecl.apply (len_fun zctx) [l_name]);
      ] @ l_lemmas

    | Apply ((Id ("filter", _), [l; _]), _) ->
      let l_name, l_lemmas = generate_lemmas ctx zctx l in
      [
        Z3.Arithmetic.mk_le zctx
          (Z3.FuncDecl.apply (len_fun zctx) [name])
          (Z3.FuncDecl.apply (len_fun zctx) [l_name]);
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
      let i_name, i_lemmas = generate_lemmas ctx zctx i in
      let l_name, l_lemmas = generate_lemmas ctx zctx l in
      [
        Z3.Boolean.mk_eq zctx
          (Z3.FuncDecl.apply (len_fun zctx) [name])
          (Z3.Arithmetic.mk_add zctx [
              Z3.FuncDecl.apply (len_fun zctx) [l_name];
              Z3.FuncDecl.apply (len_fun zctx) [i_name];
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
      let f_name, f_lemmas = generate_lemmas ctx zctx f in
      [
        Z3.Boolean.mk_eq zctx
          (Z3.FuncDecl.apply (len_fun zctx) [name])
          (Z3.FuncDecl.apply (len_fun zctx) [f_name]);
      ] @ f_lemmas

    | Apply ((Id ("foldl", _), [_; Lambda ((_, Op ((Cons, [_; List ([], _)]), _)), _); _]), _)
    | Apply ((Id ("foldr", _), [_; Lambda ((_, Op ((Cons, [_; List ([], _)]), _)), _); _]), _)
    | Apply ((Id ("foldl", _), [_; Lambda ((_, Op ((RCons, [List ([], _); _]), _)), _); _]), _)
    | Apply ((Id ("foldr", _), [_; Lambda ((_, Op ((RCons, [List ([], _); _]), _)), _); _]), _) ->
      [
        Z3.Boolean.mk_eq zctx
          (Z3.FuncDecl.apply (len_fun zctx) [name])
          (Z3.Arithmetic.Integer.mk_numeral_i zctx 0);
      ]

    | _ -> []
  in
  name, lemmas

(** Given a candidate expression and some constraints on the
    expression's input and output, check those constraints using an
    SMT solver. The constraints should refer to the inputs to the
    target function using 'i1' ... 'in' and to the output using
    'o'. *)
let check_constraints
    ?(timeout=default_timeout)
    (zctx: Z3.context)
    (examples: example list)
    (* (constraints: Z3.Expr.expr list) *)
    (expr: TypedExpr.t) : bool =
  let solver = Z3.Solver.mk_solver zctx None in

  let open TypedExpr in
  match expr with
  | Lambda ((args, body), Arrow_t (args_t, _)) ->
    let assertions = List.concat_map examples ~f:(fun (ex: example) ->
        let _, input_args, output = Example.to_triple ex in

        (* Collect any relevant assertions about the inputs in this example. *)
        let named_input_asserts =
          List.map input_args ~f:(fun e ->
              let te = infer (Ctx.empty ()) e in
              generate_lemmas (ref TypedExprMap.empty) zctx te
            )
        in

        (* Collect any relevant assertions about the example output. *)
        let output_name, output_asserts =
          generate_lemmas (ref TypedExprMap.empty) zctx (infer (Ctx.empty ()) output)
        in

        (* Generate a context that binds the lambda argument names to
           the Z3 names that we generated when getting constraints for
           the inputs. *)
        let ctx =
          ref (List.fold_left
                 ~f:(fun ctx (arg, t, (z3arg, _)) ->
                     TypedExprMap.add ctx ~key:(Id (arg, t)) ~data:z3arg)
                 ~init:(TypedExprMap.empty)
                 (zip3_exn args args_t named_input_asserts))
        in

        let body_name, body_asserts = generate_lemmas ctx zctx body in

        (Z3.Boolean.mk_eq zctx output_name body_name)
        :: output_asserts
        @ body_asserts
        @ (List.concat_map named_input_asserts ~f:(Tuple.T2.get2))
      )
    in

    if List.length assertions = 0 then true else
      let () = Z3.Solver.add solver assertions in
      let () =
        let z3asserts = Z3.Solver.get_assertions solver in
        List.iter ~f:(fun a -> printf "%s\n" (Z3.Expr.to_string a)) z3asserts
      in
      (match Z3.Solver.check solver [] with
       | Z3.Solver.UNSATISFIABLE -> false
       | Z3.Solver.SATISFIABLE -> true
       | Z3.Solver.UNKNOWN -> printf "Solver returned UNKNOWN\n"; true)

  | _ -> failwith (sprintf "Unsupported expression: %s" (to_string expr))

(* let () = *)
(*   let zctx = Z3.mk_context [] in *)
(*   let constraints = [ *)
(*     Z3.Boolean.mk_eq zctx *)
(*       (Z3.FuncDecl.apply *)
(*          (len_fun zctx) *)
(*          [Z3.Expr.mk_const_s zctx "o" (list_sort zctx)]) *)
(*       (Z3.FuncDecl.apply *)
(*          (len_fun zctx) *)
(*          [Z3.Expr.mk_const_s zctx "i0" (list_sort zctx)]) *)
(*   ] in *)
(*   let expr = *)
(*     Constraint.of_string *)
(*       "(forall (x) (lambda (l) (cons 1 l)))" *)
(*     |> Constraint.to_typed_expr *)
(*   in *)
(*   printf "Meets constraints? %b\n" (check_constraints zctx constraints expr) *)
