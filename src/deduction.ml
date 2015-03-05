open Core.Std

open Ast
open Infer
open Util

let default_timeout = 1000

let int_sort ctx = Z3.Arithmetic.Integer.mk_sort ctx
let list_sort ctx = Z3.Sort.mk_uninterpreted_s ctx "Lst"
let len_fun ctx =
  Z3.FuncDecl.mk_func_decl_s ctx "len" [list_sort ctx] (int_sort ctx)

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
  | _ -> Z3.Sort.mk_uninterpreted_s ctx (Expr.typ_to_string typ)

(** Generate a Z3 assertion from a boolean expression. *)
let rec assert_of_expr (zctx: Z3.context) (expr: typed_expr) : Z3.Expr.expr =
  let aoe = assert_of_expr zctx in
  match expr with
  | Id (name, t) -> Z3.Expr.mk_const_s zctx name (sort_of_type zctx t)
  | Num (x, _) -> Z3.Arithmetic.Integer.mk_numeral_i zctx x
  | Apply ((Id (name, _), args), ret_t) ->
    let args_t = List.map ~f:typ_of_expr args in
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
  | _ -> failwith (sprintf "Unsupported expression: %s"
                     (Expr.to_string (expr_of_texpr expr)))

let assert_of_string (zctx: Z3.context) (s: string) : Z3.Expr.expr =
  typed_expr_of_string s |> assert_of_expr zctx

(** Infer a constraint about the length of the list returned by the
    target function in terms of the length of the input list(s). *)
let infer_length_constraint
    (zctx: Z3.context)
    (examples: example list) : Z3.Expr.expr =
  let check_predicate (p: int -> int -> bool) =
    List.for_all ~f:(fun e -> match e with
        | (`List i, `List o) -> p (List.length i) (List.length o)
        | _ -> failwith (sprintf "Unsupported example: %s" (Example.to_string e)))
      examples
  in
  let i_len = Z3.FuncDecl.apply (len_fun zctx)
      [Z3.Expr.mk_fresh_const zctx "i0" (list_sort zctx)] in
  let o_len = Z3.FuncDecl.apply (len_fun zctx)
      [Z3.Expr.mk_fresh_const zctx "o" (list_sort zctx)] in
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
    (ctx: Z3.Expr.expr Ctx.t)
    (zctx: Z3.context)
    (expr: typed_expr) : Z3.Expr.expr * (Z3.Expr.expr list) =
  let name_of_expr e =
    Z3.Expr.mk_fresh_const
      zctx
      (Expr.to_string (expr_of_texpr e))
      (sort_of_type zctx (typ_of_expr e))
  in

  match expr with
  | Id (name, _) ->
    (match Ctx.lookup ctx name with
     | Some z3_name -> z3_name
     | None ->
       let z3_name = name_of_expr expr in
       (Ctx.update ctx name z3_name; z3_name)), []

  | List (l, _) ->
    let name = name_of_expr expr in
    let lemmas = [
      Z3.Boolean.mk_eq zctx
        (Z3.FuncDecl.apply (len_fun zctx) [name])
        (Z3.Arithmetic.Integer.mk_numeral_i zctx (List.length l))
    ] in name, lemmas

  | Op ((Cons, [_; x]), _)
  | Op ((RCons, [x; _]), _) ->
    (* Generate a new name for this expression. *)
    let name = name_of_expr expr in

    (* Generate any lemmas about the child expressions. *)
    let x_name, x_lemmas = generate_lemmas ctx zctx x in

    (* Generate any lemmas for this expression. In this case, len(cons
       x y) = len(y) + 1 *)
    let lemmas = [
      Z3.Boolean.mk_eq zctx
        (Z3.FuncDecl.apply (len_fun zctx) [name])
        (Z3.Arithmetic.mk_add zctx [
            Z3.FuncDecl.apply (len_fun zctx) [x_name];
            Z3.Arithmetic.Integer.mk_numeral_i zctx 1;
          ]);
    ] in name, (lemmas @ x_lemmas)

  | Op ((Cdr, [x]), _) ->
    let name = name_of_expr expr in
    let x_name, x_lemmas = generate_lemmas ctx zctx x in
    let lemmas = [
      Z3.Boolean.mk_eq zctx
        (Z3.FuncDecl.apply (len_fun zctx) [name])
        (Z3.Arithmetic.mk_sub zctx [
            Z3.FuncDecl.apply (len_fun zctx) [x_name];
            Z3.Arithmetic.Integer.mk_numeral_i zctx 1;
          ]);
    ] in name, (lemmas @ x_lemmas)

  | Apply ((Id ("map", _), [l; _]), _) ->
    let name = name_of_expr expr in
    let l_name, l_lemmas = generate_lemmas ctx zctx l in
    let lemmas = [
      Z3.Boolean.mk_eq zctx
        (Z3.FuncDecl.apply (len_fun zctx) [name])
        (Z3.FuncDecl.apply (len_fun zctx) [l_name]);
    ] in name, (lemmas @ l_lemmas)

  | Apply ((Id ("filter", _), [l; _]), _) ->
    let name = name_of_expr expr in
    let l_name, l_lemmas = generate_lemmas ctx zctx l in
    let lemmas = [
      Z3.Arithmetic.mk_le zctx
        (Z3.FuncDecl.apply (len_fun zctx) [name])
        (Z3.FuncDecl.apply (len_fun zctx) [l_name]);
    ] in name, (lemmas @ l_lemmas)

  | Apply ((Id ("foldl", _),
            [l; Lambda (([a1; _], Op ((Cons, [_; Id (a2, _)]), _)), _); i]), _)
  | Apply ((Id ("foldr", _),
            [l; Lambda (([a1; _], Op ((Cons, [_; Id (a2, _)]), _)), _); i]), _)
  | Apply ((Id ("foldl", _),
            [l; Lambda (([a1; _], Op ((RCons, [Id (a2, _); _]), _)), _); i]), _)
  | Apply ((Id ("foldr", _),
            [l; Lambda (([a1; _], Op ((RCons, [Id (a2, _); _]), _)), _); i]), _)
    when a1 = a2 ->
    let name = name_of_expr expr in
    let i_name, i_lemmas = generate_lemmas ctx zctx i in
    let l_name, l_lemmas = generate_lemmas ctx zctx l in
    let lemmas = [
      Z3.Boolean.mk_eq zctx
        (Z3.FuncDecl.apply (len_fun zctx) [name])
        (Z3.Arithmetic.mk_add zctx [
            Z3.FuncDecl.apply (len_fun zctx) [l_name];
            Z3.FuncDecl.apply (len_fun zctx) [i_name];
          ]);
    ] in name, (lemmas @ l_lemmas @ i_lemmas)

  | _ -> failwith (sprintf "Unsupported expression: %s"
                     (Expr.to_string (expr_of_texpr expr)))

(** Given a candidate expression and some constraints on the
    expression's input and output, check those constraints using an
    SMT solver. The constraints should refer to the inputs to the
    target function using 'i1' ... 'in' and to the output using
    'o'. *)
let check_constraints
    ?(timeout=default_timeout)
    (zctx: Z3.context)
    (constraints: Z3.Expr.expr list)
    (expr: typed_expr) : bool =
  let solver = Z3.Solver.mk_solver zctx None in
  match expr with
  | Lambda ((args, body), Arrow_t (args_t, ret_t)) ->
    (* Create a list of assertions about the candidate expression that
       incorporates lemmas about the expression with the constraints
       inferred from the specification. *)
    let asserts =
      let name, lemmas =
        (* Generate a context that binds the argument names to the input
           names used in the constraints. *)
        let (ctx, _) =
          List.fold_left
            ~f:(fun (ctx, i) (arg, t) ->
                let name = sprintf "i%d" i in
                Ctx.bind ctx arg (Z3.Expr.mk_const_s zctx name (sort_of_type zctx t)), i + 1)
            ~init:(Ctx.empty (), 0)
            (List.zip_exn args args_t)
        in generate_lemmas ctx zctx body in
      lemmas @
      constraints @
      [Z3.Boolean.mk_eq zctx (Z3.Expr.mk_const_s zctx "o" (sort_of_type zctx ret_t)) name]
    in
    let () = Z3.Solver.add solver asserts in
    let () =
      let assertions = Z3.Solver.get_assertions solver in
      List.iter ~f:(fun a -> printf "%s\n" (Z3.Expr.to_string a)) assertions
    in
    (match Z3.Solver.check solver [] with
     | Z3.Solver.UNSATISFIABLE -> false
     | Z3.Solver.SATISFIABLE -> true
     | Z3.Solver.UNKNOWN -> printf "Solver returned UNKNOWN\n"; true)
  | _ -> failwith (sprintf "Unsupported expression: %s"
                     (Expr.to_string (expr_of_texpr expr)))

let () =
  let zctx = Z3.mk_context [] in
  let constraints = [
    Z3.Boolean.mk_eq zctx
      (Z3.FuncDecl.apply
         (len_fun zctx)
         [Z3.Expr.mk_const_s zctx "o" (list_sort zctx)])
      (Z3.FuncDecl.apply
         (len_fun zctx)
         [Z3.Expr.mk_const_s zctx "i0" (list_sort zctx)])
  ] in
  let expr =
    Constraint.of_string
      "(forall (x) (lambda (l) (cons 1 l)))"
    |> Constraint.to_typed_expr
  in
  printf "Meets constraints? %b\n" (check_constraints zctx constraints expr)
