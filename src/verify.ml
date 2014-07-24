open Core.Std
open Ast
open Eval
open Util

exception VerifyError of string

let verify_error str = raise (VerifyError str)

type status = 
  | Invalid
  | Valid
  | Error

type expr_ctx = expr String.Map.t ref
type z3_ctx = Z3.Expr.expr String.Map.t ref

let rec expand (ctx: expr_ctx) (expr: expr) : expr =
  let exp e = expand ctx e in
  let exp_all es = List.map ~f:exp es in
  match expr with
  | `Id id -> (match lookup id ctx with Some expr' -> expr' | None -> expr)
  | `Define (id, body) -> `Define (id, expand ctx body)
  | `Let (id, bound, body) -> expand (bind ctx ~key:id ~data:(expand ctx bound)) body
  | `Lambda (args, body) ->
     let ctx' = List.fold args ~init:ctx ~f:(fun a (id, _) -> unbind a ~key:id) in
     `Lambda (args, expand ctx' body)
  | `Apply (func, args) ->
     let args' = exp_all args in
     let func' = exp func in
     (match func' with
      | `Lambda (lambda_args, body) ->
         let ctx' = List.fold2_exn lambda_args args' ~init:ctx
                                   ~f:(fun a (id, _) arg -> bind a ~key:id ~data:arg) in
         expand ctx' body
      | _ -> verify_error (Printf.sprintf "Tried to apply a non-lambda expression. (%s)" 
                                          (expr_to_string expr)))
  | `Op (op, args) -> `Op (op, exp_all args)
  | `Num _ | `Bool _ | `List _ -> expr

let rec typ_to_z3 (zctx: Z3.context) (typ: typ) : Z3.Sort.sort = 
  match typ with
  | Num_t -> Z3.Arithmetic.Integer.mk_sort zctx
  | Bool_t -> Z3.Boolean.mk_sort zctx
  | List_t elem_typ -> Z3.Z3List.mk_list_s zctx (typ_to_string typ) (typ_to_z3 zctx elem_typ)
  | Unit_t
  | Arrow_t _ -> verify_error "Unit_t and Arrow_t are not supported by Z3."

let typed_id_to_z3 zctx tid = 
  let id, typ = tid in
  let sort = typ_to_z3 zctx typ in
  Z3.Expr.mk_const_s zctx id sort

let rec const_to_z3 (zctx: Z3.context) (const: const) : Z3.Expr.expr = 
  match const with
  | `Num x  -> Z3.Arithmetic.Integer.mk_numeral_i zctx x
  | `Bool x -> Z3.Boolean.mk_val zctx x
  | `List (x, t) ->
     let sort = typ_to_z3 zctx t in
     let nil = Z3.Z3List.nil sort in
     let cons = Z3.Z3List.get_cons_decl sort in
     List.fold_right x ~init:nil
                     ~f:(fun elem acc -> 
                         let z3_elem = const_to_z3 zctx elem in
                         Z3.FuncDecl.apply cons [z3_elem; acc])  

let rec expr_to_z3 (zctx: Z3.context) (z3ectx: z3_ctx) (expr: expr) =
  match expr with
  | `Num x -> const_to_z3 zctx (`Num x)
  | `Bool x -> const_to_z3 zctx (`Bool x)
  | `List x -> const_to_z3 zctx (`List x)
  | `Id x -> (match lookup x z3ectx with
              | Some z3expr -> z3expr
              | None -> verify_error (Printf.sprintf "Looking up identifier \"%s\" failed." x))
  | `Op (op, op_args) ->
     (match op, (List.map ~f:(expr_to_z3 zctx z3ectx) op_args) with
      | Plus, z3_args -> Z3.Arithmetic.mk_add zctx z3_args
      | Minus, z3_args-> Z3.Arithmetic.mk_sub zctx z3_args
      | Mul, z3_args  -> Z3.Arithmetic.mk_mul zctx z3_args
      | Div, [a1; a2] -> Z3.Arithmetic.mk_div zctx a1 a2
      | Mod, [a1; a2] -> Z3.Arithmetic.Integer.mk_mod zctx a1 a2
      | Eq,  [a1; a2] -> Z3.Boolean.mk_eq zctx a1 a2
      | Neq, [a1; a2] -> Z3.Boolean.mk_not zctx (Z3.Boolean.mk_eq zctx a1 a2)
      | Lt,  [a1; a2] -> Z3.Arithmetic.mk_lt zctx a1 a2
      | Leq, [a1; a2] -> Z3.Arithmetic.mk_le zctx a1 a2
      | Gt,  [a1; a2] -> Z3.Arithmetic.mk_gt zctx a1 a2
      | Geq, [a1; a2] -> Z3.Arithmetic.mk_ge zctx a1 a2
      | And, z3_args  -> Z3.Boolean.mk_and zctx z3_args
      | Or, z3_args   -> Z3.Boolean.mk_or zctx z3_args
      | Not, [a]      -> Z3.Boolean.mk_not zctx a
      | If, [a; b; c] -> Z3.Boolean.mk_ite zctx a b c
      | Cons, [a; b]  -> let sort = Z3.Expr.get_sort b in
                         let cons = Z3.Z3List.get_cons_decl sort in
                         Z3.FuncDecl.apply cons [a; b]
      | Car, [a]      -> let sort = Z3.Expr.get_sort a in
                         let head = Z3.Z3List.get_head_decl sort in
                         Z3.FuncDecl.apply head [a]
      | Cdr, [a]      -> let sort = Z3.Expr.get_sort a in
                         let tail = Z3.Z3List.get_tail_decl sort in
                         Z3.FuncDecl.apply tail [a]
      | _ -> verify_error "Attempted to convert unsupported operator to Z3.")
  | `Lambda _ 
  | `Let _ 
  | `Define _ 
  | `Apply _ -> verify_error "(lambda, let, define, apply) are not supported by Z3."

let verify_example (target_prog: program) (example: example) : bool =
  let (input, result) = example in
  let test_program = target_prog @ [(input :> expr)] in
  try (Eval.prog_eval test_program) = (result :> value) with
    RuntimeError _ -> false

let verify_examples (target_prog: program) (examples: example list) : bool =
  List.for_all examples ~f:(verify_example target_prog)

let verify_constraint (zctx: Z3.context) (target_def: function_def) (constr: constr) : bool = 
  let open Z3.Solver in
  let `Define (target_name, `Lambda (target_args, target_body)) = target_def in
  let solver = mk_simple_solver zctx in
  let constr_body, constr_ids = constr in

  (* Expand the constraint using a context that contains the
    definition of the target function. *)
  let constr_body' =
    let ctx = bind (empty_ctx ())
                   ~key:target_name
                   ~data:(`Lambda (target_args, target_body)) in
    expand ctx constr_body in

  (* let _ = Printf.printf "%s\n" (expr_to_string constr_body') in *)
  
  (* Generate a correctly typed Z3 constant for each unbound id in the constraint. *)
  let z3_consts = List.map constr_ids ~f:(typed_id_to_z3 zctx) in

  (* Convert constraint body to a Z3 expression. *)
  let z3_constr_body = 
    let ctx = List.fold2_exn constr_ids z3_consts 
                             ~init:(empty_ctx ())
                             ~f:(fun acc (id, _) z3c -> bind acc ~key:id ~data:z3c) in
    expr_to_z3 zctx ctx constr_body' in

  (* let _ = Printf.printf "%s\n" (Z3.Expr.to_string z3_constr_body) in *)

  (* Add the constraint to the solver and check. *)
  add solver [Z3.Boolean.mk_not zctx z3_constr_body];
  match check solver [] with
  | UNSATISFIABLE -> true
  | UNKNOWN -> verify_error "Z3 returned unknown."
  | SATISFIABLE -> false

let verify (examples: example list) (constraints: constr list) (target_def: function_def) : status =
  if List.for_all examples ~f:(verify_example [(target_def :> expr)])
  then
    let zctx = Z3.mk_context [] in
    try
      if List.for_all constraints ~f:(verify_constraint zctx target_def)
      then Valid
      else Invalid
    with VerifyError msg -> 
      Printf.printf "%s\n" msg; 
      Error
  else Invalid
