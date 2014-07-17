open Core.Std
open Ast
open Eval
open Util

exception VerifyError

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
      | _ -> raise VerifyError)
  | `Op (op, args) -> `Op (op, exp_all args)
  | `Num _ | `Bool _ | `List _ -> expr

let rec expr_to_z3 (zctx: Z3.context) (z3ectx: z3_ctx) (expr: expr) =
  match expr with
  | `Id x -> (match lookup x z3ectx with
              | Some z3expr -> z3expr
              | None -> raise VerifyError)
  | `Num x -> Z3.Arithmetic.Integer.mk_numeral_i zctx x
  | `Bool x -> Z3.Boolean.mk_val zctx x
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
      | _             -> raise VerifyError)
  | `Lambda _ | `Let _ | `Define _ | `Apply _ | `List _ -> raise VerifyError

let rec typ_to_z3 (zctx: Z3.context) (typ: typ) = 
  match typ with
  | Num_t -> Z3.Arithmetic.Integer.mk_sort zctx
  | Bool_t -> Z3.Boolean.mk_sort zctx
  | List_t elem_typ -> Z3.Z3List.mk_list_s zctx (typ_to_string typ) (typ_to_z3 zctx elem_typ)
  | Unit_t
  | Arrow_t _ -> raise VerifyError

let typed_id_to_z3 zctx tid = 
  let id, typ = tid in
  let sort = typ_to_z3 zctx typ in
  Z3.Expr.mk_const_s zctx id sort

let verify (target_def: function_def) (constraints: constr list) =
  let open Z3.Solver in
  let `Define (target_name, `Lambda (target_args, target_body)) = target_def in
  let zctx = Z3.mk_context [] in

  let verify_constraint constr = 
    let solver = mk_simple_solver zctx in
    let constr_body, constr_ids = constr in

    (* Expand the constraint using a context that contains the
    definition of the target function. *)
    let constr_body' = 
      let ctx = bind (empty_ctx ()) ~key:target_name ~data:(`Lambda (target_args, target_body)) in
      expand ctx constr_body in

    (* let _ = Printf.printf "%s\n" (expr_to_string constr_body') in *)
    
    (* Generate a correctly typed Z3 constant for each unbound id in the constraint. *)
    let z3_consts = List.map constr_ids ~f:(typed_id_to_z3 zctx) in

    (* Convert constraint body to a Z3 expression. *)
    let z3_constr_body = 
      let ctx = List.fold2_exn constr_ids z3_consts ~init:(empty_ctx ())
                               ~f:(fun acc (id, _) z3c -> bind acc ~key:id ~data:z3c) in
      expr_to_z3 zctx ctx constr_body' in

    add solver [Z3.Boolean.mk_not zctx z3_constr_body];

    (* Add the constraint to the solver and check. *)
    match check solver [] with
    | UNSATISFIABLE -> true
    | UNKNOWN -> raise VerifyError
    | SATISFIABLE -> false
  in

  try
    if List.for_all constraints ~f:verify_constraint then Valid
    else Invalid
  with VerifyError -> Error
  
