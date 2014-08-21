open Core.Std
open Printf
open Ast
open Eval

exception VerifyError of string

let verify_error str = raise @@ VerifyError str

type status = 
  | Invalid
  | Valid
  | Error

let rec expand ctx (expr: expr) : expr =
  let exp e = expand ctx e in
  let exp_all es = List.map ~f:exp es in
  match expr with
  | `Id id -> (match Ctx.lookup ctx id with Some expr' -> expr' | None -> expr)
  | `Let (id, bound, body) -> expand (Ctx.bind ctx id (expand ctx bound)) body
  | `Lambda (args, body) ->
     let ctx' = List.fold args ~init:ctx ~f:(fun ctx' id -> Ctx.unbind ctx' id) in
     `Lambda (args, expand ctx' body)
  | `Apply (func, args) ->
     let args' = exp_all args in
     let func' = exp func in
     (match func' with
      | `Lambda (lambda_args, body) ->
         let ctx' = List.fold2_exn lambda_args args' ~init:ctx
                                   ~f:(fun ctx' id arg -> Ctx.bind ctx' id arg) in
         expand ctx' body
      | _ -> verify_error (sprintf "Tried to apply a non-lambda expression. (%s)"
                                   (expr_to_string expr)))
  | `Op (op, args) -> `Op (op, exp_all args)
  | `Num _ | `Bool _ | `List _ -> expr

let expr_to_value expr : value option =
  let rec etv = function
    | `Num x -> `Num x
    | `Bool x -> `Bool x
    | `List x -> `List (List.map x ~f:etv)
    | _ -> verify_error "Not a value."
  in
  try Some (etv expr) with VerifyError _ -> None

let rec typ_to_z3 (zctx: Z3.context) (typ: typ) : Z3.Sort.sort =
  match typ with
  | Const_t Num -> Z3.Arithmetic.Integer.mk_sort zctx
  | Const_t Bool -> Z3.Boolean.mk_sort zctx
  | App_t ("list", [elem_typ]) -> Z3.Z3List.mk_list_s zctx (typ_to_string typ) (typ_to_z3 zctx elem_typ)
  | App_t ("list", _) -> verify_error "Wrong number of arguments to list."
  | App_t (const, _) -> verify_error (sprintf "Type constructor %s is not supported." const)
  | Var_t _
  | Arrow_t _ -> verify_error "Arrow_t are not supported by Z3."

let typed_id_to_z3 zctx tid =
  let id, typ = tid in
  let sort = typ_to_z3 zctx typ in
  Z3.Expr.mk_const_s zctx id sort

(* let rec const_to_z3 (zctx: Z3.context) (const: const) : Z3.Expr.expr = *)
(*   match const with *)
(*   | `Num x  -> Z3.Arithmetic.Integer.mk_numeral_i zctx x *)
(*   | `Bool x -> Z3.Boolean.mk_val zctx x *)
(*   | `List (x, t) -> *)
     (* let sort = typ_to_z3 zctx t in *)
     (* let nil = Z3.Z3List.nil sort in *)
     (* let cons = Z3.Z3List.get_cons_decl sort in *)
     (* List.fold_right x ~init:nil *)
     (*                 ~f:(fun elem acc -> *)
     (*                     let z3_elem = const_to_z3 zctx elem in *)
     (*                     Z3.FuncDecl.apply cons [z3_elem; acc]) *)

let rec expr_to_z3 (zctx: Z3.context) z3ectx (expr: expr) =
  match expr with
  | `Num x -> Z3.Arithmetic.Integer.mk_numeral_i zctx x
  | `Bool x -> Z3.Boolean.mk_val zctx x
  (* | `List x ->  *)
  (*    let sort = typ_to_z3 zctx t in *)
  (*    let nil = Z3.Z3List.nil sort in *)
  (*    let cons = Z3.Z3List.get_cons_decl sort in *)
  (*    List.fold_right x ~init:nil *)
  (*                    ~f:(fun elem acc -> *)
  (*                        let z3_elem = const_to_z3 zctx elem in *)
  (*                        Z3.FuncDecl.apply cons [z3_elem; acc]) *)
  | `Id x -> (match Ctx.lookup z3ectx x with
              | Some z3expr -> z3expr
              | None -> verify_error (sprintf "Looking up identifier \"%s\" failed." x))
  | `Op (op, op_args) ->
     let open Op in
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
  | `List _
  | `Lambda _ 
  | `Let _ 
  | `Apply _ -> verify_error "(list, lambda, let, define, apply) are not supported by Z3."

let verify_example (target: expr -> expr) (example: example) : bool =
  let input, result = example in
  match expr_to_value result with
  | Some result' ->
     (try (Eval.eval (Ctx.empty ()) (target input)) = result'
      with RuntimeError _ -> false)
  | None -> verify_error (sprintf "Example result is not a value. (%s)" 
                                 (expr_to_string result))

let verify_examples target examples = List.for_all examples ~f:(verify_example target)

let verify_constraint (zctx: Z3.context) (target: expr -> expr) (constr: constr) : bool = 
  let open Z3.Solver in
  let solver = mk_simple_solver zctx in
  let constr_body, constr_ids = constr in

  (* Wrap the constraint in a let containing the definition of the
  target function and then expand. *)
  let constr_body' = expand (Ctx.empty ()) (target constr_body) in

  (* let _ = Printf.printf "%s\n" (expr_to_string constr_body') in *)
  
  (* Generate a correctly typed Z3 constant for each unbound id in the constraint. *)
  let z3_consts = List.map constr_ids ~f:(typed_id_to_z3 zctx) in

  (* Convert constraint body to a Z3 expression. *)
  let z3_constr_body = 
    let ctx = List.fold2_exn constr_ids z3_consts 
                             ~init:(Ctx.empty ())
                             ~f:(fun acc (id, _) z3c -> Ctx.bind acc id z3c) in
    expr_to_z3 zctx ctx constr_body' in

  (* let _ = Printf.printf "%s\n" (Z3.Expr.to_string z3_constr_body) in *)

  (* Add the constraint to the solver and check. *)
  add solver [Z3.Boolean.mk_not zctx z3_constr_body];
  match check solver [] with
  | UNSATISFIABLE -> true
  | UNKNOWN -> verify_error "Z3 returned unknown."
  | SATISFIABLE -> false

let verify (examples: example list) (constraints: constr list) (target: expr -> expr) : status =
  if verify_examples target examples
  then
    let zctx = Z3.mk_context [] in
    try
      if List.for_all constraints ~f:(verify_constraint zctx target)
      then Valid
      else Invalid
    with VerifyError msg -> 
      Printf.printf "%s\n" msg; 
      Error
  else Invalid
