open Core.Std

open Infer

module Specification = struct
  include Component0

  type t = specification with sexp

  let rec substitute inputs term = match term with
    | Constant _
    | Variable (Free _)
    | Variable Output -> term
    | Variable (Input i) -> Array.get inputs i
    | Apply (func, args) -> Apply (func, List.map args ~f:(substitute inputs))
  
  (* let evaluate spec inputs = *)
  (*   List.find_map spec ~f:(fun clause -> *)
  (*       List.fold_left clause ~init:(Some String.Map.empty) ~f:(fun ctx pred -> *)
  (*           match pred with *)
  (*           | Binary (Eq, t1, t2) -> )) *)

  let of_string s =
    let lexbuf = Lexing.from_string s in
    try Ok (Component_parser.specification_eof Component_lexer.token lexbuf) with
    | Component_parser.Error -> error "Failed to parse." s String.sexp_of_t
    | Component_lexer.SyntaxError err ->
      error "Failed to parse." (s, err) <:sexp_of<string * string>>
    | Parsing.Parse_error -> error "Failed to parse." s String.sexp_of_t
end

type t = {
  name : string;
  spec : Specification.t;
  type_ : Type.t;
} with sexp

let create name spec type_ =
  let open Or_error.Monad_infix in
  Specification.of_string spec >>| fun spec ->
  { name; spec; type_ = Type.of_string type_; }

let drop = create "drop"
    "i2 >= 0 ^ len(i1) >= i2 ^ len(i1) - i2 = len(r) ^ set(i1) ⊃ set(r)"
    "(a list, int) -> a list"

let tail = create "tail"
    "len(i1) > 0 ^ len(i1) - 1 = len(r) ^ set(i1) ⊃ set(r)"
    "(a list) -> a list"

module Constraint = struct
  let int_sort ctx = Z3.Arithmetic.Integer.mk_sort ctx
  let list_sort ctx = Z3.Sort.mk_uninterpreted_s ctx "Lst"
  let len_fun ctx = Z3.FuncDecl.mk_func_decl_s ctx "len" [list_sort ctx] (int_sort ctx)

  (* let rec to_z3 zctx spec = *)
  (*   List.map spec ~f:(fun pred -> ) *)
  (*   Z3.Boolean.mk_and zctx *)
      
  (*   let open TypedExpr in *)
  (*   let aoe = assert_of_expr zctx in *)
  (*   match spec with *)
  (*   | Id (name, t) -> Z3.Expr.mk_const_s zctx name (sort_of_type' zctx t) *)
  (*   | Num (x, _) -> z3_int zctx x *)
  (*   | List ([], t) -> Z3.Z3List.nil (sort_of_type' zctx t) *)
  (*   | List (xs, t) -> *)
  (*     (\* Convert to cons expression, instead of duplicating logic. *\) *)
  (*     let cons_expr = List.fold_right xs ~init:(List ([], t)) ~f:(fun elem rest -> *)
  (*         Op ((Cons, [elem; rest]), t)) *)
  (*     in *)
  (*     aoe cons_expr *)
  (*   | Apply ((Id (name, Arrow_t (args_t, _)), args), ret_t) -> *)
  (*     let args_z3 = List.map ~f:aoe args in *)
  (*     let args_sorts = List.map ~f:(Z3.Expr.get_sort) args_z3 in *)
  (*     let func_decl = *)
  (*       Z3.FuncDecl.mk_func_decl_s zctx name args_sorts (sort_of_type' zctx ret_t) *)
  (*     in *)
  (*     z3_app func_decl (List.map ~f:aoe args) *)
  (*   | Op ((Eq, [a1; a2]), _) -> z3_eq zctx (aoe a1) (aoe a2) *)
  (*   | Op ((Neq, [a1; a2]), _) -> *)
  (*     Z3.Boolean.mk_not zctx (z3_eq zctx (aoe a1) (aoe a2)) *)
  (*   | Op ((Lt, [a1; a2]), _) -> Z3.Arithmetic.mk_lt zctx (aoe a1) (aoe a2) *)
  (*   | Op ((Gt, [a1; a2]), _) -> Z3.Arithmetic.mk_gt zctx (aoe a1) (aoe a2) *)
  (*   | Op ((Leq, [a1; a2]), _) -> Z3.Arithmetic.mk_le zctx (aoe a1) (aoe a2) *)
  (*   | Op ((Geq, [a1; a2]), _) -> Z3.Arithmetic.mk_ge zctx (aoe a1) (aoe a2) *)
  (*   | Op ((And, [a1; a2]), _) -> Z3.Boolean.mk_and zctx [aoe a1; aoe a2] *)
  (*   | Op ((Or, [a1; a2]), _) -> Z3.Boolean.mk_or zctx [aoe a1; aoe a2] *)
  (*   | Op ((Not, [a]), _) -> Z3.Boolean.mk_not zctx (aoe a) *)
  (*   | Op ((If, [a1; a2; a3]), _) -> *)
  (*     Z3.Boolean.mk_ite zctx (aoe a1) (aoe a2) (aoe a3) *)
  (*   | Op ((Car, [a]), t) -> *)
  (*     let z3_a = aoe a in *)
  (*     let sort = Z3.Expr.get_sort z3_a in *)
  (*     z3_app (Z3.Z3List.get_head_decl sort) [z3_a] *)
  (*   | Op ((Cdr, [a]), t) -> *)
  (*     let z3_a = aoe a in *)
  (*     let sort = Z3.Expr.get_sort z3_a in *)
  (*     z3_app (Z3.Z3List.get_tail_decl sort) [z3_a] *)
  (*   | Op ((Cons, [a1; a2]), t) -> *)
  (*     let a1_z3 = aoe a1 in *)
  (*     let sort = *)
  (*       let a1_sort = Z3.Expr.get_sort a1_z3 in *)
  (*       let name = Z3.Symbol.get_string (Z3.Sort.get_name a1_sort) in *)
  (*       Z3.Z3List.mk_list_s zctx name a1_sort *)
  (*     in *)
  (*     (\* Make sure that nil gets assigned a concrete sort if possible. *\) *)
  (*     let a2_z3 = (match a2 with *)
  (*         | List ([], _) -> Z3.Z3List.nil sort *)
  (*         | _ -> aoe a2) *)
  (*     in *)
  (*     z3_app (Z3.Z3List.get_cons_decl sort) [a1_z3; a2_z3] *)
  (*   | _ -> failwith (sprintf "Unsupported expression: %s" (to_string expr)) *)

  let check c = ()
end

(* type unify_error = [ *)
(*   | `FailedOccursCheck *)
(*   | `NonUnifiable *)
(* ] *)

(* exception UnifyError of unify_error *)

(* let rec occurs var t = match t with *)
(*   | Variable x -> var = x *)
(*   | Apply (f, a) -> List.exists a ~f:(occurs var) *)
(*   | Constant _ -> false *)

(* let rec apply sub t = match t with *)
(*   | Variable (Free id) -> Option.value (String.Map.find sub id) ~default:t *)
(*   | Apply (f, a) -> Apply (f, List.map a ~f:(apply sub)) *)
(*   | Constant _ -> t *)

(* let rec unify t1 t2 = *)
(*   match t1, t2 with *)
(*   | Variable (Input i), _ | _, Variable (Input i) ->  *)
(*   | Variable x, Variable y -> if x = y then String.Map.empty else String.Map.singleton x t2 *)
(*   | Constant x, Constant y -> if x = y then String.Map.empty else raise (UnifyError `NonUnifiable) *)
(*   | Apply (f1, a1), Apply (f2, a2) -> *)
(*     if f1 = f2 then match List.zip a1 a2 with *)
(*       | Some a -> List.fold_left a ~init:String.Map.empty ~f:(fun sub (a1, a2) -> *)
(*           let sub' = unify a1 a2 in *)
(*           String.Map.merge sub sub' ~f:(function *)
(*               | `Both (x1, x2) -> )) *)
(*       | None -> raise (UnifyError `NonUnifiable) *)
(*     else raise (UnifyError `NonUnifiable) *)

(* let evaluate spec inputs = *)
  

(* let (plus: specification) = [ *)
(*   [ Binary (Eq, Variable (Input 0), Constant (Int 0)); *)
(*     Binary (Eq, Variable Output, Variable (Input 1)); ]; *)
(*   [ Binary (Eq, Variable (Input 1), Constant (Int 0)); *)
(*     Binary (Eq, Variable Output, Variable (Input 0)); ]; *)
(*   [ Binary (Eq, Variable (Input 0), Apply ("minus", [ Variable (Free 0); Variable (Free 1) ])); *)
(*     Binary (Eq, Variable (Input 1), Variable (Free 1)); *)
(*     Binary (Eq, Variable Output, Variable (Free 0)); ]; *)
(*   [ Binary (Eq, Variable (Input 1), Apply ("minus", [ Variable (Free 0); Variable (Free 1) ])); *)
(*     Binary (Eq, Variable (Input 0), Variable (Free 1)); *)
(*     Binary (Eq, Variable Output, Variable (Free 0)); ]; *)
(* ] *)

(* let plus = *)
(*   "(i0 == 0 ^ o == i1) v (i1 == 0 ^ o == i0) v (i0 == Minus(x, y) ^ i1 == y ^ o == x) v (i1 == Minus(x, y) ^ i0 == y ^ o == x)" *)
(*   |> of_string *)
