open Core.Std

open Collections
open Component

module KTree = struct
  type 'a t =
    | Leaf of 'a
    | Node of 'a * 'a t list
  with sexp, compare

  let value = function
    | Leaf x | Node (x, _) -> x

  let rec fold ~f = function
    | Leaf x -> f x []
    | Node (x, xs) -> f x (List.map xs ~f:(fold ~f))

  let rec map ~f = function
    | Leaf x -> Leaf (f x)
    | Node (x, xs) -> Node (f x, List.map xs ~f:(map ~f))
end

type t = {
  input_spec : Predicate.t list;
  body_spec : Predicate.t list KTree.t;
  sorts : Sort.t Variable.Map.t;
} with sexp, compare

let equal c1 c2 = compare c1 c2 = 0

open Or_error.Monad_infix

module P = Predicate
module Te = Term
module C = Constant
module V = Variable
module S = Specification

module H = Hypothesis.Hypothesis
module SD = Hypothesis.StaticDistance
module Sk = Hypothesis.Skeleton
module Sp = Hypothesis.Specification

let merge_sorts sorts =
  let merge2 = V.Map.merge ~f:(fun ~key:k -> function
      | `Both (s, s') -> if Sort.equal s s' then Some s else
          failwiths "Examples have conflicting sorts." (s, s')
            <:sexp_of<Sort.t * Sort.t>>
      | `Left s | `Right s -> Some s)
  in
  Or_error.try_with (fun () -> List.fold sorts ~init:V.Map.empty ~f:merge2)

let of_skeleton names components s =
  let unbound_component_err func =
    error "Unbound component." func <:sexp_of<string>>
  in

  let unexpected_skeleton_err s =
    error "Unexpected skeleton type." s <:sexp_of<Hypothesis.Specification.t Sk.t>>
  in

  let fresh_int = Util.Fresh.mk_fresh_int_fun () in
  let fresh_name () = sprintf "f%d" (fresh_int ()) in

  let spec_of_skeleton_node child_names =
    let ret_var = V.Free (fresh_name ()) in

    let of_apply func =
      match String.Map.find components func with
      | Some component ->
        let vmap =
          (List.mapi child_names ~f:(fun i name -> V.Input (i + 1), name)) @ [V.Output, ret_var]
          |> V.Map.of_alist_exn
        in
        let spec = S.substitute_var vmap component.spec in
        Ok (spec, ret_var)
      | None -> unbound_component_err func
    in
      
    function
    | Sk.Num_h (x, _) -> Ok ({
        S.constraints = [
          P.Binary (P.Eq, Te.Variable ret_var, Te.Constant (C.Int x))
        ];
        S.sorts = V.Map.of_alist_exn [ret_var, Sort.Int];
      }, ret_var)

    | Sk.Bool_h (x, _) ->
      Ok ({
        S.constraints = [
          P.Binary (P.Eq, Te.Variable ret_var, Te.Constant (C.Bool x))
        ];
        S.sorts = V.Map.of_alist_exn [ret_var, Sort.Bool];
      }, ret_var)

    | Sk.List_h (x, _) ->
      let len = List.length x in
      Ok ({
        S.constraints = [
          P.Binary (P.Eq, Te.Apply ("Len", [Te.Variable ret_var]), Te.Constant (C.Int len))
        ];
        S.sorts = V.Map.of_alist_exn [ret_var, Sort.List];
      }, ret_var)

    | Sk.Id_h (Sk.StaticDistance sd, _) -> begin match SD.Map.find names sd with
        | Some ret_var -> Ok (S.top, ret_var)
        | None -> error "Unbound free variable." (sd, names) <:sexp_of<SD.t * V.t SD.Map.t>>
      end

    | Sk.Apply_h ((Sk.Id_h (Sk.Name func, _), _), _) -> of_apply func
    | Sk.Op_h ((op, _), _) -> of_apply (Expr.Op.to_string op)

    | Sk.Hole_h (h, _) ->
      Sort.of_type h.Hypothesis.Hole.type_ >>| fun sort -> ({
        S.constraints = [];
        S.sorts = V.Map.of_alist_exn [ ret_var, sort ];
      }, ret_var)

    | s -> unexpected_skeleton_err s
  in

  let rec of_skeleton' = function
    | Sk.Num_h _ | Sk.Bool_h _ | Sk.Id_h _ | Sk.List_h _ | Sk.Hole_h _ as s ->
      spec_of_skeleton_node [] s >>| fun (spec, var) ->
      (KTree.Leaf spec.S.constraints, spec.S.sorts, var)
    | Sk.Apply_h ((_, args), _) | Sk.Op_h ((_, args), _) as s ->
      List.map args ~f:of_skeleton' |> Or_error.all >>= fun children ->
      let (child_trees, child_sorts, child_names) = List.unzip3 children in
      spec_of_skeleton_node child_names s >>= fun (spec, var) ->
      merge_sorts (spec.S.sorts::child_sorts) >>| fun sorts ->
      (KTree.Node (spec.S.constraints, child_trees), sorts, var)
    | s -> unexpected_skeleton_err s
  in      

  of_skeleton' s

let to_z3 zctx c =
  let predicate_list_to_z3 preds =
    List.map preds ~f:(fun p ->
        P.to_z3 c.sorts zctx p >>| fun z3_p -> (p, z3_p))
    |> Or_error.all
  in
  
  let rec body_spec_to_z3 = function
    | KTree.Node (preds, children) ->
      predicate_list_to_z3 preds >>= fun preds ->
      List.map children ~f:body_spec_to_z3 |> Or_error.all
      >>| fun child_preds -> KTree.Node (preds, child_preds)
    | KTree.Leaf preds ->
      predicate_list_to_z3 preds >>| fun preds -> KTree.Leaf preds
  in

  predicate_list_to_z3 c.input_spec >>= fun input_z3 ->
  body_spec_to_z3 c.body_spec >>| fun body_z3 ->
  (input_z3, body_z3)

let background zctx =
  let background_str =
    "(assert (forall ((x Lst)) (>= (Len x) 0))) \
     (assert (forall ((x Lst) (y Lst) (z Lst)) (=> (and (Subset x y) (Subset y z)) (Subset x z)))) \
     (assert (forall ((x Lst) (y Lst) (z Lst)) (=> (and (Superset x y) (Superset y z)) (Superset x z)))) \
     (assert (forall ((x Lst) (y Lst)) (=> (Subset x y) (Superset y x)))) \
     (assert (forall ((x Lst) (y Lst)) (=> (Superset x y) (Subset y x)))) \
     (assert (forall ((x Lst) (y Lst)) (=> (and (Subset x y) (Subset y x)) (= x y)))) \
     (assert (forall ((x Lst) (y Lst)) (=> (and (Superset x y) (Superset y x)) (= x y)))) \
     (assert (forall ((x Lst) (y Lst)) (=> (> (Len x) (Len y)) (not (Superset y x))))) \
     (assert (forall ((x Lst) (y Lst)) (=> (= (Len x) 0) (Superset y x))))"
  in
  let (sort_symbols, sorts) = List.unzip (Component.Z3_Defs.Sorts.mapping zctx) in
  let (func_symbols, funcs) = List.unzip (Component.Z3_Defs.Functions.mapping zctx) in
  Z3.SMT.parse_smtlib2_string zctx background_str sort_symbols sorts func_symbols funcs

let prune c =
  let cfg = ["UNSAT_CORE", "true"] in
  let zctx = Z3.mk_context cfg in
  to_z3 zctx c >>| fun (z3_input_spec, z3_body_spec) ->
  let (_, z3_input_clauses) = List.unzip z3_input_spec in
  let z3_body_clauses = KTree.fold z3_body_spec ~f:(fun preds z3s ->
      let (_, z3_preds) = List.unzip preds in
      z3_preds @ (List.concat z3s))
  in
  let z3_clauses =
    z3_input_clauses @ z3_body_clauses
    |> List.map ~f:(fun z3 ->
        let b = Z3.Expr.mk_fresh_const zctx "b" (Z3.Boolean.mk_sort zctx) in
        (Z3.Boolean.mk_iff zctx b z3, b, z3))
  in
  let solver = Z3.Solver.mk_simple_solver zctx in
  let z3_with_boolean, z3_booleans, z3_without_boolean =
    List.unzip3 z3_clauses
  in
  Z3.Solver.assert_and_track_l solver z3_with_boolean z3_booleans;
  Z3.Solver.add solver [background zctx];
  match Z3.Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE ->
    let core = Z3.Solver.get_unsat_core solver in
    let core_clauses = List.map core ~f:(fun b ->
        let m_clause =
          List.find_map z3_clauses ~f:(fun (_, b', z3) ->
              if Z3.AST.equal b (Z3.Expr.ast_of_expr b') then Some z3 else None)
        in
        Option.value_exn m_clause)
    in
    let input_spec =
      List.filter_map z3_input_spec ~f:(fun (p, z3_p) ->
          if List.exists core_clauses ~f:(fun z3_p' ->
              Z3.AST.equal
                (Z3.Expr.ast_of_expr z3_p)
                (Z3.Expr.ast_of_expr z3_p'))
          then Some p else None)
    in
    let body_spec = KTree.map z3_body_spec ~f:(fun preds ->
        List.filter_map preds ~f:(fun (p, z3_p) ->
            if List.exists core_clauses ~f:(fun z3_p' ->
              Z3.AST.equal
                (Z3.Expr.ast_of_expr z3_p)
                (Z3.Expr.ast_of_expr z3_p'))
          then Some p else None))
    in
    `Conflict { c with input_spec; body_spec; }
  | Z3.Solver.UNKNOWN
  | Z3.Solver.SATISFIABLE -> `NoConflict

let of_hypothesis_unpruned components h =
  (* Generate specifications for each of the input variables in the
     hypothesis from the input-output examples. *)
  let m_input_specs = match H.spec h with
    | Sp.Examples exs -> S.of_examples exs
    | s -> error "Unsupported specification type." s Sp.sexp_of_t
  in
  m_input_specs >>= fun input_specs ->
  (* Generate a mapping from the input variables in the hypothesis to
     specification input variables Input 1 ... Input n. *)
  Or_error.try_with (fun () -> 
      SD.Map.fold input_specs ~init:(1, SD.Map.empty, [], V.Map.empty)
        ~f:(fun ~key:sd ~data:spec (i, names, preds, sorts) ->
            let var = V.Input i in
            let names = SD.Map.add names ~key:sd ~data:var in
            let spec = S.substitute_var (V.Map.of_alist_exn [V.Input 1, var]) spec in
            let preds = spec.S.constraints @ preds in
            let sorts = merge_sorts [spec.S.sorts; sorts] |> Or_error.ok_exn in
            (i + 1, names, preds, sorts)))
  >>= fun (_, names, input_spec, input_sorts) ->
  of_skeleton names components (H.skeleton h) >>= fun (body_spec, body_sorts, ret_val) ->
  merge_sorts [input_sorts; body_sorts] >>| fun sorts ->
  {
    input_spec = (P.Binary (P.Eq, Te.Variable V.Output, Te.Variable ret_val))::input_spec;
    body_spec; sorts;    
  }

let of_hypothesis ?(components = Component.stdlib) h =
  of_hypothesis_unpruned components h >>= prune
