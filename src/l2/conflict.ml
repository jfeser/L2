open Core.Std

open Collections
    
open Or_error.Monad_infix

module T = Component.Term
module C = Component.Constant
module V = Component.Variable
module S = Component.Specification
module Sort = Component.Sort

module H = Hypothesis.Hypothesis
module SD = Hypothesis.StaticDistance
module Sk = Hypothesis.Skeleton
module Sp = Hypothesis.Specification

(* let merge_sorts sorts = *)
(*   let merge2 = V.Map.merge ~f:(fun ~key:k -> function *)
(*       | `Both (s, s') -> if Sort.equal s s' then Some s else *)
(*           failwiths "Examples have conflicting sorts." (s, s') *)
(*             <:sexp_of<Sort.t * Sort.t>> *)
(*       | `Left s | `Right s -> Some s) *)
(*   in *)
(*   Or_error.try_with (fun () -> List.fold sorts ~init:V.Map.empty ~f:merge2) *)

(** Requires: 'components' is a mapping from strings to
    components. 's' is a skeleton which is a composition of functions,
    variables, and constants.

    Ensures: The returned tree contains a node for each node in the
    input tree. The nodes in the output tree are over-approximate
    specifications of the nodes in the input tree.
*)
let spec_tree_of_skeleton (components : S.t String.Map.t) (s : 'a Sk.t) : S.t KTree.t Or_error.t =
  let unexpected_skeleton_err s =
    error "Unexpected skeleton type." s <:sexp_of<Hypothesis.Specification.t Sk.t>>
  in

  let lookup_component name =
    match String.Map.find components name with
    | Some spec -> Ok spec
    | None -> error "No specification for component." name <:sexp_of<string>>
  in

  let spec_of_skeleton_node = function
    | Sk.Num_h (x, _) -> Ok {
        S._constraint = T.Apply ("Eq", [T.Variable V.Output; T.Constant (C.Int x)]);
        S.sorts = V.Map.singleton V.Output Sort.Int;
      }

    | Sk.Bool_h (true, _) -> S.of_string "r where r : bool"
    | Sk.Bool_h (false, _) -> S.of_string "Not(r) where r : bool"

    | Sk.List_h (x, _) ->
      let len = List.length x in
      Ok {
        S._constraint = T.Apply ("Eq", [T.Apply ("Len", [T.Variable V.Output]); T.Constant (C.Int len)]);
        S.sorts = V.Map.singleton V.Output Sort.List;
      }

    | Sk.Id_h (Sk.Id.Name name, _)
    | Sk.Apply_h ((Sk.Id_h (Sk.Id.Name name, _), _), _) -> lookup_component name
    | Sk.Op_h ((op, _), _) -> lookup_component (Expr.Op.to_string op)

    | Sk.Hole_h (h, _) -> Ok S.top
                            
    | s -> unexpected_skeleton_err s
  in

  let rec spec_tree_of_skeleton' = function
    | Sk.Num_h _
    | Sk.Bool_h _
    | Sk.Id_h _
    | Sk.List_h _
    | Sk.Hole_h _ as s -> spec_of_skeleton_node s >>| fun spec -> KTree.Leaf spec
        
    | Sk.Apply_h ((_, args), _)
    | Sk.Op_h ((_, args), _) as s ->
      List.map args ~f:spec_tree_of_skeleton' |> Or_error.all >>= fun children ->
      spec_of_skeleton_node s >>| fun spec -> KTree.Node (spec, children)
        
    | s -> unexpected_skeleton_err s
  in

  spec_tree_of_skeleton' s

let rename_spec_tree t =
  let fresh_int = Util.Fresh.mk_fresh_int_fun () in
  let fresh_name () = "f" ^ (Int.to_string (fresh_int ())) in

  let rec rename =
    let ret_var = V.Free (fresh_name ()) in
    let vmap = V.Map.singleton V.Output ret_var in

    function
    | KTree.Leaf spec ->
      (* Rename the output variable of the spec to a fresh name. *)
      let renamed_spec = S.substitute_var vmap spec in

      (* Return the node with the renamed spec + the name of the output variable. *)
      (KTree.Leaf renamed_spec, ret_var)
      
    | KTree.Node (spec, children) ->
      (* Rename all children, collecting the new subtrees + the new output variables. *)
      let (renamed_children, ret_vars) = List.map children ~f:rename |> List.unzip in

      (* Create a name mapping that associates each input variable i_k
         with the output variable of the kth child. *)
      let vmap = List.foldi ret_vars ~init:vmap ~f:(fun i m rv ->
          V.Map.add m ~key:(V.Input (i + 1)) ~data:rv)
      in

      let renamed_spec = S.substitute_var vmap spec in

      (KTree.Node (renamed_spec, renamed_children), ret_var)
  in

  rename t

type location = int list * int with sexp

(** Requires: 't' is a tree of specifications. 

    Ensures: Returns a flat list of the clauses in the tree, annotated
    with their location in the tree + location in the spec and their
    sort mapping.
*)
let collect_clauses t =
  let clauses loc spec =
    List.mapi (S.clauses spec) ~f:(fun i cl -> (cl, spec.S.sorts, (loc, i)))
  in
  let rec collect loc = function
    | KTree.Leaf spec -> clauses loc spec
    | KTree.Node (spec, children) ->
      let child_clauses =
        List.mapi children ~f:(fun i ch ->
            let loc' = i :: loc in
            collect loc' ch)
        |> List.concat
      in
      (clauses loc spec) @ child_clauses
  in
  collect [0] t

let z3_id_of_expr e = Z3.AST.get_id (Z3.Expr.ast_of_expr e)

(** Requires: 'cl' is a list of clauses annotated with tree + spec
    locations.

    Ensures: Returns a list of Z3 clauses and a mapping from Z3 AST
    ids to tree + spec locations. *)
let clauses_to_z3 zctx cl =
  List.fold_left cl ~init:(Ok ([], Int.Map.empty)) ~f:(fun acc (cl, sorts, loc) ->
      acc >>= fun (z3_cls, m) ->
      T.to_z3 sorts zctx cl >>| fun z3_cl ->
      let m' = Int.Map.add m ~key:(z3_id_of_expr z3_cl) ~data:loc in
      (z3_cl :: z3_cls, m'))

let location_eq = Tuple.T2.equal ~eq1:(List.equal ~equal:Int.equal) ~eq2:Int.equal

let filter_spec_tree spec_tree locs =
  let rec filter loc = function
    | KTree.Leaf spec ->
      let clauses = List.filteri (S.clauses spec) ~f:(fun i _ ->
          List.mem ~equal:location_eq locs (loc, i))
      in
      if (clauses = []) then KTree.Leaf S.top else
        KTree.Leaf { spec with S._constraint = T.Apply ("And", clauses); }
        
    | KTree.Node (spec, children) ->
      let clauses = List.filteri (S.clauses spec) ~f:(fun i _ ->
          List.mem ~equal:location_eq locs (loc, i))
      in
      if (List.length clauses) = 0 then KTree.Leaf S.top else
        let children' = List.mapi children ~f:(fun i ch ->
            let loc' = i :: loc in
            filter loc' ch)
        in
        KTree.Node ({ spec with S._constraint = T.Apply ("And", clauses); }, children')
  in
  filter [0] spec_tree

let prune_spec_tree spec spec_tree =
  let (renamed_spec_tree, ret_var) = rename_spec_tree spec_tree in 
  let renamed_spec = S.substitute_var (V.Map.singleton V.Output ret_var) spec in
  
  (* Collect clauses from the renamed spec tree. *)
  let tree_clauses = collect_clauses renamed_spec_tree in

  (* Create a Z3 context + solver that can generate unsat cores. *)
  let cfg = ["UNSAT_CORE", "true"] in
  let zctx = Z3.mk_context cfg in
  let solver = Z3.Solver.mk_simple_solver zctx in

  (* Convert all clauses to Z3 clauses. *)
  clauses_to_z3 zctx tree_clauses >>= fun (z3_tree_clauses, id_to_loc) ->
  S.to_z3 zctx renamed_spec >>| fun z3_spec_clauses ->

  (* Add indicator booleans to all clauses and update the clause id to
     location mapping. *)
  let z3_with_boolean, z3_booleans, id_to_loc =
    List.fold_left (z3_tree_clauses @ z3_spec_clauses) ~init:([], [], id_to_loc)
      ~f:(fun (z3_cls, bs, ilm) z3_cl ->
          (* Create fresh boolean. *)
          let b = Z3.Expr.mk_fresh_const zctx "b" (Z3.Boolean.mk_sort zctx) in

          (* Create clause: b <=> cl. *)
          let z3_cl' = Z3.Boolean.mk_iff zctx b z3_cl in
          
          (* Update the id to location mapping with the id of the indicator boolean. *)
          let old_id = z3_id_of_expr z3_cl in
          let new_id = z3_id_of_expr b in
          let ilm' = match Int.Map.find ilm old_id with
            | Some loc -> Int.Map.add ilm ~key:new_id ~data:loc
            | None -> ilm
          in
          
          (z3_cl' :: z3_cls, b :: bs, ilm'))
  in

  (* Add tracked clauses and background knowledge to solver. *)
  Z3.Solver.assert_and_track_l solver z3_with_boolean z3_booleans;
  Z3.Solver.add solver [S.background zctx];

  match Z3.Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE ->
    let core = Z3.Solver.get_unsat_core solver in

    (* Select all locations that remain in the core. *)
    let core_locs = List.map core ~f:(fun b ->
        let id = Z3.AST.get_id b in
        match Int.Map.find id_to_loc id with
        | Some loc -> loc
        | None -> failwiths "BUG: Core contains a boolean with no associated location."
                    (id, id_to_loc) <:sexp_of<int * location Int.Map.t>>)
    in

    (* Filter the original spec tree to only contain clauses that
       appear in the core, and return it as a conflict. *)
    `Conflict (filter_spec_tree spec_tree core_locs)

  | Z3.Solver.UNKNOWN
  | Z3.Solver.SATISFIABLE -> `NoConflict
    
(* let of_skeleton names components s = *)
(*   let unbound_component_err func = *)
(*     error "Unbound component." func <:sexp_of<string>> *)
(*   in *)

(*   let spec_of_skeleton_node child_names = *)
(*     let ret_var = V.Free (fresh_name ()) in *)

(*     let of_apply func = *)
(*       match String.Map.find components func with *)
(*       | Some component -> *)
(*         let vmap = *)
(*           (List.mapi child_names ~f:(fun i name -> V.Input (i + 1), name)) @ [V.Output, ret_var] *)
(*           |> V.Map.of_alist_exn *)
(*         in *)
(*         let spec = S.substitute_var vmap component.spec in *)
(*         Ok (spec, ret_var) *)
(*       | None -> unbound_component_err func *)
(*     in *)
      
(*     function *)
(*     | Sk.Num_h (x, _) -> Ok { *)
(*         S._constraint = T.Apply ("Eq", [T.Variable V.Output; T.Constant (C.Int x)]); *)
(*         S.sorts = V.Map.of_alist_exn [V.Output, Sort.Int]; *)
(*       } *)

(*     | Sk.Bool_h (true, _) -> S.of_string "r where r : bool" *)
(*     | Sk.Bool_h (false, _) -> S.of_string "Not(r) where r : bool" *)

(*     | Sk.List_h (x, _) -> *)
(*       let len = List.length x in *)
(*       Ok { *)
(*         S._constraint = T.Apply ("Eq", [T.Apply ("Len", [T.Variable V.Output]); T.Constant (C.Int len)]); *)
(*         S.sorts = V.Map.of_alist_exn [ret_var, Sort.List]; *)
(*       } *)

(*     | Sk.Id_h (Sk.StaticDistance sd, _) -> *)
(*       begin match SD.Map.find names sd with *)
(*         | Some ret_var -> Ok S.top *)
(*         | None -> error "Unbound free variable." (sd, names) <:sexp_of<SD.t * V.t SD.Map.t>> *)
(*       end *)

(*     | Sk.Apply_h ((Sk.Id_h (Sk.Name func, _), _), _) -> of_apply func *)
(*     | Sk.Op_h ((op, _), _) -> of_apply (Expr.Op.to_string op) *)

(*     | Sk.Hole_h (h, _) -> *)
(*       Sort.of_type h.Hypothesis.Hole.type_ >>| fun sort -> { *)
(*         S._constraint = T.Constant (C.Bool true); *)
(*         S.sorts = V.Map.of_alist_exn [ ret_var, sort ]; *)
(*       } *)

(*     | s -> unexpected_skeleton_err s *)
(*   in *)

(*   let rec of_skeleton' = function *)
(*     | Sk.Num_h _ | Sk.Bool_h _ | Sk.Id_h _ | Sk.List_h _ | Sk.Hole_h _ as s -> *)
(*       spec_of_skeleton_node [] s >>| fun (spec, var) -> *)
(*       (KTree.Leaf spec.S.constraints, spec.S.sorts, var) *)
(*     | Sk.Apply_h ((_, args), _) | Sk.Op_h ((_, args), _) as s -> *)
(*       List.map args ~f:of_skeleton' |> Or_error.all >>= fun children -> *)
(*       let (child_trees, child_sorts, child_names) = List.unzip3 children in *)
(*       spec_of_skeleton_node child_names s >>= fun (spec, var) -> *)
(*       merge_sorts (spec.S.sorts::child_sorts) >>| fun sorts -> *)
(*       (KTree.Node (spec.S.constraints, child_trees), sorts, var) *)
(*     | s -> unexpected_skeleton_err s *)
(*   in       *)

(*   of_skeleton' s *)

(* let spec_tree_to_z3 zctx c = *)
(*   let predicate_list_to_z3 preds = *)
(*     List.map preds ~f:(fun p -> *)
(*         P.to_z3 c.sorts zctx p >>| fun z3_p -> (p, z3_p)) *)
(*     |> Or_error.all *)
(*   in *)
  
(*   let rec body_spec_to_z3 = function *)
(*     | KTree.Node (spec, children) -> *)
(*       predicate_list_to_z3 preds >>= fun preds -> *)
(*       List.map children ~f:body_spec_to_z3 |> Or_error.all *)
(*       >>| fun child_preds -> KTree.Node (preds, child_preds) *)
(*     | KTree.Leaf preds -> *)
(*       predicate_list_to_z3 preds >>| fun preds -> KTree.Leaf preds *)
(*   in *)

(*   predicate_list_to_z3 c.input_spec >>= fun input_z3 -> *)
(*   body_spec_to_z3 c.body_spec >>| fun body_z3 -> *)
(*   (input_z3, body_z3) *)

(* let of_hypothesis_unpruned components h = *)
(*   (\* Generate specifications for each of the input variables in the *)
(*      hypothesis from the input-output examples. *\) *)
(*   let m_input_specs = match H.spec h with *)
(*     | Sp.Examples exs -> S.of_examples exs *)
(*     | s -> error "Unsupported specification type." s Sp.sexp_of_t *)
(*   in *)
(*   m_input_specs >>= fun input_specs -> *)
(*   (\* Generate a mapping from the input variables in the hypothesis to *)
(*      specification input variables Input 1 ... Input n. *\) *)
(*   Or_error.try_with (fun () ->  *)
(*       SD.Map.fold input_specs ~init:(1, SD.Map.empty, [], V.Map.empty) *)
(*         ~f:(fun ~key:sd ~data:spec (i, names, preds, sorts) -> *)
(*             let var = V.Input i in *)
(*             let names = SD.Map.add names ~key:sd ~data:var in *)
(*             let spec = S.substitute_var (V.Map.of_alist_exn [V.Input 1, var]) spec in *)
(*             let preds = spec.S.constraints @ preds in *)
(*             let sorts = merge_sorts [spec.S.sorts; sorts] |> Or_error.ok_exn in *)
(*             (i + 1, names, preds, sorts))) *)
(*   >>= fun (_, names, input_spec, input_sorts) -> *)
(*   of_skeleton names components (H.skeleton h) >>= fun (body_spec, body_sorts, ret_val) -> *)
(*   merge_sorts [input_sorts; body_sorts] >>| fun sorts -> *)
(*   { *)
(*     input_spec = (P.Binary (P.Eq, T.Variable V.Output, T.Variable ret_val))::input_spec; *)
(*     body_spec; sorts;     *)
(*   } *)

(* let of_hypothesis ?(components = Component.stdlib) h = *)
(*   of_hypothesis_unpruned components h >>= prune *)
