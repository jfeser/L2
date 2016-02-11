open Core.Std

open Collections
open Hypothesis
open Infer

module Spec = Component.Specification

module Rule = struct
  type t = Symbol.t * Spec.t * (Symbol.t list) [@@deriving sexp, compare]

  let start_state (q, _, _) = q
  let spec (_, s, _) = s
  let end_states (_, _, qq) = qq

  let arity r = List.length (end_states r)
  let is_terminal r = arity r = 0
end

module Constrained = struct
  module C = Component
    
  type t = {
    states : Symbol.Set.t;
    initial_states : Symbol.Set.t;
    components : C.Set.t;
    rules : Rule.t list;
  } [@@deriving sexp, compare]

  let equal a1 a2 = (compare a1 a2 = 0)
  let to_string a = Sexp.to_string_hum (sexp_of_t a)

  let create states initial_states components rules =
    if not (Set.subset initial_states states) then
      failwiths "Initial states not a subset of states."
        (states, initial_states) [%sexp_of:String.Set.t * String.Set.t]
    else
      let (states, symbol_map) = String.Set.fold states
          ~init:(Symbol.Set.empty, String.Map.empty) ~f:(fun (ss, m) st ->
              let sym = Symbol.create st in
              let ss' = Symbol.Set.add ss sym in
              let m' = String.Map.add m ~key:st ~data:sym in
              (ss', m'))
      in
      {
        states;
        initial_states =
          Set.map ~comparator:Symbol.comparator initial_states ~f:(fun st ->
              String.Map.find_exn symbol_map st);
        components;
        rules = List.map rules ~f:(fun (q, spec, qq) ->
            let q' = String.Map.find_exn symbol_map q in
            let qq' = List.map qq ~f:(fun q -> String.Map.find_exn symbol_map q) in
            (q', spec, qq'));
      }

  let reduce zctx a =
    let any_component_fits spec =
      let rec any_fits errs = function
        | [] -> if List.length errs > 0 then Error (Error.of_list errs) else Ok false
        | c::cs -> begin match Spec.entails zctx c.C.spec spec with
            | Ok true -> Ok true
            | Ok false -> any_fits errs cs
            | Error err -> any_fits (err::errs) cs
          end
      in
      any_fits [] (Set.to_list a.components) |> Or_error.ok_exn
    in

    let rec fix m =
      let m' =
        List.fold_left a.rules ~init:m ~f:(fun m' r ->
            if List.for_all (Rule.end_states r) ~f:(Set.mem m') && any_component_fits (Rule.spec r)
            then Set.add m' (Rule.start_state r)
            else m')
      in
      if Set.equal m m' then m' else fix m'
    in
    
    let m =
      List.fold_left a.rules ~init:Symbol.Set.empty ~f:(fun m r ->
          if Rule.is_terminal r && any_component_fits (Rule.spec r)
          then Set.add m (Rule.start_state r)
          else m
        )
    in

    Or_error.try_with (fun () ->
        let m = fix m in
        {
          a with
          states = m;
          initial_states = Set.inter a.initial_states m;
          rules = List.filter a.rules ~f:(fun r ->
              Set.mem m (Rule.start_state r) &&
              List.for_all (Rule.end_states r) ~f:(Set.mem m));
        })

  let is_empty zctx a =
    let open Or_error.Monad_infix in
    reduce zctx a >>| fun a' -> (Set.is_empty a'.initial_states, a')
  
  let generalize rules matching_components cost_model hole spec =
    let module H = Hypothesis in
    let module Sp = Specification in
    let open Option.Monad_infix in

    let cm = cost_model in
    
    (* Select all rules which match the hole symbol. *)
    List.filter rules ~f:(fun r -> Symbol.equal hole.Hole.symbol (Rule.start_state r)) |> 

    (* For each matching rule, select each matching component and expand. *)
    List.map ~f:(fun r ->
        let components =
          Spec.Map.find matching_components (Rule.spec r)
          |> Option.value ~default:[]
          |> List.filter ~f:(fun c -> Int.equal c.C.arity (Rule.arity r))
        in

        (* print_endline (Sexp.to_string_hum ([%sexp_of:Component.t list] components)); *)
        List.filter_map components ~f:(fun c ->
            match instantiate 0 c.C.type_ with
            | Type.Arrow_t (args_t, ret_t) ->
              (* Try to unify the return type of the operator with the type of the hole. *)
              (Unifier.of_types hole.Hole.type_ ret_t) >>| fun u ->

              (* If unification succeeds, apply the unifier to the rest of the type. *)
              let args_t = List.map args_t ~f:(Unifier.apply u) in
              let arg_holes = List.map2_exn args_t (Rule.end_states r) ~f:(fun t sym ->
                  H.hole cm (Hole.create ~ctx:hole.Hole.ctx t sym) Sp.Top)
              in
              (H.apply cm (H.id_name cm c.C.name Sp.Top) arg_holes spec, u)
            | type_ ->
              Unifier.of_types hole.Hole.type_ type_ >>| fun u ->
              (H.id_name cm c.C.name Sp.Top, u)))
    |> List.concat_no_order

  let to_generalizer zctx a cost_model =
    let open Or_error.Monad_infix in

    let specs =
      List.map a.rules ~f:(Rule.spec)
      |> List.dedup ~compare:Spec.compare
    in

    let component_list = C.Set.to_list a.components in

    (* Create a mapping from specifications to matching components. *)    
    List.map specs ~f:(fun spec ->
        List.filter_map component_list ~f:(fun c ->
            match Spec.entails zctx c.C.spec spec with
            | Ok true -> Some (Ok c)
            | Ok false -> None
            | Error err -> Some (Error err))
        |> Or_error.all
        >>| fun matches -> (spec, matches))
    |> Or_error.all
    >>| fun alist ->
    let matching_components = Spec.Map.of_alist_exn alist in
    generalize a.rules matching_components cost_model

  module SymbolPair = struct
    module T = struct
      type t = Symbol.t * Symbol.t [@@deriving compare, sexp]
    end

    include Comparable.Make(T)
  end
    
  let intersect a1 a2 =
    let (states, symbol_map) =
      List.cartesian_product (Symbol.Set.to_list a1.states) (Symbol.Set.to_list a2.states) |>
      List.fold ~init:(Symbol.Set.empty, SymbolPair.Map.empty) ~f:(fun (ss, m) (st1, st2) ->
            let sym = Symbol.create ("(" ^ Symbol.to_string st1 ^ ", " ^ Symbol.to_string st2 ^ ")") in
            let ss' = Symbol.Set.add ss sym in
            let m' = SymbolPair.Map.add m ~key:(st1, st2) ~data:sym in
            (ss', m'))
    in

    let initial_states =
      List.cartesian_product (Symbol.Set.to_list a1.initial_states) (Symbol.Set.to_list a2.initial_states)
      |> List.map ~f:(fun st -> SymbolPair.Map.find_exn symbol_map st)
      |> Symbol.Set.of_list
    in

    let components = Component.Set.union a1.components a2.components in

    let rules =
      List.cartesian_product a1.rules a2.rules |>
      List.filter_map ~f:(fun (r1, r2) ->
          match Spec.conjoin (Rule.spec r1) (Rule.spec r2) with
          | Ok spec -> 
            if Rule.arity r1 = Rule.arity r2 then
              let q = SymbolPair.Map.find_exn symbol_map (Rule.start_state r1, Rule.start_state r1) in
              let qq = List.map2_exn (Rule.end_states r1) (Rule.end_states r2) ~f:(fun q1 q2 ->
                  SymbolPair.Map.find_exn symbol_map (q1, q2))
              in
              Some (q, spec, qq)
            else None
          | Error _ -> None)
    in

    { states; initial_states; components; rules }
end

module Conflict = struct
  type t = {
    automaton : Constrained.t;
    any_state : Symbol.t;
  }

  let complement ca =
    let rules' = List.concat_map ca.automaton.Constrained.rules ~f:(fun r ->
        let negated_r = (Rule.start_state r, Spec.negate (Rule.spec r), Rule.end_states r) in
        let rs = List.map (List.diag (Rule.end_states r) ca.any_state) ~f:(fun es ->
            (Rule.start_state r, Rule.spec r, es))
        in
        negated_r :: rs)
    in
    { ca with automaton = { ca.automaton with Constrained.rules = rules' } }

  module T = Component.Term
  module C = Component.Constant
  module V = Component.Variable
  module S = Component.Specification
  module Sort = Component.Sort

  module H = Hypothesis
  module SD = StaticDistance
  module Sk = Skeleton
  module Sp = Specification

  (** Requires: 'components' is a mapping from strings to
      components. 's' is a skeleton which is a composition of functions,
      variables, and constants.

      Ensures: The returned tree contains a node for each node in the
      input tree. The nodes in the output tree are over-approximate
      specifications of the nodes in the input tree.
  *)
  let spec_tree_of_skeleton (components : S.t String.Map.t) s : S.t KTree.t Or_error.t =
    let unexpected_skeleton_err s =
      error "Unexpected skeleton type." s [%sexp_of:Sp.t Sk.t]
    in

    let lookup_component name =
      match String.Map.find components name with
      | Some spec -> Ok spec
      | None -> error "No specification for component." name [%sexp_of:string]
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

    let rec spec_tree_of_skeleton' =
      let open Or_error.Monad_infix in
      function
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

  type location = int list * int [@@deriving sexp]

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
    let open Or_error.Monad_infix in
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
    let open Or_error.Monad_infix in

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
          let id = Z3.AST.get_id (Z3.Expr.ast_of_expr b) in
          match Int.Map.find id_to_loc id with
          | Some loc -> loc
          | None -> failwiths "BUG: Core contains a boolean with no associated location."
                      (id, id_to_loc) [%sexp_of:int * location Int.Map.t])
      in

      (* Filter the original spec tree to only contain clauses that
         appear in the core, and return it as a conflict. *)
      Some (filter_spec_tree spec_tree core_locs)

    | Z3.Solver.UNKNOWN
    | Z3.Solver.SATISFIABLE -> None

  let of_skeleton components sk spec =
    let module Let_syntax = Or_error.Let_syntax in
    let%map spec_tree = spec_tree_of_skeleton components sk in
    let%map conflict_tree = prune_spec_tree spec spec_tree in
end
