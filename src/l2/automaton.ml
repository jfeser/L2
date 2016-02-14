open Core.Std

open Collections
open Hypothesis
open Infer
open Synthesis_common

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

  let invariants : t -> unit = fun a ->
    if not (Symbol.Set.subset a.initial_states a.states) then
      failwiths "'initial_states' is not a subset of 'states'."
        (a.initial_states, a.states) [%sexp_of:Symbol.Set.t * Symbol.Set.t];
    
    List.iter a.rules ~f:(fun rule ->
        let (q, _, qq) = rule in
        if not (Symbol.Set.mem a.states q) then
          failwiths "State in rule is not in 'states'."
            (q, rule, a.states) [%sexp_of:Symbol.t * Rule.t * Symbol.Set.t];
        List.iter qq ~f:(fun q ->
            if not (Symbol.Set.mem a.states q) then
              failwiths "State in rule is not in 'states'."
                (q, rule, a.states) [%sexp_of:Symbol.t * Rule.t * Symbol.Set.t]))

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
          else m)
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

    include T
    include Comparable.Make(T)
  end
    
  let intersect a1 a2 =
    let find_pair map pair =
      match SymbolPair.Map.find map pair with
          | Some sym -> sym
          | None -> failwiths "BUG: State pair does not have an associated symbol."
                      (pair, map) [%sexp_of:(SymbolPair.t * Symbol.t SymbolPair.Map.t)]
    in
    let (states, symbol_map) =
      List.cartesian_product (Symbol.Set.to_list a1.states) (Symbol.Set.to_list a2.states) |>
      List.fold ~init:(Symbol.Set.empty, SymbolPair.Map.empty) ~f:(fun (ss, m) (st1, st2) ->
            let sym = Symbol.create (Symbol.to_string st1 ^ ", " ^ Symbol.to_string st2) in
            let ss' = Symbol.Set.add ss sym in
            let m' = SymbolPair.Map.add m ~key:(st1, st2) ~data:sym in
            (ss', m'))
    in

    let initial_states =
      List.cartesian_product (Symbol.Set.to_list a1.initial_states) (Symbol.Set.to_list a2.initial_states)
      |> List.map ~f:(find_pair symbol_map)
      |> Symbol.Set.of_list
    in

    let components = Component.Set.union a1.components a2.components in

    let rules =
      List.cartesian_product a1.rules a2.rules |>
      List.filter_map ~f:(fun (r1, r2) ->
          match Spec.conjoin (Rule.spec r1) (Rule.spec r2) with
          | Ok spec -> 
            if Rule.arity r1 = Rule.arity r2 then
              let q = find_pair symbol_map (Rule.start_state r1, Rule.start_state r2) in
              let qq =
                List.zip_exn (Rule.end_states r1) (Rule.end_states r2)
                |> List.map ~f:(find_pair symbol_map)
              in
              Some (q, spec, qq)
            else None
          | Error _ -> None)
    in

    { states; initial_states; components; rules }

  (** Create an automaton that accepts any composition of a set of components. *)
  let mk_any : Component.Set.t -> (Symbol.t * t) = fun components ->
    let state = Symbol.create "*" in
    let initial_states = Symbol.Set.singleton state in
    let states = initial_states in
    let rules =
      Sequence.map (C.Set.to_sequence components) ~f:(fun c ->
        (state, c.Component.spec, List.repeat c.Component.arity state))
      |> Sequence.to_list
    in
    (state, { initial_states; states; rules; components; })
end

module Conflict = struct
  type t = {
    automaton : Constrained.t;
    any_state : Symbol.t;
  } [@@deriving sexp]

  let invariants : t -> unit = fun ca ->
    Constrained.invariants ca.automaton;
    if not (Symbol.Set.mem ca.automaton.Constrained.states ca.any_state) then
      failwiths "'any_state' is not in 'automaton.states'."
        (ca.any_state, ca.automaton.Constrained.states) [%sexp_of:Symbol.t * Symbol.Set.t]

  let complement : t -> t = fun ca ->
    let rules' = List.concat_map ca.automaton.Constrained.rules ~f:(fun r ->
        let negated_r = (Rule.start_state r, Spec.negate (Rule.spec r), Rule.end_states r) in
        let rs = List.map (List.diag (Rule.end_states r) ca.any_state) ~f:(fun es ->
            (Rule.start_state r, Rule.spec r, es))
        in
        negated_r :: rs)
    in
    { ca with automaton = { ca.automaton with Constrained.rules = rules' } }

  let to_constrained_automaton : t -> Constrained.t = fun ca ->
    let module CA = Constrained in
    
    (* Generate an automaton that accepts all compositions of the
       components in the input automaton. *)
    let components = ca.automaton.CA.components in
    let (any_state, any_a) = CA.mk_any components in
    let map_any q = if Symbol.equal q ca.any_state then any_state else q in

    (* Replace all references to the any state in the rules with
       references to the initial state of the any automaton. *)
    let rules =
      List.map ca.automaton.CA.rules ~f:(fun (q, spec, qq) ->
          let q' = map_any q in
          let qq' = List.map qq ~f:map_any in
          (q', spec, qq'))
    in

    let initial_states = Symbol.Set.map ~f:map_any ca.automaton.CA.initial_states in
    let states = Symbol.Set.map ~f:map_any ca.automaton.CA.states in
    let a = { CA.states; CA.initial_states; CA.rules; components; } in
    Constrained.invariants a;
    a
            

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

    let sub vmap spec =
      Or_error.tag_arg (S.substitute_var vmap spec)
        "BUG: Fresh variable collided with a variable in the spec."
        vmap [%sexp_of:V.t V.Map.t]
      |> Or_error.ok_exn
    in

    let rec rename kt =
      let ret_var = V.Free (fresh_name ()) in
      let vmap = V.Map.singleton V.Output ret_var in

      match kt with
      | KTree.Leaf spec ->
        (* Rename the output variable of the spec to a fresh name. *)
        let renamed_spec = sub vmap spec in

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

        let renamed_spec = sub vmap spec in

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

  let prune_spec_tree : Spec.t -> Spec.t KTree.t -> Spec.t KTree.t Option.t Or_error.t =
    fun spec spec_tree ->
      let module Let_syntax = Or_error.Let_syntax in

      let (renamed_spec_tree, ret_var) = rename_spec_tree spec_tree in 
      let%bind renamed_spec = S.substitute_var (V.Map.singleton V.Output ret_var) spec in

      (* Collect clauses from the renamed spec tree. *)
      let tree_clauses = collect_clauses renamed_spec_tree in

      (* Create a Z3 context + solver that can generate unsat cores. *)
      let cfg = ["UNSAT_CORE", "true"] in
      let zctx = Z3.mk_context cfg in
      let solver = Z3.Solver.mk_simple_solver zctx in

      (* Convert all clauses to Z3 clauses. *)
      let%bind (z3_tree_clauses, id_to_loc) = clauses_to_z3 zctx tree_clauses in
      let%map z3_spec_clauses = S.to_z3 zctx renamed_spec in

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

        (* Select all locations that remain in the core. Note that not
           all booleans have an associated location, because some come from
           the spec, not the spec tree. *)
        let core_locs = List.filter_map core ~f:(fun b ->
            let id = Z3.AST.get_id (Z3.Expr.ast_of_expr b) in
            Int.Map.find id_to_loc id)
        in

        (* Filter the original spec tree to only contain clauses that
           appear in the core, and return it as a conflict. *)
        Some (filter_spec_tree spec_tree core_locs)

      | Z3.Solver.UNKNOWN
      | Z3.Solver.SATISFIABLE -> None

  (** Generates a conflict automaton from a tree of specifications. *)
  let of_spec_tree : Z3.context -> Component.Set.t -> Spec.t KTree.t -> t Or_error.t =
    fun zctx components spec_tree ->
      let module Let_syntax = Or_error.Let_syntax in
      let fresh_state =
        let fresh_int = Util.Fresh.mk_fresh_int_fun () in
        fun () -> Symbol.create ("q" ^ Int.to_string (fresh_int ()))
      in
      let any = Symbol.create "*" in
      let any_set = Symbol.Set.singleton any in

      let rec of_spec_tree' = function
        (* At the leaves, if the transition spec is valid, then
           transition from the parent to the any state. Otherwise,
           generate a new state for this leaf and a terminal rule that
           starts at the new state. *)
        | KTree.Leaf spec -> begin
            match%map Spec.is_valid zctx spec with
            | true -> ([], any, any_set)
            | false ->
              let sym = fresh_state () in
              ([sym, spec, []], sym, Symbol.Set.singleton sym)
          end

        (* At the nodes, if the transition spec is valid, then
           transition from the parent to the any state. Otherwise,
           recursively process the children and generate a transition
           to their returned states. *)
        | KTree.Node (spec, children) -> begin
            match%bind Spec.is_valid zctx spec with
            | true -> Ok ([], any, any_set)
            | false ->
              let%map child_ret = List.map children ~f:of_spec_tree' |> Or_error.all in
              let child_rules, child_states, child_state_sets = List.unzip3 child_ret in
              let sym = fresh_state () in
              [sym, spec, child_states] @ List.concat child_rules,
              sym,
              Symbol.Set.union_list (Symbol.Set.singleton sym :: child_state_sets)
          end
      in
      let%map (rules, initial_state, states) = of_spec_tree' spec_tree in
      let module CA = Constrained in
      {
        any_state = any;
        automaton = {
          CA.components = components;
          CA.rules = rules;
          CA.initial_states = Symbol.Set.singleton initial_state;
          CA.states = states;
        }
      }

  let of_skeleton zctx components sk spec =
    let module Let_syntax = Or_error.Let_syntax in
    let spec_map =
      Component.Set.to_list components
      |> List.map ~f:(fun c -> (c.Component.name, c.Component.spec))
      |> String.Map.of_alist_exn
    in
    let%bind spec_tree = spec_tree_of_skeleton spec_map sk in

    match%bind prune_spec_tree spec spec_tree with
    | Some conflict_tree ->
      let%map conflict_automaton = of_spec_tree zctx components conflict_tree in
      Some conflict_automaton
    | None -> Ok None
end

module Synthesizer = struct
  exception SynthesisException of Hypothesis.t

  let synthesize : max_cost:int -> Component.Set.t -> Spec.t -> Hypothesis.t Option.t Or_error.t =
    let module Let_syntax = Or_error.Let_syntax in
    fun ~max_cost components spec ->
      (* TODO: Should use our own cost model here. *)
      let cost_model = V2_engine.cost_model in
      let zctx = Z3.mk_context [] in
      let space = Constrained.mk_any components |> Tuple.T2.get2 in
      
      let rec search_in_space space =
        let gen = Constrained.to_generalizer zctx space cost_model |> Or_error.ok_exn in
        let memo = Memoizer.create gen cost_model in

        (* TODO: Should use all initial states. *)
        let hole =
          Hole.create (Type.list (Type.free 1 1)) (Symbol.Set.choose_exn space.Constrained.initial_states)
        in
        
        let rec search_at_cost : int -> unit = fun cost ->
          if cost > max_cost then () else
            let candidates = Memoizer.get memo hole Specification.Top ~cost in
            List.iter candidates ~f:(fun (candidate, _) ->
                let m_conflict =
                  Conflict.of_skeleton zctx components (Hypothesis.skeleton candidate) spec
                  |> Or_error.ok_exn
                in
                match m_conflict with
                | Some conflict ->
                  print_endline "Found conflict!";
                  print_endline (Sexp.to_string_hum ([%sexp_of:Hypothesis.t] candidate));
                  print_endline (Sexp.to_string_hum ([%sexp_of:Conflict.t] conflict));
                  print_newline ();
                  let space' = Constrained.intersect (Conflict.to_constrained_automaton conflict) space in
                  print_endline "New space:";
                  print_endline (Sexp.to_string_hum ([%sexp_of:Constrained.t] space'))
                | None -> raise (SynthesisException candidate));

            search_at_cost (cost + 1)
        in

        search_at_cost 0
      in

      Or_error.try_with (fun () ->
          try search_in_space space; None with
          | SynthesisException ret -> Some ret)
end
