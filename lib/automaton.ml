open Core
open Collections
open Hypothesis
open Infer
open Synthesis_common
module Spec = Component.Specification

module Rule = struct
  type t = Symbol.t * Spec.t * Symbol.t list [@@deriving sexp, compare]

  let start_state (q, _, _) = q

  let spec (_, s, _) = s

  let end_states (_, _, qq) = qq

  let arity r = List.length (end_states r)

  let is_terminal r = arity r = 0
end

let mk_fresh_state : unit -> unit -> Symbol.t =
 fun () ->
  let fresh_int = Util.Fresh.mk_fresh_int_fun () in
  fun () -> Symbol.create ("q" ^ Int.to_string (fresh_int ()))

module Constrained = struct
  module C = Component

  type t =
    { states: Symbol.Set.t
    ; initial_states: Symbol.Set.t
    ; components: C.Set.t
    ; rules: Rule.t list }
  [@@deriving sexp, compare]

  let equal a1 a2 = compare a1 a2 = 0

  let to_string a = Sexp.to_string_hum (sexp_of_t a)

  let invariants : t -> unit =
   fun a ->
    if not (Symbol.Set.subset a.initial_states a.states) then
      failwiths "'initial_states' is not a subset of 'states'."
        (a.initial_states, a.states) [%sexp_of: Symbol.Set.t * Symbol.Set.t] ;
    List.iter a.rules ~f:(fun rule ->
        let q, _, qq = rule in
        if not (Symbol.Set.mem a.states q) then
          failwiths "State in rule is not in 'states'." (q, rule, a.states)
            [%sexp_of: Symbol.t * Rule.t * Symbol.Set.t] ;
        List.iter qq ~f:(fun q ->
            if not (Symbol.Set.mem a.states q) then
              failwiths "State in rule is not in 'states'." (q, rule, a.states)
                [%sexp_of: Symbol.t * Rule.t * Symbol.Set.t] ) )

  let create states initial_states components rules =
    if not (Set.subset initial_states states) then
      failwiths "Initial states not a subset of states." (states, initial_states)
        [%sexp_of: String.Set.t * String.Set.t]
    else
      let states, symbol_map =
        String.Set.fold states ~init:(Symbol.Set.empty, String.Map.empty)
          ~f:(fun (ss, m) st ->
            let sym = Symbol.create st in
            let ss' = Symbol.Set.add ss sym in
            let m' = String.Map.add m ~key:st ~data:sym in
            (ss', m') )
      in
      { states
      ; initial_states=
          Set.map ~comparator:Symbol.comparator initial_states ~f:(fun st ->
              String.Map.find_exn symbol_map st )
      ; components
      ; rules=
          List.map rules ~f:(fun (q, spec, qq) ->
              let q' = String.Map.find_exn symbol_map q in
              let qq' =
                List.map qq ~f:(fun q -> String.Map.find_exn symbol_map q)
              in
              (q', spec, qq') ) }

  let reduce zctx a =
    let any_component_fits spec =
      let rec any_fits errs = function
        | [] ->
            if List.length errs > 0 then Error (Error.of_list errs) else Ok false
        | c :: cs -> (
          match Spec.entails zctx c.C.spec spec with
          | Ok true -> Ok true
          | Ok false -> any_fits errs cs
          | Error err -> any_fits (err :: errs) cs )
      in
      any_fits [] (Set.to_list a.components) |> Or_error.ok_exn
    in
    (* Find the fixed point of f applied to s. *)
    let rec fix ~cmp x f =
      let x' = f x in
      if cmp x x' = 0 then x else fix ~cmp x' f
    in
    (* Collect the set of reachable states from a set of initial states going top-down. *)
    let top_down (a, m) =
      let m' =
        List.fold a.rules ~init:m ~f:(fun m' (q, spec, qq) ->
            if Symbol.Set.mem m' q && any_component_fits spec then
              List.fold qq ~init:m' ~f:Symbol.Set.add
            else m' )
      in
      (a, m')
    in
    (* Collect the set of reachable states from a set of initial states going bottom-up. *)
    let rec bottom_up (a, m) =
      let m' =
        List.fold a.rules ~init:m ~f:(fun m' (q, spec, qq) ->
            if List.for_all qq ~f:(Symbol.Set.mem m') && any_component_fits spec
            then Symbol.Set.add m' q
            else m' )
      in
      (a, m')
    in
    Or_error.try_with (fun () ->
        let cmp (_, m1) (_, m2) = Symbol.Set.compare m1 m2 in
        let _, reachable = fix ~cmp (a, a.initial_states) top_down in
        let a' =
          { a with
            states= reachable
          ; rules=
              List.filter a.rules ~f:(fun (q, _, qq) ->
                  Symbol.Set.mem reachable q
                  && List.for_all qq ~f:(Symbol.Set.mem reachable) ) }
        in
        let _, reachable = fix ~cmp (a', Symbol.Set.empty) bottom_up in
        { a' with
          initial_states= Set.inter a'.initial_states reachable
        ; states= reachable
        ; rules=
            List.filter a.rules ~f:(fun (q, _, qq) ->
                Symbol.Set.mem reachable q
                && List.for_all qq ~f:(Symbol.Set.mem reachable) ) } )

  let is_empty zctx a =
    let open Or_error.Monad_infix in
    reduce zctx a >>| fun a' -> (Set.is_empty a'.initial_states, a')

  let generalize rules matching_components cost_model ctx type_ symbol spec =
    let module H = Hypothesis in
    let module Sp = Specification in
    let open Option.Monad_infix in
    let cm = cost_model in
    (* Select all rules which match the hole symbol. *)
    List.filter rules ~f:(fun r -> Symbol.equal symbol (Rule.start_state r))
    |> (* For each matching rule, select each matching component and expand. *)
       List.map ~f:(fun r ->
           let components =
             Spec.Map.find matching_components (Rule.spec r)
             |> Option.value ~default:[]
             |> List.filter ~f:(fun c -> Int.equal c.C.arity (Rule.arity r))
           in
           List.filter_map components ~f:(fun c ->
               match instantiate 0 c.C.type_ with
               | Type.Arrow_t (args_t, ret_t) ->
                   (* Try to unify the return type of the operator with the type of the hole. *)
                   Unifier.of_types type_ ret_t
                   >>| fun u ->
                   (* If unification succeeds, apply the unifier to the rest of the type. *)
                   let args_t = List.map args_t ~f:(Unifier.apply u) in
                   let arg_holes =
                     List.map2_exn args_t (Rule.end_states r) ~f:(fun t sym ->
                         H.hole cm (Hole.create ~ctx t sym) Sp.top )
                   in
                   (H.apply cm (H.id_name cm c.C.name Sp.top) arg_holes spec, u)
               | type_ ->
                   Unifier.of_types type_ type_
                   >>| fun u -> (H.id_name cm c.C.name Sp.top, u) ) )
    |> List.concat_no_order

  let to_generalizer zctx a cost_model =
    let open Or_error.Monad_infix in
    let specs = List.map a.rules ~f:Rule.spec |> List.dedup ~compare:Spec.compare in
    let component_list = C.Set.to_list a.components in
    (* Create a mapping from specifications to matching components. *)
    List.map specs ~f:(fun spec ->
        List.filter_map component_list ~f:(fun c ->
            match Spec.entails zctx c.C.spec spec with
            | Ok true -> Some (Ok c)
            | Ok false -> None
            | Error err -> Some (Error err) )
        |> Or_error.all
        >>| fun matches -> (spec, matches) )
    |> Or_error.all
    >>| fun alist ->
    let matching_components = Spec.Map.of_alist_exn alist in
    generalize a.rules matching_components cost_model

  module SymbolPair = struct
    module T = struct
      type t = Symbol.t * Symbol.t [@@deriving compare, sexp]
    end

    include T
    include Comparable.Make (T)
  end

  let intersect a1 a2 =
    let find_pair map pair =
      match SymbolPair.Map.find map pair with
      | Some sym -> sym
      | None ->
          failwiths "BUG: State pair does not have an associated symbol."
            (pair, map) [%sexp_of: SymbolPair.t * Symbol.t SymbolPair.Map.t]
    in
    let fresh_state = mk_fresh_state () in
    let states, symbol_map =
      List.cartesian_product
        (Symbol.Set.to_list a1.states)
        (Symbol.Set.to_list a2.states)
      |> List.fold ~init:(Symbol.Set.empty, SymbolPair.Map.empty)
           ~f:(fun (ss, m) (st1, st2) ->
             let sym = fresh_state () in
             let ss' = Symbol.Set.add ss sym in
             let m' = SymbolPair.Map.add m ~key:(st1, st2) ~data:sym in
             (ss', m') )
    in
    let initial_states =
      List.cartesian_product
        (Symbol.Set.to_list a1.initial_states)
        (Symbol.Set.to_list a2.initial_states)
      |> List.map ~f:(find_pair symbol_map)
      |> Symbol.Set.of_list
    in
    let components = Component.Set.union a1.components a2.components in
    let rules =
      List.cartesian_product a1.rules a2.rules
      |> List.filter ~f:(fun (r1, r2) -> Rule.arity r1 = Rule.arity r2)
      |> List.filter_map ~f:(fun (r1, r2) ->
             match Spec.conjoin (Rule.spec r1) (Rule.spec r2) with
             | Ok spec ->
                 if Rule.arity r1 = Rule.arity r2 then
                   let q =
                     find_pair symbol_map (Rule.start_state r1, Rule.start_state r2)
                   in
                   let qq =
                     List.zip_exn (Rule.end_states r1) (Rule.end_states r2)
                     |> List.map ~f:(find_pair symbol_map)
                   in
                   Some (q, spec, qq)
                 else None
             | Error _ -> None )
    in
    {states; initial_states; components; rules}

  (** Create an automaton that accepts any composition of a set of components. *)
  let mk_any : Component.Set.t -> Symbol.t * t =
   fun components ->
    let state = Symbol.create "*" in
    let initial_states = Symbol.Set.singleton state in
    let states = initial_states in
    let rules =
      Set.map components ~comparator:Int.comparator ~f:(fun c -> c.Component.arity)
      |> Int.Set.to_list
      |> List.map ~f:(fun arity -> (state, Spec.top, List.repeat arity state))
    in
    (state, {initial_states; states; rules; components})
end

module Conflict = struct
  type t = {automaton: Constrained.t; any_state: Symbol.t} [@@deriving sexp]

  let invariants : t -> unit =
   fun ca ->
    Constrained.invariants ca.automaton ;
    if not (Symbol.Set.mem ca.automaton.Constrained.states ca.any_state) then
      failwiths "'any_state' is not in 'automaton.states'."
        (ca.any_state, ca.automaton.Constrained.states)
        [%sexp_of: Symbol.t * Symbol.Set.t]

  let complement : t -> t =
   fun ca ->
    let distinct_arities =
      Set.map ca.automaton.Constrained.components ~comparator:Int.comparator
        ~f:(fun c -> c.Component.arity )
    in
    let rules' =
      List.concat_map ca.automaton.Constrained.rules ~f:(fun r ->
          let q, spec, qq = r in
          let arity = Rule.arity r in
          (* q -> ~spec -> (@, ..., @) *)
          let negated_r = (q, Spec.negate spec, List.repeat arity ca.any_state) in
          (* q -> T -> (q0, ..., qn) where n != arity and there exists a
           component with arity n. *)
          let other_arity_rs =
            Int.Set.remove distinct_arities arity
            |> Int.Set.to_list
            |> List.map ~f:(fun a -> (q, Spec.top, List.repeat a ca.any_state))
          in
          (* q -> spec -> (q0, @, ..., @), ... q -> spec -> (@, ..., @, qn) *)
          let other_deviation_rs =
            List.filter_mapi qq ~f:(fun i q' ->
                if Symbol.equal q' ca.any_state then None
                else
                  let qq' =
                    List.repeat i ca.any_state
                    @ (q' :: List.repeat (arity - i - 1) ca.any_state)
                  in
                  Some (q, spec, qq') )
          in
          (negated_r :: other_arity_rs) @ other_deviation_rs )
    in
    {ca with automaton= {ca.automaton with Constrained.rules= rules'}}

  let to_constrained_automaton : t -> Constrained.t =
   fun ca ->
    let module CA = Constrained in
    (* Generate an automaton that accepts all compositions of the
       components in the input automaton. *)
    let components = ca.automaton.CA.components in
    let any_state, any_a = CA.mk_any components in
    let map_any q = if Symbol.equal q ca.any_state then any_state else q in
    (* Replace all references to the any state in the rules with
       references to the initial state of the any automaton. *)
    let rules =
      List.map ca.automaton.CA.rules ~f:(fun (q, spec, qq) ->
          let q' = map_any q in
          let qq' = List.map qq ~f:map_any in
          (q', spec, qq') )
      @ any_a.CA.rules
    in
    let initial_states = Symbol.Set.map ~f:map_any ca.automaton.CA.initial_states in
    let states =
      Symbol.Set.map ~f:map_any ca.automaton.CA.states
      |> Symbol.Set.union any_a.CA.states
    in
    let a = {CA.states; CA.initial_states; CA.rules; components} in
    Constrained.invariants a ; a

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
  let spec_tree_of_skeleton (components : S.t String.Map.t) s :
      S.t KTree.t Or_error.t =
    let unexpected_skeleton_err s =
      error "Unexpected skeleton type." s [%sexp_of: Sp.t Sk.t]
    in
    let lookup_component name =
      match String.Map.find components name with
      | Some spec -> Ok spec
      | None -> error "No specification for component." name [%sexp_of: string]
    in
    let spec_of_skeleton_node = function
      | Sk.Num_h (x, _) ->
          Ok
            { S._constraint=
                T.Apply ("Eq", [T.Variable V.Output; T.Constant (C.Int x)])
            ; S.sorts= V.Map.singleton V.Output Sort.Int }
      | Sk.Bool_h (true, _) -> S.of_string "r where r : bool"
      | Sk.Bool_h (false, _) -> S.of_string "Not(r) where r : bool"
      | Sk.List_h (x, _) ->
          let len = List.length x in
          Ok
            { S._constraint=
                T.Apply
                  ( "Eq"
                  , [T.Apply ("Len", [T.Variable V.Output]); T.Constant (C.Int len)]
                  )
            ; S.sorts= V.Map.singleton V.Output Sort.List }
      | Sk.Id_h (Sk.Id.Name name, _)
       |Sk.Apply_h ((Sk.Id_h (Sk.Id.Name name, _), _), _) ->
          lookup_component name
      | Sk.Op_h ((op, _), _) -> lookup_component (Expr.Op.to_string op)
      | Sk.Hole_h (h, _) -> Ok S.top
      | s -> unexpected_skeleton_err s
    in
    let rec spec_tree_of_skeleton' =
      let open Or_error.Monad_infix in
      function
      | (Sk.Num_h _ | Sk.Bool_h _ | Sk.Id_h _ | Sk.List_h _ | Sk.Hole_h _) as s ->
          spec_of_skeleton_node s >>| fun spec -> KTree.Leaf spec
      | (Sk.Apply_h ((_, args), _) | Sk.Op_h ((_, args), _)) as s ->
          List.map args ~f:spec_tree_of_skeleton'
          |> Or_error.all
          >>= fun children ->
          spec_of_skeleton_node s >>| fun spec -> KTree.Node (spec, children)
      | s -> unexpected_skeleton_err s
    in
    spec_tree_of_skeleton' s

  let rename_spec_tree t =
    let fresh_int = Util.Fresh.mk_fresh_int_fun () in
    let fresh_name () = "f" ^ Int.to_string (fresh_int ()) in
    let sub vmap spec =
      Or_error.tag_arg (S.substitute_var vmap spec)
        "BUG: Fresh variable collided with a variable in the spec." vmap
        [%sexp_of: V.t V.Map.t]
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
          let renamed_children, ret_vars =
            List.map children ~f:rename |> List.unzip
          in
          (* Create a name mapping that associates each input variable i_k
           with the output variable of the kth child. *)
          let vmap =
            List.foldi ret_vars ~init:vmap ~f:(fun i m rv ->
                V.Map.add m ~key:(V.Input (i + 1)) ~data:rv )
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
                collect loc' ch )
            |> List.concat
          in
          clauses loc spec @ child_clauses
    in
    collect [0] t

  let z3_id_of_expr e = Z3.AST.get_id (Z3.Expr.ast_of_expr e)

  (** Requires: 'cl' is a list of clauses annotated with tree + spec
      locations.

      Ensures: Returns a list of Z3 clauses and a mapping from Z3 AST
      ids to tree + spec locations. *)
  let clauses_to_z3 zctx cl =
    let open Or_error.Monad_infix in
    List.fold_left cl
      ~init:(Ok ([], Int.Map.empty))
      ~f:(fun acc (cl, sorts, loc) ->
        acc
        >>= fun (z3_cls, m) ->
        T.to_z3 sorts zctx cl
        >>| fun z3_cl ->
        let m' = Int.Map.add m ~key:(z3_id_of_expr z3_cl) ~data:loc in
        (z3_cl :: z3_cls, m') )

  let location_eq = Tuple.T2.equal ~eq1:(List.equal ~equal:Int.equal) ~eq2:Int.equal

  let filter_spec_tree spec_tree locs =
    let spec_of_clauses spec = function
      | [] -> S.top
      | [clause] -> {spec with S._constraint= clause}
      | clauses -> {spec with S._constraint= T.Apply ("And", clauses)}
    in
    let rec filter loc = function
      | KTree.Leaf spec ->
          let clauses =
            List.filteri (S.clauses spec) ~f:(fun i _ ->
                List.mem ~equal:location_eq locs (loc, i) )
          in
          KTree.Leaf (spec_of_clauses spec clauses)
      | KTree.Node (spec, children) ->
          let clauses =
            List.filteri (S.clauses spec) ~f:(fun i _ ->
                List.mem ~equal:location_eq locs (loc, i) )
          in
          if List.length clauses = 0 then KTree.Leaf S.top
          else
            let children' =
              List.mapi children ~f:(fun i ch ->
                  let loc' = i :: loc in
                  filter loc' ch )
            in
            KTree.Node (spec_of_clauses spec clauses, children')
    in
    filter [0] spec_tree

  let prune_spec_tree :
      Spec.t -> Spec.t KTree.t -> Spec.t KTree.t Option.t Or_error.t =
   fun spec spec_tree ->
    let module Let_syntax = Or_error.Let_syntax.Let_syntax in
    let renamed_spec_tree, ret_var = rename_spec_tree spec_tree in
    let%bind renamed_spec =
      S.substitute_var (V.Map.singleton V.Output ret_var) spec
    in
    (* Collect clauses from the renamed spec tree. *)
    let tree_clauses = collect_clauses renamed_spec_tree in
    (* Create a Z3 context + solver that can generate unsat cores. *)
    let cfg = [("UNSAT_CORE", "true")] in
    let zctx = Z3.mk_context cfg in
    let solver = Z3.Solver.mk_simple_solver zctx in
    (* Convert all clauses to Z3 clauses. *)
    let%bind z3_tree_clauses, id_to_loc = clauses_to_z3 zctx tree_clauses in
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
          let ilm' =
            match Int.Map.find ilm old_id with
            | Some loc -> Int.Map.add ilm ~key:new_id ~data:loc
            | None -> ilm
          in
          (z3_cl' :: z3_cls, b :: bs, ilm') )
    in
    (* Add tracked clauses and background knowledge to solver. *)
    Z3.Solver.assert_and_track_l solver z3_with_boolean z3_booleans ;
    Z3.Solver.add solver [S.background zctx] ;
    match Z3.Solver.check solver [] with
    | Z3.Solver.UNSATISFIABLE ->
        let core = Z3.Solver.get_unsat_core solver in
        (* Select all locations that remain in the core. Note that not
           all booleans have an associated location, because some come from
           the spec, not the spec tree. *)
        let core_locs =
          List.filter_map core ~f:(fun b ->
              let id = Z3.AST.get_id (Z3.Expr.ast_of_expr b) in
              Int.Map.find id_to_loc id )
        in
        (* Filter the original spec tree to only contain clauses that
           appear in the core, and return it as a conflict. *)
        Some (filter_spec_tree spec_tree core_locs)
    | Z3.Solver.UNKNOWN | Z3.Solver.SATISFIABLE -> None

  (** Generates a conflict automaton from a tree of specifications. *)
  let of_spec_tree : Z3.context -> Component.Set.t -> Spec.t KTree.t -> t Or_error.t
      =
   fun zctx components spec_tree ->
    let module Let_syntax = Or_error.Let_syntax.Let_syntax in
    let fresh_state = mk_fresh_state () in
    let any = Symbol.create "*" in
    let rec of_spec_tree' = function
      (* At the leaves, if the transition spec is valid, then
           transition from the parent to the any state. Otherwise,
           generate a new state for this leaf and a terminal rule that
           starts at the new state. *)
      | KTree.Leaf spec -> (
          match%map Spec.is_valid zctx spec with
          | true -> ([], any, Symbol.Set.empty)
          | false ->
              let sym = fresh_state () in
              ([(sym, spec, [])], sym, Symbol.Set.singleton sym) )
      (* At the nodes, if the transition spec is valid, then
           transition from the parent to the any state. Otherwise,
           recursively process the children and generate a transition
           to their returned states. *)
      | KTree.Node (spec, children) -> (
          match%bind Spec.is_valid zctx spec with
          | true -> Ok ([], any, Symbol.Set.empty)
          | false ->
              let%map child_ret =
                List.map children ~f:of_spec_tree' |> Or_error.all
              in
              let child_rules, child_states, child_state_sets =
                List.unzip3 child_ret
              in
              let sym = fresh_state () in
              ( [(sym, spec, child_states)] @ List.concat child_rules
              , sym
              , Symbol.Set.union_list (Symbol.Set.singleton sym :: child_state_sets)
              ) )
    in
    let%map rules, initial_state, states = of_spec_tree' spec_tree in
    let states = Symbol.Set.add states any in
    let module CA = Constrained in
    { any_state= any
    ; automaton=
        { CA.components
        ; CA.rules
        ; CA.initial_states= Symbol.Set.singleton initial_state
        ; CA.states } }

  let of_skeleton zctx components sk spec =
    let module Let_syntax = Or_error.Let_syntax.Let_syntax in
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

  exception ConflictException of Conflict.t

  type search_state =
    { zctx: Z3.context
    ; cost_model: CostModel.t
    ; space: Constrained.t
    ; spec: Spec.t
    ; type_: Type.t
    ; max_cost: int }

  type check = Hypothesis.t -> unit

  let print_sexp x to_sexp = print_endline (Sexp.to_string_hum (to_sexp x))

  let rec search_at_cost :
      cost:int -> check -> search_state -> Hole.t -> Memoizer.t -> unit =
   fun ~cost check search_state hole memoizer ->
    let ss = search_state in
    if cost > ss.max_cost then ()
    else
      let candidates = Memoizer.get memoizer hole Specification.top ~cost in
      List.iter candidates ~f:(fun (candidate, _) ->
          print_endline (Sexp.to_string_hum ([%sexp_of: Hypothesis.t] candidate)) ;
          let components = ss.space.Constrained.components in
          let m_conflict =
            Conflict.of_skeleton ss.zctx components
              (Hypothesis.skeleton candidate)
              ss.spec
            |> Or_error.ok_exn
          in
          match m_conflict with
          | Some conflict ->
              print_newline () ;
              print_endline "Found conflict!" ;
              print_endline
                (Sexp.to_string_hum ([%sexp_of: Hypothesis.t] candidate)) ;
              print_endline (Sexp.to_string_hum ([%sexp_of: Conflict.t] conflict)) ;
              raise (ConflictException conflict)
          | None -> check candidate ) ;
      search_at_cost ~cost:(cost + 1) check search_state hole memoizer

  let rec search_in_space : check -> search_state -> unit =
   fun check search_state ->
    let ss = search_state in
    let gen =
      Constrained.to_generalizer ss.zctx ss.space ss.cost_model |> Or_error.ok_exn
    in
    let memo = Memoizer.create Library.empty gen ss.cost_model in
    Symbol.Set.iter ss.space.Constrained.initial_states ~f:(fun init_state ->
        let hole = Hole.create (Infer.instantiate 0 ss.type_) init_state in
        try search_at_cost ~cost:0 check search_state hole memo
        with ConflictException conflict ->
          let c_conflict = Conflict.complement conflict in
          (* print_newline (); *)
          (* print_endline "Conflict complement:"; *)
          (* print_endline (Sexp.to_string_hum ([%sexp_of:Conflict.t] c_conflict)); *)
          let cc_conflict = Conflict.to_constrained_automaton c_conflict in
          (* print_newline (); *)
          (* print_endline "Conflict complement (constrained):"; *)
          (* print_endline (Sexp.to_string_hum ([%sexp_of:Constrained.t] cc_conflict)); *)
          let space' =
            cc_conflict
            |> Constrained.intersect ss.space
            |> Constrained.reduce ss.zctx |> Or_error.ok_exn
          in
          print_newline () ;
          print_endline "New space:" ;
          print_endline (Sexp.to_string_hum ([%sexp_of: Constrained.t] space')) ;
          search_in_space check {search_state with space= space'} )

  let synthesize :
         max_cost:int
      -> Component.Set.t
      -> Spec.t
      -> Type.t
      -> Hypothesis.t Option.t Or_error.t =
   fun ~max_cost components spec type_ ->
    let search_state =
      { zctx= Z3.mk_context []
      ; cost_model= V2_engine.default_cost_model
      ; (* TODO: Should use our own cost model here. *)
        space= Constrained.mk_any components |> Tuple.T2.get2
      ; spec
      ; type_
      ; max_cost }
    in
    print_sexp search_state.space [%sexp_of: Constrained.t] ;
    Or_error.try_with (fun () ->
        try
          search_in_space (fun h -> raise (SynthesisException h)) search_state ;
          None
        with SynthesisException ret -> Some ret )

  let synthesize_from_examples :
         max_cost:int
      -> Component.Set.t
      -> Example.t list
      -> Hypothesis.t Option.t Or_error.t =
    let module Exs = Examples in
    let module T = Component.Term in
    let module V = Component.Variable in
    let module S = Component.Sort in
    let module Spec = Component.Specification in
    fun ~max_cost components examples ->
      (* Get the type of the examples, so we have argument and return types. *)
      let args_t, ret_t =
        match Infer.Type.normalize (Example.signature examples) with
        | Type.Arrow_t (args_t, ret_t) -> (args_t, ret_t)
        | t -> failwiths "Unexpected type." t [%sexp_of: Type.t]
      in
      (* Assign each argument a name. This is how we will refer to the
         arguments inside the hypothesis. *)
      let names =
        let fresh_name = Util.Fresh.mk_fresh_name_fun () in
        List.init (List.length args_t) ~f:(fun _ -> fresh_name ())
      in
      (* Generate a constraint for each example which relates inputs
         and outputs and a constraint for each example which determines
         the valid inputs. *)
      let constraints =
        List.map examples ~f:(function
          | `Apply (_, args), ret ->
              let args_terms =
                List.map ~f:(Eval.eval (Ctx.empty ())) args
                |> List.map ~f:T.of_value
                |> List.map2_exn names ~f:(fun n t -> (V.Free n, t))
              in
              let ret_term =
                (V.Output, T.of_value (Eval.eval (Ctx.empty ()) ret))
              in
              let abstract_terms = T.abstract (ret_term :: args_terms) in
              T.Apply ("And", abstract_terms)
          | ex -> failwiths "Unexpected example." ex [%sexp_of: Example.t] )
      in
      let _constraint = T.Apply ("Or", constraints) in
      let sorts =
        List.map2_exn names args_t ~f:(fun n t ->
            (V.Free n, S.of_type t |> Or_error.ok_exn) )
        |> V.Map.of_alist_exn
        |> V.Map.add ~key:V.Output ~data:(S.of_type ret_t |> Or_error.ok_exn)
      in
      let spec = {Spec._constraint; Spec.sorts} in
      let arg_components =
        List.map2_exn args_t names ~f:(fun t n ->
            { Component.arity= Type.arity t
            ; Component.type_= t
            ; Component.name= n
            ; Component.spec=
                { Spec._constraint=
                    T.Apply ("Eq", [T.Variable (V.Free n); T.Variable V.Output])
                ; Spec.sorts=
                    V.Map.of_alist_exn
                      [ (V.Free n, S.of_type t |> Or_error.ok_exn)
                      ; (V.Output, S.of_type t |> Or_error.ok_exn) ] } } )
        |> Component.Set.of_list
      in
      let components = Component.Set.union components arg_components in
      print_endline (Sexp.to_string_hum ([%sexp_of: Spec.t] spec)) ;
      let search_state =
        { zctx= Z3.mk_context []
        ; cost_model= V2_engine.default_cost_model
        ; (* TODO: Should use our own cost model here. *)
          space= Constrained.mk_any components |> Tuple.T2.get2
        ; type_= ret_t
        ; spec
        ; max_cost }
      in
      let io_ctx =
        List.map examples ~f:(function
          | `Apply (_, args), ret ->
              let ret = Eval.eval (Ctx.empty ()) ret in
              let ctx =
                List.map2_exn names args ~f:(fun n e ->
                    (n, Eval.eval (Ctx.empty ()) e) )
                |> Ctx.of_alist_exn
              in
              (ctx, ret)
          | e -> failwiths "Unexpected example." e [%sexp_of: Example.t] )
      in
      let check h =
        let h_expr = Hypothesis.to_expr h in
        let is_valid =
          List.for_all io_ctx ~f:(fun (ctx, ret) ->
              try Eval.eval ctx h_expr = ret with Eval.RuntimeError msg -> false )
        in
        if is_valid then raise (SynthesisException h)
      in
      print_sexp search_state.space [%sexp_of: Constrained.t] ;
      Or_error.try_with (fun () ->
          try
            search_in_space check search_state ;
            None
          with SynthesisException ret -> Some ret )
end
