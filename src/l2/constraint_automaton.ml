open Core.Std

open Collections
open Hypothesis

module Spec = Component.Specification

module Rule = struct
  type t = Symbol.t * Spec.t * (Symbol.t list)

  let start_state (q, _, _) = q
  let spec (_, s, _) = s
  let end_states (_, _, qq) = qq

  let arity r = List.length (end_states r)
  let is_terminal r = arity r = 0
end

module ConstrainedAutomaton = struct
  module C = Component
    
  type t = {
    states : Symbol.Set.t;
    initial_states : Symbol.Set.t;
    components : C.Set.t;
    rules : Rule.t list;
  }

  let create states initial_states components rules =
    if not (Set.subset initial_states states) then
      failwiths "Initial states not a subset of states."
        (states, initial_states) <:sexp_of<String.Set.t * String.Set.t>>
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
      
  let reduce a =
    let m =
      List.fold_left a.rules ~init:Symbol.Set.empty ~f:(fun m r ->
          if Rule.is_terminal r &&
             C.Set.exists a.components ~f:(fun c -> Spec.entails (Rule.spec r) c.C.spec)
          then Set.add m (Rule.start_state r)
          else m
        )
    in

    let rec fix m =
      let m' =
        List.fold_left a.rules ~init:m ~f:(fun m' r ->
            if List.for_all (Rule.end_states r) ~f:(Set.mem m') &&
               C.Set.exists a.components ~f:(fun c -> Spec.entails (Rule.spec r) c.C.spec)
            then Set.add m' (Rule.start_state r)
            else m')
      in
      if Set.equal m m' then m' else fix m'
    in

    let m = fix m in
    {
      a with
      states = m;
      initial_states = Set.inter a.initial_states m;
      rules = List.filter a.rules ~f:(fun r ->
          Set.mem m (Rule.start_state r) &&
          List.for_all (Rule.end_states r) ~f:(Set.mem m));
    }

  let is_empty a =
    let a' = reduce a in
    (Set.is_empty a'.initial_states, a')

  let to_generalizer a cm =
    let open Option.Monad_infix in
    let module H = Hypothesis in
    let module Sp = Specification in
    let gen hole spec =
      (* Select all rules which match the hole symbol. *)
      List.filter a.rules ~f:(fun r -> hole.Hole.symbol = Rule.start_state r) |> 

      (* For each matching rule, select each matching component and expand. *)
      List.map ~f:(fun r ->
          C.Set.to_list a.components |>
          List.filter_map ~f:(fun c ->
              if Spec.entails (Rule.spec r) c.C.spec then
                match c.C.type_ with
                | Infer.Type.Arrow_t (args_t, ret_t) ->
                  Infer.Unifier.of_types ret_t hole.Hole.type_ >>| fun unifier ->
                  let args =
                    List.map args_t ~f:(fun t -> Infer.Unifier.apply unifier t) |>
                    List.map2_exn (Rule.end_states r) ~f:(fun q t ->
                        H.hole cm (Hole.create hole.Hole.ctx t q) Sp.Top)
                  in
                  let hypo = H.apply cm (H.id_name cm c.C.name Sp.Top) args spec in
                  (hypo, unifier)
                | type_ ->
                  if List.length (Rule.end_states r) > 0 then
                    failwiths "Number of output states does not match component arity."
                      (r, c) <:sexp_of<Rule.t * C.t>>
                  else
                    Infer.Unifier.of_types c.C.type_ hole.Hole.type_ >>| fun unifier ->
                    let hypo = H.id_name cm c.C.name Sp.Top in
                    (hypo, unifier)
              else None
            )) |>
      List.concat_no_order
    in
    gen

  module SymbolPair = struct
    module T = struct
      type t = Symbol.t * Symbol.t with compare, sexp
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

module ConflictAutomaton = struct
  module A = ConstrainedAutomaton
    
  type t = {
    automaton : A.t;
    any_state : Symbol.t;
  }

  let complement ca =
    let rules' = List.concat_map ca.automaton.A.rules ~f:(fun r ->
        let negated_r = (Rule.start_state r, Spec.negate (Rule.spec r), Rule.end_states r) in
        let rs = List.map (List.diag (Rule.end_states r) ca.any_state) ~f:(fun es ->
            (Rule.start_state r, Rule.spec r, es))
        in
        negated_r :: rs)
    in
    { ca with automaton = { ca.automaton with A.rules = rules' } }
end
