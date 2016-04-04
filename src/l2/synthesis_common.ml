open Core.Std

open Collections
open Hypothesis
open Infer

let print_sexp x s = print_endline (Sexp.to_string_hum (s x))

module Generalizer = struct
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list
  
  let generalize_all generalize cost_model hypo =
    let open Hypothesis in
    List.fold_left
      (List.sort ~cmp:(fun (h1, _) (h2, _) -> Hole.compare h1 h2) (holes hypo))
      ~init:[ hypo ]
      ~f:(fun hypos (hole, spec) ->
          let children = List.filter (generalize hole spec) ~f:(fun (c, _) ->
              kind c = Abstract || Specification.verify spec (skeleton c))
          in
          List.map hypos ~f:(fun p -> List.map children ~f:(fun (c, u) ->
              apply_unifier (fill_hole cost_model hole ~parent:p ~child:c) u))
          |> List.concat)

  let compose : t -> t -> t = fun g1 g2 hole spec ->
    (g1 hole spec) @ (g2 hole spec)

  let compose_all_exn : t list -> t = function
    | [] -> failwith "Expected a non-empty list."
    | g::gs -> List.fold gs ~init:g ~f:compose
end

module Deduction = struct
  module Sp = Specification
  module Sk = Skeleton

  type t = Sp.t Sk.t -> Sp.t Sk.t Option.t

  let no_op : t = Option.return

  let compose : t -> t -> t = fun d1 d2 ->
    fun skel -> Option.bind (d1 skel) d2
end

let timer =
  let t = Timer.empty () in
  let n = Timer.add_zero t in
  n "deduction_time" "Total time spent in deduction methods.";
  t
let run_with_time = Timer.run_with_time timer 

let counter =
  let c = Counter.empty () in
  let n = Counter.add_zero c in
  n "num_hypos" "Number of hypotheses verified.";
  c
let incr = Counter.incr counter 

(** Maps (hole, spec) pairs to the hypotheses that can fill in the hole and match the spec.

    The memoizer can be queried with a hole, a spec and a cost.

    Internally, the type of the hole and the types in the type context
    of the hole are normalized by substituting their free type
    variable ids with fresh ones. The memoizer only stores the
    normalized holes. This increases potential for sharing when
    different holes have the same type structure but different ids in
    their free type variables.
*)
module Memoizer = struct
  let denormalize_unifier u map =
    Unifier.to_alist u
    |> List.filter_map ~f:(fun (k, v) -> Option.map (Int.Map.find map k) ~f:(fun k' -> k', v))
    |> Unifier.of_alist_exn

  module Key = struct
    module Hole_without_id = struct
      type t = {
        ctx : Type.t StaticDistance.Map.t;
        type_ : Type.t;
        symbol : Symbol.t;
      } [@@deriving compare, sexp]

      let normalize_free ctx t =
        let open Type in
        let fresh_int = Util.Fresh.mk_fresh_int_fun () in
        let rec norm t = match t with
          | Var_t { contents = Quant _ }
          | Const_t _ -> t
          | App_t (name, args) -> App_t (name, List.map args ~f:norm)
          | Arrow_t (args, ret) -> Arrow_t (List.map args ~f:norm, norm ret)
          | Var_t { contents = Free (id, level) } ->
            (match Int.Map.find !ctx id with
             | Some id -> Type.free id level
             | None ->
               let new_id = fresh_int () in
               ctx := Int.Map.add !ctx ~key:new_id ~data:id;
               Type.free new_id level)
          | Var_t { contents = Link t } -> norm t
        in
        norm t

      let of_hole h =
        let free_ctx = ref Int.Map.empty in
        let type_ = normalize_free free_ctx h.Hole.type_ in
        let type_ctx = StaticDistance.Map.map h.Hole.ctx ~f:(normalize_free free_ctx) in
        ({ ctx = type_ctx; symbol = h.Hole.symbol; type_; }, !free_ctx)
    end

    type t = {
      hole : Hole_without_id.t;
      spec : Specification.t;
    } [@@deriving compare, sexp]

    let to_string k = Sexp.to_string_hum ([%sexp_of:t] k)

    let hash = Hashtbl.hash

    let of_hole_spec hole spec =
      let (hole, map) = Hole_without_id.of_hole hole in
      ({ hole; spec; }, map)
  end

  module HoleTable = Hashtbl.Make(Key)
  module CostTable = Int.Table

  module HoleState = struct
    type t = {
      hypotheses : (Hypothesis.t * Unifier.t) list CostTable.t;
      generalizations : (Hypothesis.t * Unifier.t) list Lazy.t;
    } [@@deriving sexp]
  end

  type t = {
    hole_table : HoleState.t HoleTable.t;
    generalize : Generalizer.t;
    cost_model : CostModel.t;
    deduction : Deduction.t;
    counter : Counter.t;
  }

  let create : ?deduce:Deduction.t -> Generalizer.t -> CostModel.t -> t =
    fun ?(deduce = Deduction.no_op) g cm ->
      {
        generalize = g;
        cost_model = cm;
        deduction = (fun sk -> run_with_time "deduction_time" (fun () -> deduce sk));
        hole_table = HoleTable.create ();
        counter = Counter.empty ();
      }

  let to_string m = Sexp.to_string_hum ([%sexp_of:HoleState.t HoleTable.t] m.hole_table)

  (** Requires: 'm' is a memoization table. 'hypo' is a
      hypothesis. 'cost' is an integer cost.

      Ensures: Returns a list of hypotheses which are children of
      'hypo' and have cost 'cost'. Uses the memoization table to avoid
      as much computation as possible.  
  *)
  let rec fill_holes_in_hypothesis m hypo cost =
    (* printf "Fill %s %d\n" (Hypothesis.to_string_hum hypo) cost; *)
    (* flush stdout; *)
    let module H = Hypothesis in

    let holes = H.holes hypo in
    let total_hole_cost =
      List.map holes ~f:(fun (h, _) -> m.cost_model.CostModel.hole h)
      |> List.fold_left ~init:0 ~f:(+)
    in

    let spine_cost = H.cost hypo - total_hole_cost in

    match H.kind hypo with
    | H.Concrete -> if spine_cost = cost then
        Sequence.singleton (hypo, Unifier.empty)
      else Sequence.empty
    | H.Abstract -> if spine_cost >= cost then Sequence.empty else
        (* Determine all possible ways to fill in the holes in this
           generalization. We compute the total cost of all holes because
           this is the part of the hypothesis that will be replaced when
           we generalize, so this cost can be discounted. *)
        let all_hole_costs =
          let num_holes = List.length holes in
          Combinat.m_partition (cost - spine_cost) num_holes
          |> Sequence.concat_map ~f:Combinat.permutations
        in
        let holes = Sequence.of_list holes in

        (* For each list of hole costs... *)
        Sequence.concat_map all_hole_costs ~f:(fun hole_costs ->
            let hole_costs = Array.to_sequence hole_costs in

            Sequence.zip holes hole_costs

            (* Fold over the holes and their corresponding cost... *)
            |> Sequence.fold
              ~init:(Sequence.singleton (hypo, Unifier.empty))
              ~f:(fun hs ((hole, spec), hole_cost) ->
                  (* And select all hypotheses which could be used to fill them. *)
                  Sequence.concat_map hs ~f:(fun (p, p_u) ->
                      let hole = Hole.apply_unifier p_u hole in
                      let children =
                        get m hole spec ~cost:hole_cost
                        |> Sequence.of_list 
                      in

                      (* Fill in the hole and merge the unifiers. *)
                      Sequence.map children ~f:(fun (c, c_u) ->
                          let u = Unifier.compose c_u p_u in
                          let h = H.fill_hole m.cost_model hole ~parent:p ~child:c in
                          h, u)
                        
                      |> Sequence.filter_map ~f:(fun (h, u) ->
                          match H.kind h with
                          | H.Concrete -> Some (h, u)
                          | H.Abstract -> 
                            let sk = Hypothesis.skeleton h in
                            Option.map (m.deduction sk) (fun sk' ->
                                (Hypothesis.of_skeleton m.cost_model sk', u))))))
          
        (* Only return concrete hypotheses which match the specification. *)
        |> Sequence.filter ~f:(fun (h, _) ->
            incr "num_hypos";
            let num_hypos = Counter.find_exn counter "num_hypos" in
            if num_hypos mod 100 = 0 then begin
              printf "%d\n" num_hypos;
              flush stdout
            end;
            match H.kind h with
            | H.Concrete -> H.verify h
            | H.Abstract -> failwiths "BUG: Did not fill in all holes." h H.sexp_of_t)
  
  and get m hole spec ~cost =
    if cost < 0 then failwiths "Argument out of range." cost [%sexp_of:int] else
    if cost = 0 then [] else
      let module S = HoleState in
      let module H = Hypothesis in

      (* For the given hole and specification, select the 'state'
         object, which contains previously generated hypotheses for this
         hole, spec pair and possible generalizations of the hole. *)
      let (key, map) = Key.of_hole_spec hole spec in
      let state = HoleTable.find_or_add m.hole_table key ~default:(fun () ->
          {
            S.hypotheses = CostTable.create ();
            S.generalizations = Lazy.from_fun (fun () ->
                m.generalize hole spec
                |> List.filter_map ~f:(fun (h, u) ->
                    match H.kind h with
                    | H.Concrete -> Some (h, u)
                    | H.Abstract -> 
                      let sk = Hypothesis.skeleton h in
                      Option.map (m.deduction sk) (fun sk' ->
                          (Hypothesis.of_skeleton m.cost_model sk', u)))
              );
          })
      in
      let ret =
        match CostTable.find state.S.hypotheses cost with
        (* If we have previously generated the hypotheses of this cost, return them. *)
        | Some hs -> hs

        (* Otherwise, we will need to use the available
           generalizations to generate hypothesis of the current cost. *)
        | None ->
          let hs =
          (* For each possible generalization, fill in its holes so
             that the resulting hypothesis has the correct cost. *)
            Lazy.force state.S.generalizations

            |> List.concat_map ~f:(fun (p, p_u) ->
                List.map (fill_holes_in_hypothesis m p cost |> Sequence.to_list)
                  ~f:(fun (filled_p, filled_u) -> (filled_p, Unifier.compose filled_u p_u)))

            |> List.dedup
          in

          (* Save the computed result, so we can use it later. *)
          CostTable.add_exn state.S.hypotheses ~key:cost ~data:hs; hs
      in
      List.map ret ~f:(fun (h, u) -> (h, denormalize_unifier u map))

  let to_sequence : t -> ?min_cost:int -> ?max_cost:int -> Hypothesis.t -> (Hypothesis.t * Unifier.t) Sequence.t Sequence.t =
    fun m ?(min_cost = 0) ?max_cost hypo ->
      match max_cost with
      | Some max_cost -> 
        Sequence.unfold ~init:min_cost ~f:(fun cost ->
            (* printf "Cost: %d\n" cost; *)
            (* printf "%s\n" (to_string m); *)
            (* print_newline (); *)
            (* flush stdout; *)
            if cost > max_cost then None else
              Some (fill_holes_in_hypothesis m hypo cost, cost + 1))
      | None ->
        Sequence.unfold ~init:min_cost ~f:(fun cost ->
            Some (fill_holes_in_hypothesis m hypo cost, cost + 1))

  let to_flat_sequence : t -> ?min_cost:int -> ?max_cost:int -> Hypothesis.t -> (Hypothesis.t * Unifier.t) Sequence.t =
    fun m ?(min_cost = 0) ?max_cost hypo  ->
      to_sequence m ~min_cost ?max_cost hypo
      (* |> Sequence.map ~f:Sequence.of_list *)
      |> Sequence.concat
end

module Synthesizer = struct
  module type S = sig
    val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t Or_error.t
  end
end
