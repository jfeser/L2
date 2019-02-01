open Core
open Collections
open Hypothesis
open Infer

module Generalizer = struct
  type t =
       Type.t StaticDistance.Map.t
    -> Type.t
    -> Symbol.t
    -> Specification.t
    -> (Hypothesis.t * Unifier.t) list

  type params = {cost_model: CostModel.t; library: Library.t}

  let generalize_single : params -> t -> Hypothesis.t -> Hypothesis.t list =
    let open Hypothesis in
    fun params generalize hypo ->
      holes hypo
      |> List.sort ~compare:(fun (h1, _) (h2, _) -> Hole.compare h1 h2)
      |> List.map ~f:(fun (hole, spec) ->
             generalize hole.Hole.ctx hole.Hole.type_ hole.Hole.symbol spec
             |> List.filter ~f:(fun (c, _) ->
                    kind c = Abstract
                    || Specification.verify ~library:params.library spec
                         (skeleton c) )
             |> List.map ~f:(fun (c, u) ->
                    let h =
                      fill_hole params.cost_model hole ~parent:hypo ~child:c
                    in
                    apply_unifier h u ) )
      |> List.concat

  let generalize_all params generalize hypo =
    let open Hypothesis in
    List.fold_left
      (List.sort ~compare:(fun (h1, _) (h2, _) -> Hole.compare h1 h2) (holes hypo))
      ~init:[hypo]
      ~f:(fun hypos (hole, spec) ->
        let children =
          List.filter
            (generalize hole.Hole.ctx hole.Hole.type_ hole.Hole.symbol spec)
            ~f:(fun (c, _) ->
              kind c = Abstract
              || Specification.verify ~library:params.library spec (skeleton c) )
        in
        List.map hypos ~f:(fun p ->
            List.map children ~f:(fun (c, u) ->
                apply_unifier
                  (fill_hole params.cost_model hole ~parent:p ~child:c)
                  u ) )
        |> List.concat )

  let compose : t -> t -> t =
   fun g1 g2 ctx type_ symbol spec ->
    g1 ctx type_ symbol spec @ g2 ctx type_ symbol spec

  let compose_all_exn : t list -> t = function
    | [] -> failwith "Expected a non-empty list."
    | g :: gs -> List.fold gs ~init:g ~f:compose
end

module Deduction = struct
  module Sp = Specification
  module Sk = Skeleton

  type t = Sk.t -> Sk.t Option.t

  exception Bottom

  let bottom : t =
   fun sk ->
    let rec bot sk =
      if Sp.equal (Sk.spec sk) Sp.bottom then raise Bottom ;
      match Sk.ast sk with
      | Sk.Num _ | Sk.Bool _ | Sk.Id _ | Sk.Hole _ -> ()
      | Sk.List l -> List.iter l ~f:bot
      | Sk.Tree t -> Tree.iter t ~f:bot
      | Sk.Let {bound; body} -> bot bound ; bot body
      | Sk.Lambda {body; _} -> bot body
      | Sk.Op {args; _} -> List.iter args ~f:bot
      | Sk.Apply {func; args} -> bot func ; List.iter args ~f:bot
    in
    try bot sk ; Some sk with Bottom -> None

  let no_op : t = Option.return

  let compose : t -> t -> t = fun d1 d2 skel -> Option.bind (d1 skel) ~f:d2
end

let timer =
  let t = Timer.empty () in
  let n = Timer.add_zero t in
  n "deduction_time" "Total time spent in deduction methods." ;
  t

let counter =
  let c = Counter.empty () in
  let n = Counter.add_zero c in
  n "num_hypos" "Number of hypotheses verified." ;
  n "num_holes" "Number of unique holes in the memoization table." ;
  n "hole_hits" "Number of hits on the memoization table" ;
  n "hole_misses" "Number of misses on the memoization table" ;
  n "num_saved_hypos" "Number of hypotheses stored in the memoization table." ;
  n "num_distinct_hypos" "Number of distinct hypotheses in memoization table." ;
  n "num_distinct_types" "Number of distinct types in memoization table." ;
  n "num_distinct_specs" "Number of distinct specs in memoization table." ;
  n "top_match_count"
    "Number of times we could have used hypos from the top spec row." ;
  n "sigs_none" "# of hypos w/ no signature" ;
  n "sigs_checked" "# of signatures calculated" ;
  n "sigs_fail" "# of failing hypotheses" ;
  n "sigs_dup" "# of duplicate hypotheses" ;
  c

let incr = Counter.incr counter

let sexp_log =
  let s = SexpLog.empty () in
  let n = SexpLog.add s in
  n "specs" "Specifications in memoization table." ;
  s

(** Maps (hole, spec) pairs to the hypotheses that can fill in the
    hole and match the spec.

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
    |> List.filter_map ~f:(fun (k, v) ->
           match Int.Map.find map k with Some k' -> Some (k', v) | None -> None )
    |> Unifier.of_alist_exn

  module Key = struct
    module Hole_without_id = struct
      type t = {ctx: Type.t StaticDistance.Map.t; type_: Type.t; symbol: Symbol.t}
      [@@deriving compare, sexp]

      let normalize_free ctx t =
        let open Type in
        let fresh_int = Util.Fresh.mk_fresh_int_fun () in
        let rec norm t =
          match t with
          | Var_t {contents= Quant _} | Const_t _ -> t
          | App_t (name, args) -> App_t (name, List.map args ~f:norm)
          | Arrow_t (args, ret) -> Arrow_t (List.map args ~f:norm, norm ret)
          | Var_t {contents= Free (id, level)} -> (
            match Int.Map.find !ctx id with
            | Some id -> Type.free id level
            | None ->
                let new_id = fresh_int () in
                ctx := Int.Map.set !ctx ~key:new_id ~data:id ;
                Type.free new_id level )
          | Var_t {contents= Link t} -> norm t
        in
        norm t

      let of_hole h =
        let free_ctx = ref Int.Map.empty in
        let type_ = normalize_free free_ctx h.Hole.type_ in
        let type_ctx =
          StaticDistance.Map.map h.Hole.ctx ~f:(normalize_free free_ctx)
        in
        ({ctx= type_ctx; symbol= h.Hole.symbol; type_}, !free_ctx)
    end

    type t = {hole: Hole_without_id.t; spec: Specification.t}
    [@@deriving compare, sexp]

    let hash = Hashtbl.hash

    let of_hole_spec hole spec =
      let hole, map = Hole_without_id.of_hole hole in
      ({hole; spec}, map)
  end

  module SignatureSet = Hash_set.Make (struct
    type t = Value.t list [@@deriving sexp, compare]

    let hash = Hashtbl.hash
  end)

  module HoleTable = Hashtbl.Make (Key)
  module CostTable = Int.Table

  module HoleState = struct
    type t =
      { signatures: SignatureSet.t
      ; hypotheses: (Hypothesis.t * Unifier.t) list CostTable.t
      ; generalizations: (Hypothesis.t * Unifier.t) list Lazy.t }
    [@@deriving sexp]
  end

  module Config = struct
    type t =
      { generalize: Generalizer.t
      ; cost_model: CostModel.t
      ; deduction: Deduction.t
      ; library: Library.t
      ; search_space_out: Out_channel.t Option.t }
  end

  open Config

  type t = {hole_table: HoleState.t HoleTable.t; config: Config.t}

  let create : Config.t -> t =
   fun config -> {config; hole_table= HoleTable.create ()}

  let to_string m =
    Sexp.to_string_hum ([%sexp_of: HoleState.t HoleTable.t] m.hole_table)

  let perform_deduction :
      t -> (Hypothesis.t * 'a) Sequence.t -> (Hypothesis.t * 'a) Sequence.t =
    let module H = Hypothesis in
    fun m ->
      Sequence.filter_map ~f:(fun (h, u) ->
          match H.kind h with
          | H.Concrete -> Some (h, u)
          | H.Abstract ->
              let sk = Hypothesis.skeleton h in
              Option.map (m.config.deduction sk) ~f:(fun sk' ->
                  (Hypothesis.of_skeleton m.config.cost_model sk', u) ) )

  let select_matching :
      t -> (Hypothesis.t * 'a) Sequence.t -> (Hypothesis.t * 'a) Sequence.t =
    let module H = Hypothesis in
    fun m ->
      Sequence.filter ~f:(fun (h, _) ->
          incr "num_hypos" ;
          Status.(
            print_status {synthesis= counter; hashcons= Skeleton.Table.counter}) ;
          match H.kind h with
          | H.Concrete -> H.verify ~library:m.config.library h
          | H.Abstract -> failwiths "BUG: Did not fill in all holes." h H.sexp_of_t
      )

  let dump_to_channel :
         t
      -> parent:Hypothesis.t
      -> (Hypothesis.t * 'a) Sequence.t
      -> (Hypothesis.t * 'a) Sequence.t =
    let module H = Hypothesis in
    fun m ~parent:_ seq ->
      match m.config.search_space_out with
      | Some ch ->
          Sequence.inspect seq ~f:(fun (h, _) ->
              let json = `List [`String (H.to_string_hum h)] in
              Json.to_channel ~std:true ch json )
      | None -> seq

  (** Requires: 'm' is a memoization table. 'hypo' is a
      hypothesis. 'cost' is an integer cost.

      Ensures: Returns a list of hypotheses which are children of
      'hypo' and have cost 'cost'. Uses the memoization table to avoid
      as much computation as possible.  
  *)
  let rec fill_holes_in_hypothesis :
      t -> Hypothesis.t -> int -> (Hypothesis.t * Unifier.t) Sequence.t =
    let module Seq = Sequence in
    let module H = Hypothesis in
    fun m hypo cost ->
      (* printf "Fill %s %d\n" (Hypothesis.to_string_hum hypo) cost; *)
      (* flush stdout; *)
      let holes = H.holes hypo in
      let total_hole_cost =
        List.map holes ~f:(fun (h, _) -> m.config.cost_model.CostModel.hole h)
        |> List.fold_left ~init:0 ~f:( + )
      in
      let spine_cost = H.cost hypo - total_hole_cost in
      match H.kind hypo with
      | H.Concrete ->
          if spine_cost = cost then Seq.singleton (hypo, Unifier.empty)
          else Seq.empty
      | H.Abstract -> (
          if spine_cost > cost then Seq.empty
          else
            match m.config.deduction (Hypothesis.skeleton hypo) with
            | Some sk' ->
                let hypo = Hypothesis.of_skeleton m.config.cost_model sk' in
                (* Determine all possible ways to fill in the holes in this
                 generalization. We compute the total cost of all holes because
                 this is the part of the hypothesis that will be replaced when
                 we generalize, so this cost can be discounted. *)
                let all_hole_costs =
                  let num_holes = List.length holes in
                  Combinat.m_partition_with_zeros (cost - spine_cost) num_holes
                  |> Seq.concat_map ~f:Combinat.permutations
                in
                let holes = Seq.of_list holes in
                (* For each list of hole costs... *)
                Seq.concat_map all_hole_costs ~f:(fun hole_costs ->
                    let hole_costs = Array.to_sequence hole_costs in
                    Seq.zip holes hole_costs
                    (* Fold over the holes and their corresponding cost... *)
                    |> Seq.fold
                         ~init:(Seq.singleton (hypo, Unifier.empty))
                         ~f:(fun hs ((hole, _), hole_cost) ->
                           (* And select all hypotheses which could be used to fill them. *)
                           Seq.concat_map hs ~f:(fun (p, p_u) ->
                               let spec =
                                 List.find_map_exn (H.holes p) ~f:(fun (h, s) ->
                                     if Hole.equal hole h then Some s else None )
                               in
                               let hole = Hole.apply_unifier p_u hole in
                               let children =
                                 get m hole spec ~cost:hole_cost |> Seq.of_list
                               in
                               (* Fill in the hole and merge the unifiers. *)
                               Seq.map children ~f:(fun (c, c_u) ->
                                   let u = Unifier.compose ~outer:p_u ~inner:c_u in
                                   let h =
                                     H.fill_hole m.config.cost_model hole ~parent:p
                                       ~child:c
                                   in
                                   (h, u) )
                               |> perform_deduction m ) ) )
                (* Only return concrete hypotheses which match the specification. *)
                |> select_matching m
                (* Dump child hypotheses to channel if requested. *)
                |> dump_to_channel m ~parent:hypo
            | None -> Seq.empty )

  and get :
      t -> Hole.t -> Specification.t -> cost:int -> (Hypothesis.t * Unifier.t) list
      =
    let module S = HoleState in
    let module H = Hypothesis in
    fun m hole spec ~cost ->
      if cost < 0 then failwiths "Argument out of range." cost [%sexp_of: int]
      else
        (* For the given hole and specification, select the 'state'
           object, which contains previously generated hypotheses for this
           hole, spec pair and possible generalizations of the hole. *)
        let key, map = Key.of_hole_spec hole spec in
        let state =
          match HoleTable.find m.hole_table key with
          | Some state -> incr "hole_hits" ; state
          | None ->
              (* let distinct_specs = *)
              (*   m.hole_table *)
              (*   |> HoleTable.keys *)
              (*   |> List.map ~f:(fun k -> k.Key.spec) *)
              (*   |> List.dedup ~compare:Specification.compare *)
              (* in *)
              (* Counter.set counter "num_distinct_specs" (List.length distinct_specs); *)
              (* set_sexp "specs" ([%sexp_of:Specification.t list] distinct_specs); *)
              
              (* let num_distinct_types = *)
              (*   m.hole_table *)
              (*   |> HoleTable.keys *)
              (*   |> List.map ~f:(fun k -> k.Key.hole.Key.Hole_without_id.type_) *)
              (*   |> List.dedup ~compare:Type.compare *)
              (*   |> List.length *)
              (* in *)
              (* Counter.set counter "num_distinct_types" num_distinct_types; *)
              incr "hole_misses" ;
              let state' =
                Counter.set counter "num_holes" (HoleTable.length m.hole_table) ;
                { S.signatures= SignatureSet.create ()
                ; S.hypotheses= CostTable.create ()
                ; S.generalizations=
                    Lazy.from_fun (fun () ->
                        m.config.generalize key.Key.hole.Key.Hole_without_id.ctx
                          key.Key.hole.Key.Hole_without_id.type_
                          key.Key.hole.Key.Hole_without_id.symbol spec
                        |> Sequence.of_list |> perform_deduction m
                        |> Sequence.to_list ) }
              in
              HoleTable.add_exn m.hole_table ~key ~data:state' ;
              state'
        in
        let ret =
          match CostTable.find state.S.hypotheses cost with
          (* If we have previously generated the hypotheses of this cost, return them. *)
          | Some hs -> hs
          (* Otherwise, we will need to use the available
             generalizations to generate hypothesis of the current cost. *)
          | None ->
              (* let (top_key, _) = Key.of_hole_spec hole Specification.top in *)
              (* let top_match_count = begin match HoleTable.find m.hole_table top_key with *)
              (*   | Some state -> begin match CostTable.find state.S.hypotheses cost with *)
              (*       | Some hs -> List.length hs *)
              (*       | None -> 0 *)
              (*     end *)
              (*   | None -> 0 *)
              (* end *)
              (* in *)
              (* Counter.set counter "top_match_count" top_match_count; *)
              let hs =
                (* For each possible generalization, fill in its holes so
                 that the resulting hypothesis has the correct cost. *)
                Lazy.force state.S.generalizations
                |> List.concat_map ~f:(fun (p, p_u) ->
                       Sequence.map (fill_holes_in_hypothesis m p cost)
                         ~f:(fun (filled_p, filled_u) ->
                           (filled_p, Unifier.compose ~inner:filled_u ~outer:p_u) )
                       |> Sequence.to_list )
                |> List.filter ~f:(fun (h, _) ->
                       let module Sp = Specification in
                       match (H.spec h).Sp.data with
                       | Inputs.Inputs inp -> (
                           let m_sign =
                             Inputs.signature m.config.Config.library (H.skeleton h)
                               inp
                           in
                           incr "sigs_checked" ;
                           match m_sign with
                           | Some sign ->
                               if Hash_set.mem state.HoleState.signatures sign then (
                                 incr "sigs_dup" ; false )
                               else (
                                 Hash_set.add state.HoleState.signatures sign ;
                                 true )
                           | None -> incr "sigs_fail" ; false )
                       | _ -> incr "sigs_none" ; true )
              in
              (* Save the computed result, so we can use it later. *)
              CostTable.add_exn state.S.hypotheses ~key:cost ~data:hs ;
              (* let all_saved_hypos = *)
              (*   m.hole_table *)
              (*   |> HoleTable.to_alist  *)
              (*   |> List.map ~f:(fun (_, data) -> *)
              (*       data.HoleState.hypotheses *)
              (*       |> CostTable.to_alist *)
              (*       |> List.map ~f:(fun (_, hs) -> hs) *)
              (*       |> List.concat) *)
              (*   |> List.concat *)
              (* in *)
              (* let num_distinct_hypos = *)
              (*   all_saved_hypos *)
              (*   |> List.map ~f:Tuple.T2.get1 *)
              (*   |> List.dedup ~compare:H.compare_skeleton *)
              (*   |> List.length *)
              (* in *)
              (* Counter.set counter "num_distinct_hypos" num_distinct_hypos; *)
              (* let num_saved_hypos = *)
              (*   all_saved_hypos *)
              (*   |> List.length *)
              (* in *)
              (* Counter.set counter "num_saved_hypos" num_saved_hypos; *)
              hs
        in
        List.map ret ~f:(fun (h, u) ->
            let u' = denormalize_unifier u map in
            (h, u') )

  let to_sequence :
         t
      -> ?min_cost:int
      -> ?max_cost:int
      -> Hypothesis.t
      -> (Hypothesis.t * Unifier.t) Sequence.t Sequence.t =
   fun m ?(min_cost = 0) ?max_cost hypo ->
    match max_cost with
    | Some max_cost ->
        Sequence.unfold ~init:min_cost ~f:(fun cost ->
            (* printf "Cost: %d\n" cost; *)
            (* printf "%s\n" (to_string m); *)
            (* print_newline (); *)
            (* flush stdout; *)
            if cost > max_cost then None
            else Some (fill_holes_in_hypothesis m hypo cost, cost + 1) )
    | None ->
        Sequence.unfold ~init:min_cost ~f:(fun cost ->
            Some (fill_holes_in_hypothesis m hypo cost, cost + 1) )

  let to_flat_sequence :
         t
      -> ?min_cost:int
      -> ?max_cost:int
      -> Hypothesis.t
      -> (Hypothesis.t * Unifier.t) Sequence.t =
   fun m ?(min_cost = 0) ?max_cost hypo ->
    to_sequence m ~min_cost ?max_cost hypo
    (* |> Sequence.map ~f:Sequence.of_list *)
    |> Sequence.concat
end

module Synthesizer = struct
  module type S = sig
    val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t Or_error.t
  end
end
