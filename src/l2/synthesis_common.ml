open Core.Std

open Hypothesis
open Infer

module Generalizer = struct
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list
  
  module type S = sig
    val generalize : t
    val generalize_all : Hypothesis.t -> Hypothesis.t list
  end

  module Make (G: sig val generalize : t end) : S = struct
    include G
        
    let generalize_all hypo =
      let open Hypothesis in
      List.fold_left
        (List.sort ~cmp:(fun (h1, _) (h2, _) -> Hole.compare h1 h2) (holes hypo))
        ~init:[ hypo ]
        ~f:(fun hypos (hole, spec) ->
            let children = List.filter (generalize hole spec) ~f:(fun (c, _) ->
                kind c = Abstract || Specification.verify spec (skeleton c))
            in
            List.map hypos ~f:(fun p -> List.map children ~f:(fun (c, u) ->
                apply_unifier (fill_hole hole ~parent:p ~child:c) u))
            |> List.concat)
  end
end


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
  module type S = sig
    type t
    val create : unit -> t
    val get : t -> Hole.t -> Specification.t -> cost:int -> (Hypothesis.t * Unifier.t) list
  end

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
      } with compare, sexp

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
    } with compare, sexp

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
    } with sexp
  end

  module Make (G: Generalizer.S) : S = struct
    type t = HoleState.t HoleTable.t

    let create () = HoleTable.create ()

    let rec get m hole spec ~cost =
      if cost < 0 then raise (Invalid_argument "Argument out of range.") else
      if cost = 0 then [] else
        let module S = HoleState in
        let module H = Hypothesis in
        let (key, map) = Key.of_hole_spec hole spec in
        let state = HoleTable.find_or_add m key ~default:(fun () ->
            {
              S.hypotheses = CostTable.create ();
              S.generalizations = Lazy.from_fun (fun () -> G.generalize hole spec);
            })
        in
        let ret =
          match CostTable.find state.S.hypotheses cost with
          | Some hs -> hs
          | None ->
            (* For each expansion of the grammar symbol for this hole,
               fill in the holes in the hypothesis and return if it it
               matches the spec. *)
            let hs = List.concat_map (Lazy.force state.S.generalizations) ~f:(fun (p, p_u) ->
                match H.kind p with
                | H.Concrete -> if H.cost p = cost then [ (p, p_u) ] else []
                | H.Abstract -> if H.cost p >= cost then [] else
                    let num_holes = List.length (H.holes p) in
                    let all_hole_costs =
                      Util.m_partition (cost - H.cost p) num_holes
                      |> List.concat_map ~f:Util.permutations
                    in
                    List.concat_map all_hole_costs ~f:(fun hole_costs ->
                        List.fold2_exn (H.holes p) hole_costs ~init:[ (p, p_u) ]
                          ~f:(fun hs (hole, spec) hole_cost ->
                              List.concat_map hs ~f:(fun (p, p_u) ->
                                  let children = get m hole spec hole_cost in
                                  List.map children ~f:(fun (c, c_u) ->
                                      let u = Unifier.compose c_u p_u in
                                      let h = H.fill_hole hole ~parent:p ~child:c in
                                      h, u))))
                    |> List.filter ~f:(fun (h, _) ->
                        (* let () = Debug.eprintf "Verifying %d %s" h.H.cost (H.to_string_hum h) in *)
                        match H.kind h with
                        | H.Concrete -> H.verify h
                        | H.Abstract -> failwiths "BUG: Did not fill in all holes." h H.sexp_of_t))
            in
            CostTable.add_exn state.S.hypotheses ~key:cost ~data:hs; hs
        in
        List.map ret ~f:(fun (h, u) -> (h, denormalize_unifier u map))
  end
end
