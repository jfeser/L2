open Core.Std

type example = expr Ctx.t * expr

type hole = {
  examples: example list;
  signature: typ;
  tctx: typ Ctx.t;
}

type spec = {
  target: expr Ctx.t -> expr -> expr;
  holes: hole Ctx.t;
}

module type GeneralizerImpl = sig
  val deduce_examples : example list -> string list -> example list option

  (** Given a type context and a list of examples for a hole, generate
      a list of input lists selected from the type context that are
      compatible with the generalization. *)
  val select_inputs : typ Ctx.t -> (expr Ctx.t * expr) list -> (string * typ) list list

  val generate_spec : (string * typ) list -> spec option
end

module Generalizer (Impl : GeneralizerImpl) = struct
  let generalize (spec: spec) : spec list =
    (* Attempt to generalize each hole in the specification. *)
    Ctx.to_alist spec.holes
    |> List.concat_map ~f:(fun (hole_name, hole) ->
        if hole.depth > 0 then
          (* Select inputs for the generalization. I.e., if we're
             implementing the hole with map, this would select all lists
             in the type context that could act as an input to map. *)
          let selected_inputs = Impl.select_inputs hole.tctx hole.examples in

          (* Generate new specs where this hole is further generalized. *)
          List.filter_map selected_inputs ~f:Impl.generate_spec
        else [])
end

let check_examples examples : bool =
  not (List.exists examples ~f:(fun (vctx, res) ->
      List.exists examples ~f:(fun (vctx', res') -> 
          Ctx.equal Expr.equal vctx vctx' && rhs <> rhs')))

module MapGeneralizerImpl = struct
  let select_inputs tctx examples =
    Ctx.filter_mapi tctx ~f:(fun ~key:name ~data:typ ->
        let typ' = normalize typ in
        match typ' with
        | App_t ("list", [elem_typ]) ->
          if List.for_all examples ~f:(fun (vctx, result) ->
              match Ctx.lookup_exn vctx name, result with
              | `List x, `List y -> List.length x = List.length y
              | `Apply _, `List _ -> true
              | _ -> false)
          && List.exists examples ~f:(fun (vctx, result) ->
              match Ctx.lookup_exn vctx name, result with
              | `List x, `List y -> x <> y
              | _ -> false)
          then Some typ' else None
        | _ -> None)
    |> Ctx.to_alist
    |> List.map ~f:(fun list_input -> [list_input])

  let deduce_examples examples list_name elem_name =
    let ex =
      List.concat_map examples ~f:(fun (vctx, result) ->
          (match Ctx.lookup_exn vctx list_name, result with
           | `List x, `List y -> List.zip_exn x y
           | _ -> [])
          |> List.map ~f:(fun (i, o) -> Ctx.bind vctx elem_name i, o))
      |> List.dedup
    in if check_examples ex then Some ex else None

  let generate_spec spec hole hole_name inputs = match inputs, hole.signature with
    | [(list_name, App_t ("list", [elem_typ]))], App_t ("list", [res_elem_typ]) ->
      let elem_name = Fresh.name "e" in
      match map_examples hole.examples list_name elem_name with
      | Some examples ->
        let hole' = {
          examples;
          signature = res_elem_typ;
          tctx = Ctx.bind hole.tctx elem_name elem_typ;
          depth = hole.depth - 1;
        } in
        let body_name = Fresh.name "f" in
        let target ctx =
          let body = Ctx.lookup_exn ctx body_name in
          let ctx' =
            Ctx.bind ctx name (`Apply (`Id map_name, [`Id list_name; `Lambda ([elem_name], body)]))
          in
          spec.target ctx'
        in
        Some { target; holes = Ctx.bind (Ctx.unbind spec.holes hole_name) body_name hole' }
      | None -> None
end

(* module MaptGeneralizerImpl = struct *)
(*   let select_inputs tctx examples = *)
(*     Ctx.filter_mapi tctx *)
(*       ~f:(fun ~key:name ~data:typ -> *)
(*           match typ |> normalize with *)
(*           | App_t ("tree", [elem_typ]) -> *)
(*             if List.for_all examples ~f:(fun (vctx, result) -> *)
(*                 match Ctx.lookup_exn vctx name, result with *)
(*                 | `Tree x, `Tree y -> Tree.equal x y ~cmp:(fun _ _ -> true) *)
(*                 | `Apply _, `Tree _ -> true *)
(*                 | _ -> false) *)
(*             && List.exists examples ~f:(fun (vctx, result) -> *)
(*                 match Ctx.lookup_exn vctx name, result with *)
(*                 | `Tree x, `Tree y -> x <> y *)
(*                 | _ -> false) *)
(*             then Some elem_typ else None *)
(*           | _ -> None) *)
(*     |> Ctx.to_alist *)
(*     |> List.map ~f:(fun list_input -> [list_input]) *)
(* end *)
