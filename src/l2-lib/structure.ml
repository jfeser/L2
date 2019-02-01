open Core
open Ast
open Collections
open Infer
open Util

type hole = {examples: (example * expr Ctx.t) list; signature: typ; tctx: typ Ctx.t}

let ctx_merge outer_ctx inner_ctx =
  Ctx.merge outer_ctx inner_ctx ~f:(fun ~key:_ value ->
      match value with
      | `Both (_, ictx_v) -> Some ictx_v
      | `Left octx_v -> Some octx_v
      | `Right ictx_v -> Some ictx_v )

module Cost = struct
  type t =
    {foldr: int; foldl: int; foldt: int; rec_: int; map: int; mapt: int; filter: int}

  let default = {foldr= 8; foldl= 8; foldt= 8; rec_= 40; map= 7; mapt= 7; filter= 7}

  let flat = {foldr= 1; foldl= 1; foldt= 1; rec_= 1; map= 1; mapt= 1; filter= 1}
end

module Spec = struct
  type t = {target: expr Ctx.t -> expr -> expr; holes: hole Ctx.t; cost: int}

  let to_string (spec : t) : string =
    let (hole_bodies : expr Ctx.t) =
      Ctx.mapi spec.holes ~f:(fun ~key:name ~data:_ -> `Id name)
    in
    spec.target hole_bodies (`Id "_") |> Expr.to_string

  (* Map is an appropriate implementation when one of the inputs is a
     list and the output is a list of the same length. *)
  let map_bodies ?(deduce_examples = true) ?(cost = Cost.default) (spec : t) :
      t list =
    let map_example lambda_name input result : example =
      (`Apply (`Id lambda_name, [input]), result)
    in
    let map_examples examples lambda_name lambda_arg_name =
      let ex =
        List.concat_map examples ~f:(fun ((_, result), vctx) ->
            ( match (Ctx.lookup_exn vctx lambda_arg_name, result) with
            | `List x, `List y -> List.zip_exn x y
            | `Tree x, `Tree y -> List.zip_exn (Tree.flatten x) (Tree.flatten y)
            | _ -> [] )
            |> List.map ~f:(fun (i, o) -> (map_example lambda_name i o, vctx)) )
        |> List.dedup_and_sort ~compare:Polymorphic_compare.compare
      in
      if Example.check ex then if deduce_examples then Some ex else Some []
      else None
    in
    let fill name hole =
      match hole.signature with
      | Arrow_t (arg_typs, App_t ("tree", [res_elem_typ]))
       |Arrow_t (arg_typs, App_t ("list", [res_elem_typ])) ->
          let arg_names = List.map arg_typs ~f:(fun _ -> Fresh.name "x") in
          let tctx =
            ctx_merge hole.tctx (List.zip_exn arg_names arg_typs |> Ctx.of_alist_exn)
          in
          let examples =
            List.map hole.examples ~f:(fun (ex, ovctx) ->
                (ex, ctx_merge ovctx (Example.to_vctx ex arg_names)) )
          in
          let tree_args =
            Ctx.filter_mapi tctx ~f:(fun ~key:name ~data:typ ->
                match typ |> normalize with
                | App_t ("tree", [elem_typ]) ->
                    if
                      List.for_all examples ~f:(fun ((_, result), vctx) ->
                          match (Ctx.lookup_exn vctx name, result) with
                          | `Tree x, `Tree y ->
                              Tree.equal x y ~equal:(fun _ _ -> true)
                          | `Apply _, `Tree _ -> true
                          | _ -> false )
                    then Some elem_typ
                    else None
                | _ -> None )
            |> Ctx.to_alist
          in
          let list_args =
            Ctx.filter_mapi tctx ~f:(fun ~key:name ~data:typ ->
                match typ |> normalize with
                | App_t ("list", [elem_typ]) ->
                    if
                      List.for_all examples ~f:(fun ((_, result), vctx) ->
                          match (Ctx.lookup_exn vctx name, result) with
                          | `List x, `List y -> List.length x = List.length y
                          | `Apply _, `List _ -> true
                          | _ -> false )
                    then Some elem_typ
                    else None
                | _ -> None )
            |> Ctx.to_alist
          in
          let map_specs args map_name cost =
            List.filter_map args ~f:(fun (input_name, input_elem_typ) ->
                let lambda_name = Fresh.name "f" in
                match map_examples examples lambda_name input_name with
                | Some examples ->
                    let hole' =
                      { examples
                      ; tctx
                      ; signature= Arrow_t ([input_elem_typ], res_elem_typ) }
                    in
                    let target ctx =
                      let body = Ctx.lookup_exn ctx lambda_name in
                      let ctx' =
                        Ctx.bind ctx name
                          (`Lambda
                            ( arg_names
                            , `Apply (`Id map_name, [`Id input_name; body]) ))
                      in
                      spec.target ctx'
                    in
                    Some
                      { target
                      ; holes=
                          Ctx.bind (Ctx.unbind spec.holes name) lambda_name hole'
                      ; cost= spec.cost + cost }
                | None -> None )
          in
          map_specs tree_args "mapt" cost.Cost.mapt
          @ map_specs list_args "map" cost.Cost.map
      | _ -> []
    in
    Ctx.to_alist spec.holes
    |> List.concat_map ~f:(fun (name, hole) -> fill name hole)

  let filter_bodies ?(deduce_examples = true) ?(cost = Cost.default) (spec : t) :
      t list =
    let filter_example lambda_name input result =
      (`Apply (`Id lambda_name, [input]), `Bool result)
    in
    let filter_examples examples lambda_name list_name =
      let ex =
        List.concat_map examples ~f:(fun ((_, result), vctx) ->
            match (Ctx.lookup_exn vctx list_name, result) with
            | `List x, `List y ->
                let rec f inputs outputs =
                  match (inputs, outputs) with
                  | [], [] -> []
                  (* This is a hack. In this case, there
                   is more in the output list than there
                   was in the input list. Return a pair of
                   conflicting examples that will be picked
                   up by the example checker. *)
                  | [], _ :: _ ->
                      [ filter_example lambda_name (`Num 1) false
                      ; filter_example lambda_name (`Num 1) true ]
                  | i :: is, [] -> filter_example lambda_name i false :: f is []
                  | i :: is, o :: os ->
                      if i = o then filter_example lambda_name i true :: f is os
                      else filter_example lambda_name i false :: f is outputs
                in
                f x y |> List.map ~f:(fun ex -> (ex, vctx))
            | _ -> [] )
        |> List.dedup_and_sort ~compare:Polymorphic_compare.compare
      in
      if Example.check ex then if deduce_examples then Some ex else Some []
      else None
    in
    let fill name hole =
      let cost = cost.Cost.filter in
      match hole.signature with
      | Arrow_t (arg_typs, App_t ("list", [res_elem_typ])) ->
          let arg_names = List.map arg_typs ~f:(fun _ -> Fresh.name "x") in
          let tctx =
            ctx_merge hole.tctx (List.zip_exn arg_names arg_typs |> Ctx.of_alist_exn)
          in
          let examples =
            List.map hole.examples ~f:(fun (ex, ovctx) ->
                (ex, ctx_merge ovctx (Example.to_vctx ex arg_names)) )
          in
          (* Select all list arguments which are a superset of the result
           for every example and a strict superset of the result for at
           least one example. *)
          tctx
          |> Ctx.filter_mapi ~f:(fun ~key:name ~data:typ ->
                 match typ |> normalize with
                 | App_t ("list", [elem_typ]) when elem_typ = res_elem_typ ->
                     if
                       List.for_all examples ~f:(fun ((_, result), vctx) ->
                           match (Ctx.lookup_exn vctx name, result) with
                           | `List x, `List y -> Util.superset x y
                           | `Apply _, `List _ -> true
                           | _ -> failwith "Examples do not have a consistent type."
                       )
                     then Some elem_typ
                     else None
                 | _ -> None )
          |> Ctx.to_alist
          |> List.filter_map ~f:(fun (input_name, input_elem_typ) ->
                 let lambda_name = Fresh.name "f" in
                 match filter_examples examples lambda_name input_name with
                 | Some examples ->
                     let hole' =
                       { examples
                       ; tctx
                       ; signature= Arrow_t ([input_elem_typ], Const_t Bool_t) }
                     in
                     let target ctx =
                       let body = Ctx.lookup_exn ctx lambda_name in
                       let expr =
                         `Lambda
                           (arg_names, `Apply (`Id "filter", [`Id input_name; body]))
                       in
                       let ctx' = Ctx.bind ctx name expr in
                       spec.target ctx'
                     in
                     Some
                       { target
                       ; holes=
                           Ctx.bind (Ctx.unbind spec.holes name) lambda_name hole'
                       ; cost= spec.cost + cost }
                 | None -> None )
      | _ -> []
    in
    Ctx.to_alist spec.holes
    |> List.concat_map ~f:(fun (name, hole) -> fill name hole)

  let extract_base_case examples input_name : expr option =
    let base_cases =
      examples
      |> List.filter_map ~f:(fun ((_, result), vctx) ->
             match Ctx.lookup_exn vctx input_name with
             | `List [] | `Tree Tree.Empty -> Some result
             | _ -> None )
      |> List.dedup_and_sort ~compare:Polymorphic_compare.compare
    in
    match base_cases with [] -> None | [base] -> Some base | _ :: _ :: _ -> None

  (* Foldl and foldr are the most general functions. They are
     appropriate whenever one of the inputs is a list. If another of the
     arguments can act as a base case, it is used. Otherwise, a default
     base case is used for each type. *)
  let fold_bodies ?(deduce_examples = true) ?(infer_base = false)
      ?(cost = Cost.default) (spec : t) : t list =
    let init_examples examples init_name list_name =
      let ex =
        List.filter_map examples ~f:(fun ((_, result), vctx) ->
            match Ctx.lookup_exn vctx list_name with
            | `List [] -> Some ((`Id init_name, result), vctx)
            | _ -> None )
      in
      if Example.check ex then if deduce_examples then Some ex else Some []
      else None
    in
    let foldr_examples examples lambda_name list_name init_expr =
      let apply_lambda acc elem = `Apply (`Id lambda_name, [acc; elem]) in
      let ex =
        List.filter_map examples ~f:(fun ((_, result), vctx) ->
            match Ctx.lookup_exn vctx list_name with
            | `List [x] -> Some ((apply_lambda init_expr x, result), vctx)
            | `List (x :: xs) ->
                let acc_result_m =
                  List.find_map examples ~f:(fun ((_, result), vctx) ->
                      match Ctx.lookup_exn vctx list_name with
                      | `List xs' when xs = xs' -> Some result
                      | _ -> None )
                in
                Option.map acc_result_m ~f:(fun acc_result ->
                    ((apply_lambda acc_result x, result), vctx) )
            | _ -> None )
      in
      if Example.check ex then if deduce_examples then Some ex else Some []
      else None
    in
    let foldl_examples examples lambda_name list_name init_expr =
      let apply_lambda acc elem = `Apply (`Id lambda_name, [acc; elem]) in
      let ex =
        List.filter_map examples ~f:(fun ((_, result), vctx) ->
            match Ctx.lookup_exn vctx list_name with
            | `List [x] -> Some ((apply_lambda init_expr x, result), vctx)
            | `List (r :: rs) -> (
              match List.rev (r :: rs) with
              | x :: xs ->
                  let acc_result_m =
                    List.find_map examples ~f:(fun ((_, result), vctx) ->
                        match Ctx.lookup_exn vctx list_name with
                        | `List rs' when xs = List.rev rs' -> Some result
                        | _ -> None )
                  in
                  Option.map acc_result_m ~f:(fun acc_result ->
                      ((apply_lambda acc_result x, result), vctx) )
              | [] -> failwith "BUG: This should never happen." )
            | _ -> None )
      in
      if Example.check ex then if deduce_examples then Some ex else Some []
      else None
    in
    let fill name hole : t list =
      let foldl_cost = cost.Cost.foldl in
      let foldr_cost = cost.Cost.foldr in
      match hole.signature with
      | Arrow_t (arg_typs, res_typ) ->
          let arg_names = List.map arg_typs ~f:(fun _ -> Fresh.name "x") in
          let tctx =
            ctx_merge hole.tctx (List.zip_exn arg_names arg_typs |> Ctx.of_alist_exn)
          in
          let examples =
            List.map hole.examples ~f:(fun (ex, ovctx) ->
                (ex, ctx_merge ovctx (Example.to_vctx ex arg_names)) )
          in
          (* Create a list of tuples (list name, list element type) from
           the type context. *)
          let lists =
            Ctx.to_alist tctx
            |> List.filter_map ~f:(fun (name, typ) ->
                   match typ |> normalize with
                   | App_t ("list", [elem_typ]) -> Some (name, elem_typ)
                   | _ -> None )
          in
          List.concat_map lists ~f:(fun (input_name, input_elem_typ) ->
              let init_name = Fresh.name "i" in
              match init_examples examples init_name input_name with
              | Some init_exs ->
                  let holes' = Ctx.unbind spec.holes name in
                  let lambda_name = Fresh.name "f" in
                  let lambda_hole =
                    { tctx
                    ; examples= []
                    ; signature= Arrow_t ([res_typ; input_elem_typ], res_typ) }
                  in
                  let init_hole = {tctx; examples= init_exs; signature= res_typ} in
                  let baseless_target fold_name ctx =
                    let body = Ctx.lookup_exn ctx lambda_name in
                    let init = Ctx.lookup_exn ctx init_name in
                    let expr =
                      `Lambda
                        ( arg_names
                        , `Apply (`Id fold_name, [`Id input_name; body; init]) )
                    in
                    let ctx' = Ctx.bind ctx name expr in
                    spec.target ctx'
                  in
                  let baseless_holes =
                    Ctx.bind
                      (Ctx.bind holes' lambda_name lambda_hole)
                      init_name init_hole
                  in
                  let baseless_specs =
                    [ { target= baseless_target "foldl"
                      ; holes= baseless_holes
                      ; cost= spec.cost + foldl_cost }
                    ; { target= baseless_target "foldr"
                      ; holes= baseless_holes
                      ; cost= spec.cost + foldr_cost } ]
                  in
                  if infer_base then
                    match extract_base_case examples input_name with
                    | Some base -> (
                        let target fold_name ctx =
                          let body = Ctx.lookup_exn ctx lambda_name in
                          let expr =
                            `Lambda
                              ( arg_names
                              , `Apply (`Id fold_name, [`Id input_name; body; base])
                              )
                          in
                          let ctx' = Ctx.bind ctx name expr in
                          spec.target ctx'
                        in
                        ( match
                            foldl_examples examples lambda_name input_name base
                          with
                        | Some examples ->
                            [ { target= target "foldl"
                              ; holes=
                                  Ctx.bind holes' lambda_name
                                    {lambda_hole with examples}
                              ; cost= spec.cost + foldl_cost - 1 } ]
                        | None -> [] )
                        @
                        match
                          foldr_examples examples lambda_name input_name base
                        with
                        | Some examples ->
                            [ { target= target "foldr"
                              ; holes=
                                  Ctx.bind holes' lambda_name
                                    {lambda_hole with examples}
                              ; cost= spec.cost + foldr_cost - 1 } ]
                        | None -> [] )
                    | None -> baseless_specs
                  else baseless_specs
              | None -> [] )
      | _ -> []
    in
    Ctx.to_alist spec.holes
    |> List.concat_map ~f:(fun (name, hole) -> fill name hole)

  let foldt_bodies ?(deduce_examples = true) ?(infer_base = false)
      ?(cost = Cost.default) (spec : t) : t list =
    let init_examples examples init_name input_name =
      let ex =
        List.filter_map examples ~f:(fun ((_, result), vctx) ->
            match Ctx.lookup_exn vctx input_name with
            | `Tree Tree.Empty -> Some ((`Id init_name, result), vctx)
            | _ -> None )
      in
      if Example.check ex then if deduce_examples then Some ex else Some []
      else None
    in
    let fill name hole : t list =
      match hole.signature with
      | Arrow_t (arg_typs, res_typ) ->
          let arg_names = List.map arg_typs ~f:(fun _ -> Fresh.name "x") in
          let tctx =
            ctx_merge hole.tctx (List.zip_exn arg_names arg_typs |> Ctx.of_alist_exn)
          in
          let examples =
            List.map hole.examples ~f:(fun (ex, ovctx) ->
                (ex, ctx_merge ovctx (Example.to_vctx ex arg_names)) )
          in
          let trees =
            tctx
            |> Ctx.filter_mapi ~f:(fun ~key:_ ~data:typ ->
                   match typ |> normalize with
                   | App_t ("tree", [elem_typ]) -> Some elem_typ
                   | _ -> None )
            |> Ctx.to_alist
          in
          let cost = cost.Cost.foldt in
          List.concat_map trees ~f:(fun (input_name, input_elem_typ) ->
              let init_name = Fresh.name "i" in
              match init_examples examples init_name input_name with
              | Some init_exs ->
                  let holes' = Ctx.unbind spec.holes name in
                  let lambda_name = Fresh.name "f" in
                  let lambda_hole =
                    { tctx
                    ; examples= []
                    ; signature=
                        Arrow_t
                          ([App_t ("list", [res_typ]); input_elem_typ], res_typ) }
                  in
                  let init_hole = {tctx; examples= init_exs; signature= res_typ} in
                  let baseless_target ctx =
                    let body = Ctx.lookup_exn ctx lambda_name in
                    let init = Ctx.lookup_exn ctx init_name in
                    let expr =
                      `Lambda
                        ( arg_names
                        , `Apply (`Id "foldt", [`Id input_name; body; init]) )
                    in
                    let ctx' = Ctx.bind ctx name expr in
                    spec.target ctx'
                  in
                  let baseless_specs =
                    [ { target= baseless_target
                      ; holes=
                          Ctx.bind
                            (Ctx.bind holes' lambda_name lambda_hole)
                            init_name init_hole
                      ; cost= spec.cost + cost } ]
                  in
                  if infer_base then
                    match extract_base_case examples input_name with
                    | Some base ->
                        let target ctx =
                          let body = Ctx.lookup_exn ctx lambda_name in
                          let expr =
                            `Lambda
                              ( arg_names
                              , `Apply (`Id "foldt", [`Id input_name; body; base])
                              )
                          in
                          let ctx' = Ctx.bind ctx name expr in
                          spec.target ctx'
                        in
                        [ { target
                          ; holes= Ctx.bind holes' lambda_name lambda_hole
                          ; cost= spec.cost + cost } ]
                    | None -> baseless_specs
                  else baseless_specs
              | None -> [] )
      | _ -> []
    in
    Ctx.to_alist spec.holes
    |> List.concat_map ~f:(fun (name, hole) -> fill name hole)

  let recurs_bodies ?(deduce_examples = true) ?(cost = Cost.default) (spec : t) :
      t list =
    let base_examples examples base_name input_name =
      let ex =
        List.filter_map examples ~f:(fun ((_, result), vctx) ->
            match Ctx.lookup_exn vctx input_name with
            | `List [] -> Some ((`Id base_name, result), vctx)
            | _ -> None )
      in
      if Example.check ex then if deduce_examples then Some ex else Some []
      else None
    in
    let recurs_examples examples recurs_name input_name =
      let ex =
        List.filter_map examples ~f:(fun ((_, result), vctx) ->
            match Ctx.lookup_exn vctx input_name with
            | `List (x :: xs) ->
                Some ((`Apply (`Id recurs_name, [x; `List xs]), result), vctx)
            | _ -> None )
      in
      if Example.check ex then if deduce_examples then Some ex else Some []
      else None
    in
    let fill name hole : t list =
      match hole.signature with
      | Arrow_t (arg_typs, res_typ) ->
          let arg_names = List.map arg_typs ~f:(fun _ -> Fresh.name "x") in
          let tctx =
            ctx_merge hole.tctx (List.zip_exn arg_names arg_typs |> Ctx.of_alist_exn)
          in
          let examples =
            List.map hole.examples ~f:(fun (ex, ovctx) ->
                (ex, ctx_merge ovctx (Example.to_vctx ex arg_names)) )
          in
          let lists =
            tctx
            |> Ctx.filter_mapi ~f:(fun ~key:_ ~data:typ ->
                   match typ |> normalize with
                   | App_t ("list", [elem_typ]) -> Some elem_typ
                   | _ -> None )
            |> Ctx.to_alist
          in
          let cost = cost.Cost.rec_ in
          List.filter_map lists ~f:(fun (input_name, input_elem_typ) ->
              let base_name = Fresh.name "f" in
              let recurs_name = Fresh.name "f" in
              match
                ( base_examples examples base_name input_name
                , recurs_examples examples recurs_name input_name )
              with
              | Some base_exs, Some recurs_exs ->
                  let base_hole = {tctx; examples= base_exs; signature= res_typ} in
                  let recurs_hole =
                    { examples= recurs_exs
                    ; signature=
                        Arrow_t
                          ( [input_elem_typ; App_t ("list", [input_elem_typ])]
                          , res_typ )
                    ; tctx= Ctx.bind tctx recurs_name hole.signature }
                  in
                  let target ctx =
                    let base = Ctx.lookup_exn ctx base_name in
                    let recurs = Ctx.lookup_exn ctx recurs_name in
                    let expr =
                      `Lambda
                        ( arg_names
                        , `Let
                            ( recurs_name
                            , `Lambda
                                ( arg_names
                                , `Op
                                    ( If
                                    , [ `Op (Eq, [`Id input_name; `List []])
                                      ; base
                                      ; `Apply
                                          ( recurs
                                          , [ `Op (Car, [`Id input_name])
                                            ; `Op (Cdr, [`Id input_name]) ] ) ] ) )
                            , `Apply (`Id recurs_name, [`Id input_name]) ) )
                    in
                    let ctx' = Ctx.bind ctx name expr in
                    spec.target ctx'
                  in
                  Some
                    { target
                    ; holes=
                        Ctx.bind
                          (Ctx.bind (Ctx.unbind spec.holes name) recurs_name
                             recurs_hole)
                          base_name base_hole
                    ; cost= spec.cost + cost }
              | _ -> None )
      | _ -> []
    in
    Ctx.to_alist spec.holes
    |> List.concat_map ~f:(fun (name, hole) -> fill name hole)
end
