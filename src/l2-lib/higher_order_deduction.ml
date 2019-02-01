open Core
open Collections
open Hypothesis
module Sp = Specification
module Sk = Skeleton

let spec_err name spec =
  failwiths "Unexpected spec for return value of function." (name, spec)
    [%sexp_of: Ast.id * Sp.t]

let input_err name inp =
  failwiths "Unexpected input value for function." (name, inp)
    [%sexp_of: Ast.id * Value.t]

let ret_err name ret =
  failwiths "Unexpected return value of function." (name, ret)
    [%sexp_of: Ast.id * Value.t]

let lookup_err name id =
  failwiths "Variable name not present in context." (name, id)
    [%sexp_of: Ast.id * StaticDistance.t]

module type Deduce_2_intf = sig
  val name : string

  val examples_of_io :
    Value.t -> Value.t -> ((Value.t * Value.t) list, unit) Result.t
end

module Make_deduce_2 (M : Deduce_2_intf) = struct
  let lambda_spec collection_id parent_spec =
    let open Result.Monad_infix in
    match Sp.data parent_spec with
    | Examples.Examples exs -> (
        let m_hole_exs =
          List.map (Examples.to_list exs) ~f:(fun (ctx, out_v) ->
              let in_v =
                match StaticDistance.Map.find ctx collection_id with
                | Some in_v -> in_v
                | None -> lookup_err M.name collection_id
              in
              Result.map (M.examples_of_io in_v out_v) ~f:(fun io ->
                  List.map io ~f:(fun (i, o) -> ((ctx, [i]), o)) ) )
          |> Result.all >>| List.concat
          >>= fun hole_exs ->
          Result.map_error (FunctionExamples.of_list hole_exs) ~f:(fun _ -> ())
        in
        match m_hole_exs with
        | Ok hole_exs -> FunctionExamples.to_spec hole_exs
        | Error () -> Sp.bottom )
    | Sp.Top -> Sp.top
    | Sp.Bottom -> Sp.bottom
    | Inputs.Inputs _ -> Sp.top
    | _ -> spec_err M.name parent_spec

  let deduce spec args =
    match args with
    | [list; lambda] when Sp.equal (Sk.spec lambda) Sp.top -> (
      match Sk.ast list with
      | Sk.Id (Sk.Id.StaticDistance sd) ->
          let child_spec = lambda_spec sd spec in
          [list; Sk.replace_spec lambda child_spec]
      | _ -> args )
    | _ -> args
end

module type Deduce_fold_intf = sig
  val name : string

  val is_base_case : Value.t -> bool
end

module Make_deduce_fold (M : Deduce_fold_intf) = struct
  let base_spec collection_id parent_spec =
    match Sp.data parent_spec with
    | Examples.Examples exs -> (
        let exs = Examples.to_list exs in
        let m_base_exs =
          List.filter exs ~f:(fun (ctx, _) ->
              match StaticDistance.Map.find ctx collection_id with
              | Some v -> M.is_base_case v
              | None -> lookup_err (M.name ^ "-base-case") collection_id )
          |> Examples.of_list
        in
        match m_base_exs with
        | Ok base_exs -> Examples.to_spec base_exs
        | Error _ -> Sp.bottom )
    | Sp.Top -> Sp.top
    | Sp.Bottom -> Sp.bottom
    | _ -> spec_err (M.name ^ "-base-case") parent_spec

  let deduce spec args =
    match args with
    | [input; lambda; base] -> (
      match Sk.ast input with
      | Sk.Id (Sk.Id.StaticDistance sd) ->
          let b_spec = Sk.spec base in
          let b_spec =
            if Sp.equal b_spec Sp.top then base_spec sd spec else b_spec
          in
          [input; lambda; Sk.replace_spec base b_spec]
      | _ -> args )
    | _ -> args
end

module Deduce_map = Make_deduce_2 (struct
  let name = "map"

  let examples_of_io in_v out_v =
    let out = match out_v with `List out -> out | _ -> ret_err name out_v in
    let inp = match in_v with `List inp -> inp | _ -> input_err name in_v in
    Option.value_map (List.zip inp out) ~default:(Error ()) ~f:(fun io -> Ok io)
end)

module Deduce_mapt = Make_deduce_2 (struct
  let name = "mapt"

  let examples_of_io in_v out_v =
    let out = match out_v with `Tree out -> out | _ -> ret_err name out_v in
    let inp = match in_v with `Tree inp -> inp | _ -> input_err name in_v in
    Option.map (Tree.zip inp out) ~f:(fun io -> Ok (Tree.flatten io))
    |> Option.value ~default:(Error ())
end)

module Deduce_filter = Make_deduce_2 (struct
  let name = "filter"

  let rec f = function
    (* If there are no inputs and no outputs, then there are no
         examples, but filter is valid. *)
    | [], [] -> Some []
    (* If there are some inputs and no outputs, then the inputs
         must have been filtered. *)
    | (_ :: _ as inputs), [] ->
        Some (List.map inputs ~f:(fun i -> (i, `Bool false)))
    (* If there are some outputs and no inputs, then filter is
         not valid. *)
    | [], _ :: _ -> None
    | i :: is, o :: os when i = o ->
        Option.map (f (is, os)) ~f:(fun exs -> (i, `Bool true) :: exs)
    | i :: is, (_ :: _ as outputs) ->
        Option.map (f (is, outputs)) ~f:(fun exs -> (i, `Bool false) :: exs)

  let examples_of_io in_v out_v =
    let out = match out_v with `List out -> out | _ -> ret_err name out_v in
    let inp = match in_v with `List inp -> inp | _ -> input_err name in_v in
    Option.value_map (f (inp, out)) ~default:(Error ()) ~f:(fun io -> Ok io)
end)

module Deduce_foldl = Make_deduce_fold (struct
  let name = "foldl"

  let is_base_case v = v = `List []
end)

module Deduce_foldr = Make_deduce_fold (struct
  let name = "foldr"

  let is_base_case v = v = `List []
end)

module Deduce_foldt = Make_deduce_fold (struct
  let name = "foldt"

  let is_base_case v = v = `Tree Tree.Empty
end)

let deduce_lambda lambda spec =
  let num_args, body = lambda in
  if Sp.equal (Sk.spec body) Sp.top then
    let child_spec = Sp.increment_scope spec in
    let child_spec =
      match Sp.data child_spec with
      | FunctionExamples.FunctionExamples exs ->
          let arg_names = StaticDistance.args num_args in
          let child_exs =
            FunctionExamples.to_list exs
            |> List.map ~f:(fun ((in_ctx, in_args), out) ->
                   let value_ctx =
                     StaticDistance.Map.of_alist_exn
                       (List.zip_exn arg_names in_args)
                   in
                   let in_ctx =
                     StaticDistance.Map.merge value_ctx in_ctx ~f:(fun ~key:_ v ->
                         match v with `Both (x, _) | `Left x | `Right x -> Some x )
                   in
                   (in_ctx, out) )
            |> Examples.of_list_exn
          in
          Examples.to_spec child_exs
      | Sp.Bottom -> Sp.bottom
      | Sp.Top -> Sp.top
      | Inputs.Inputs _ -> Sp.top
      | _ -> spec_err "<lambda>" spec
    in
    (num_args, Sk.replace_spec body child_spec)
  else lambda

let rec push_specs (skel : Skeleton.t) : Skeleton.t Option.t =
  let open Option.Monad_infix in
  let spec = Sk.spec skel in
  match Sk.ast skel with
  | Sk.Num _ | Sk.Bool _ | Sk.Id _ | Sk.Hole _ ->
      if Sp.equal spec Sp.bottom then None else Some skel
  | Sk.List l ->
      let m_l = List.map l ~f:push_specs |> Option.all in
      m_l >>| fun l -> Sk.list l spec
  | Sk.Tree t ->
      let m_t = Tree.map t ~f:push_specs |> Tree.all in
      m_t >>| fun t -> Sk.tree t spec
  | Sk.Let {bound; body} ->
      let m_bound = push_specs bound in
      let m_body = push_specs body in
      m_bound >>= fun bound -> m_body >>| fun body -> Sk.let_ bound body spec
  | Sk.Lambda {num_args; body} ->
      let num_args, body = deduce_lambda (num_args, body) spec in
      let m_body = push_specs body in
      m_body >>| fun body -> Sk.lambda num_args body spec
  | Sk.Op {op; args} ->
      let m_args = List.map args ~f:push_specs |> Option.all in
      m_args >>| fun args -> Sk.op op args spec
  | Sk.Apply {func; args} ->
      let args =
        match Sk.ast func with
        | Sk.Id (Sk.Id.Name "map") -> Deduce_map.deduce spec args
        | Sk.Id (Sk.Id.Name "mapt") -> Deduce_mapt.deduce spec args
        | Sk.Id (Sk.Id.Name "filter") -> Deduce_filter.deduce spec args
        | Sk.Id (Sk.Id.Name "foldl") -> Deduce_foldl.deduce spec args
        | Sk.Id (Sk.Id.Name "foldr") -> Deduce_foldr.deduce spec args
        | Sk.Id (Sk.Id.Name "foldt") -> Deduce_foldt.deduce spec args
        | _ -> args
      in
      let m_args =
        if List.exists args ~f:(fun a -> Sp.equal (Sk.spec a) Sp.bottom) then None
        else Option.all (List.map args ~f:push_specs)
      in
      let m_func = push_specs func in
      m_args >>= fun args -> m_func >>| fun func -> Sk.apply func args spec
