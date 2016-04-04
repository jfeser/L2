open Core.Std

open Synthesis_common
open Collections
open Hypothesis
open Infer

module Sp = Specification
module Sk = Skeleton

let type_err name type_ =
  failwiths "Unexpected type for return value of function." (name, type_)
    [%sexp_of:Ast.id * Type.t]

let spec_err name spec =
  failwiths "Unexpected spec for return value of function." (name, spec)
    [%sexp_of:Ast.id * Sp.t]

let input_err name inp =
  failwiths "Unexpected input value for function." (name, inp)
    [%sexp_of:Ast.id * Value.t]

let ret_err name ret =
  failwiths "Unexpected return value of function." (name, ret)
    [%sexp_of:Ast.id * Value.t]

let lookup_err name id =
  failwiths "Variable name not present in context." (name, id)
    [%sexp_of:Ast.id * StaticDistance.t]

module type Deduce_2_intf = sig
  val name : string
  val examples_of_io : Value.t -> Value.t -> ((Value.t * Value.t) list, unit) Result.t
end

module Make_deduce_2 (M : Deduce_2_intf) = struct
  let lambda_spec collection_id parent_spec =
    let open Result.Monad_infix in
    match parent_spec with
    | Sp.Examples exs ->
      let m_hole_exs =
        List.map (Sp.Examples.to_list exs) ~f:(fun (ctx, out_v) ->
            let in_v = match StaticDistance.Map.find ctx collection_id with
              | Some in_v -> in_v
              | None -> lookup_err M.name collection_id
            in
            Result.map (M.examples_of_io in_v out_v) ~f:(fun io ->
                List.map io ~f:(fun (i, o) -> (ctx, [i]), o)))
        |> Result.all
        >>| List.concat
        >>= fun hole_exs ->
        Result.map_error (Sp.FunctionExamples.of_list hole_exs) ~f:(fun _ -> ())
      in
      begin
        match m_hole_exs with
        | Ok hole_exs -> Sp.FunctionExamples hole_exs
        | Error () -> Sp.Bottom
      end
    | Sp.Top -> Sp.Top
    | Sp.Bottom -> Sp.Bottom
    | _ -> spec_err M.name parent_spec

  let deduce spec args =
    let open Result.Monad_infix in
    match args with
    | [ Sk.Id_h (Sk.Id.StaticDistance sd, _) as list; lambda ] when (Sk.annotation lambda) = Sp.Top ->
      let child_spec = lambda_spec sd spec in
      [ list; Sk.map_annotation lambda ~f:(fun _ -> child_spec) ]
    | _ -> args
end

module type Deduce_fold_intf = sig
  val name : string
  val is_base_case : Value.t -> bool
  val examples_of_io : Value.t -> Value.t -> ((Value.t * Value.t) list, unit) Result.t
end

module Make_deduce_fold (M : Deduce_fold_intf) = struct
  let base_spec collection_id parent_spec =
    match parent_spec with
    | Sp.Examples exs ->
      let exs = Sp.Examples.to_list exs in
      let m_base_exs =
        List.filter exs ~f:(fun (ctx, out_v) ->
            match StaticDistance.Map.find ctx collection_id with
            | Some v -> M.is_base_case v
            | None -> lookup_err (M.name ^ "-base-case") collection_id)
        |> Sp.Examples.of_list
      in
      begin
        match m_base_exs with
        | Ok base_exs -> Sp.Examples base_exs
        | Error _ -> Sp.Bottom
      end
    | Sp.Top -> Sp.Top
    | Sp.Bottom -> Sp.Bottom
    | _ -> spec_err (M.name ^ "-base-case") parent_spec

  let deduce spec args =
    let open Result.Monad_infix in
    match args with
    | [ Sk.Id_h (Sk.Id.StaticDistance sd, _) as input; lambda; base ] ->
      let b_spec = Sk.annotation base in
      let b_spec = if b_spec = Sp.Top then base_spec sd spec else b_spec in
      [ input; lambda; Sk.map_annotation base ~f:(fun _ -> b_spec ) ]
    | _ -> args
end

module Deduce_map = Make_deduce_2 (struct
    let name = "map"
    let examples_of_io in_v out_v =
      let out = match out_v with
        | `List out -> out
        | _ -> ret_err name out_v
      in
      let inp = match in_v with
        | `List inp -> inp
        | _ -> input_err name in_v
      in
      Option.value_map (List.zip inp out) ~default:(Error ()) ~f:(fun io -> Ok (io))
  end)

module Deduce_mapt = Make_deduce_2 (struct
    let name = "mapt"
    let examples_of_io in_v out_v =
      let out = match out_v with
        | `Tree out -> out
        | _ -> ret_err name out_v
      in
      let inp = match in_v with
        | `Tree inp -> inp
        | _ -> input_err name in_v
      in
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
      | (_::_ as inputs), [] -> Some (List.map inputs ~f:(fun i -> i, `Bool false))

      (* If there are some outputs and no inputs, then filter is
         not valid. *)
      | [], _::_ -> None

      | i::is, o::os when i = o ->
        Option.map (f (is, os)) ~f:(fun exs -> (i, `Bool true)::exs)

      | i::is, (_::_ as outputs) ->
        Option.map (f (is, outputs)) ~f:(fun exs -> (i, `Bool false)::exs)

    let examples_of_io in_v out_v =
      let out = match out_v with
        | `List out -> out
        | _ -> ret_err name out_v
      in
      let inp = match in_v with
        | `List inp -> inp
        | _ -> input_err name in_v
      in
      Option.value_map (f (inp, out)) ~default:(Error ()) ~f:(fun io -> Ok io)
  end)

module Deduce_foldl = Make_deduce_fold (struct
    let name = "foldl"
    let is_base_case v = v = `List []
    let examples_of_io _ _ = Error ()
  end)

module Deduce_foldr = Make_deduce_fold (struct
    let name = "foldr"
    let is_base_case v = v = `List []
    let examples_of_io _ _ = Error ()
  end)

module Deduce_foldt = Make_deduce_fold (struct
    let name = "foldt"
    let is_base_case v = v = `Tree Tree.Empty
    let examples_of_io _ _ = Error ()
  end)

let deduce_lambda lambda spec =
  let (num_args, body) = lambda in
  if (Sk.annotation body) = Sp.Top then
    let child_spec = match Sp.increment_scope spec with
      | Sp.FunctionExamples exs ->
        let arg_names = StaticDistance.args num_args in
        let child_exs =
          Sp.FunctionExamples.to_list exs
          |> List.map ~f:(fun ((in_ctx, in_args), out) ->
              let value_ctx = StaticDistance.Map.of_alist_exn (List.zip_exn arg_names in_args) in
              let in_ctx = StaticDistance.Map.merge value_ctx in_ctx ~f:(fun ~key:_ v ->
                  match v with
                  | `Both (x, _)
                  | `Left x
                  | `Right x -> Some x)
              in
              (in_ctx, out))
          |> Sp.Examples.of_list_exn
        in
        Sp.Examples child_exs
      | Sp.Bottom -> Sp.Bottom
      | Sp.Top -> Sp.Top
      | _ -> spec_err "<lambda>" spec
    in
    (num_args, Sk.map_annotation body ~f:(fun _ -> child_spec))
  else lambda

let rec push_specs (skel: Specification.t Skeleton.t) : Specification.t Skeleton.t Option.t =
  let open Option.Monad_infix in
  match skel with
  | Sk.Num_h (_, s)
  | Sk.Bool_h (_, s)
  | Sk.Id_h (_, s)
  | Sk.Hole_h (_, s) -> if s = Sp.Bottom then None else Some skel
  | Sk.List_h (l, s) ->
    let m_l = List.map l ~f:push_specs |> Option.all in
    m_l >>| fun l -> Sk.List_h (l, s)
  | Sk.Tree_h (t, s) ->
    let m_t = Tree.map t ~f:push_specs |> Tree.all in
    m_t >>| fun t -> Sk.Tree_h (t, s)
  | Sk.Let_h ((bound, body), s) ->
    let m_bound = push_specs bound in
    let m_body = push_specs body in
    m_bound >>= fun bound -> m_body >>| fun body -> Sk.Let_h ((bound, body), s)
  | Sk.Lambda_h (lambda, s) ->
    let (num_args, body) = deduce_lambda lambda s in
    let m_body = push_specs body in
    m_body >>| fun body -> Sk.Lambda_h ((num_args, body), s)
  | Sk.Op_h ((op, args), s) ->
    let m_args = List.map args ~f:push_specs |> Option.all in
    m_args >>| fun args -> Sk.Op_h ((op, args), s)
  | Sk.Apply_h ((func, args), s) ->
    let args = match func with
      | Sk.Id_h (Sk.Id.Name "map", _) -> Deduce_map.deduce s args
      | Sk.Id_h (Sk.Id.Name "mapt", _) -> Deduce_mapt.deduce s args
      | Sk.Id_h (Sk.Id.Name "filter", _) -> Deduce_filter.deduce s args
      | Sk.Id_h (Sk.Id.Name "foldl", _) -> Deduce_foldl.deduce s args
      | Sk.Id_h (Sk.Id.Name "foldr", _) -> Deduce_foldr.deduce s args
      | Sk.Id_h (Sk.Id.Name "foldt", _) -> Deduce_foldt.deduce s args
      | _ -> args        
    in
    let m_args =
      if List.exists args ~f:(fun a -> Sk.annotation a = Sp.Bottom) then None else
        Option.all (List.map args ~f:push_specs)
    in
    let m_func = push_specs func in
    m_args >>= fun args -> m_func >>| fun func -> Sk.Apply_h ((func, args), s)
