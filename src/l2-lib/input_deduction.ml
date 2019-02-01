open Core
open Collections
open Hypothesis
module Sk = Skeleton
module Sp = Specification

let get_curr_spec : Sp.t -> Sk.t -> Sp.t =
 fun parent_spec sk ->
  let curr_spec = Sk.spec sk in
  if Sp.equal Sp.top curr_spec then parent_spec else curr_spec

let get_child_spec : Sp.t -> Sk.t -> Sp.t =
 fun parent_spec sk ->
  let sp = Sk.spec sk in
  match sp.Sp.data with
  | Examples.Examples exs -> Inputs.of_examples exs |> Inputs.to_spec
  | Inputs.Inputs _ -> sp
  | _ -> parent_spec

let rec push_specs parent_spec sk =
  let curr_spec = get_curr_spec parent_spec sk in
  let child_spec = get_child_spec parent_spec sk in
  match Sk.ast sk with
  | Sk.Num _ | Sk.Bool _ | Sk.Id _ | Sk.Hole _ -> Sk.replace_spec sk curr_spec
  | Sk.List l -> Sk.list (List.map l ~f:(push_specs child_spec)) curr_spec
  | Sk.Tree t -> Sk.tree (Tree.map t ~f:(push_specs child_spec)) curr_spec
  | Sk.Let {bound; body} ->
      (* Let introduces a new scope, so we can't use the parent
       context. *)
      let bound' = push_specs Sp.top bound in
      let body' = push_specs Sp.top body in
      Sk.let_ bound' body' curr_spec
  | Sk.Lambda {num_args; body} ->
      (* Lambdas introduce a new scope, so we can't use the parent
       context. Also, we can't use Inputs specs on function typed
       skeletons. *)
      Sk.lambda num_args (push_specs Sp.top body) (Sk.spec sk)
  | Sk.Op {op; args} ->
      Sk.op op (List.map args ~f:(push_specs child_spec)) curr_spec
  | Sk.Apply {func; args} ->
      let func' = push_specs child_spec func in
      let args' = List.map ~f:(push_specs child_spec) args in
      Sk.apply func' args' curr_spec

let push_specs : Synthesis_common.Deduction.t =
 fun sk -> push_specs Sp.top sk |> Option.some
