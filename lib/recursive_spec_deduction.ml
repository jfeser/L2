open Core
open Synthesis_common
open Hypothesis
open Collections
module Sk = Skeleton
module Sp = Specification

exception Bottom

let push_specs_exn : Sk.t -> unit =
  let rec push sps sk =
    let spec = Sk.spec sk in
    let sps =
      match Sp.data spec with
      | Sp.Top -> sps
      | Examples.Examples _ | FunctionExamples.FunctionExamples _ ->
          if Sp.Set.mem sps spec then raise Bottom ;
          Sp.Set.add sps spec
      | Sp.Bottom -> raise Bottom
      | _ -> sps
    in
    match Sk.ast sk with
    | Sk.Num _ | Sk.Bool _ | Sk.Id _ | Sk.Hole _ -> ()
    | Sk.List l -> List.iter l ~f:(push sps)
    | Sk.Tree t -> Tree.iter t ~f:(push sps)
    | Sk.Let {bound; body} -> push sps bound ; push sps body
    | Sk.Lambda {body; _} -> push sps body
    | Sk.Op {args; _} | Sk.Apply {args; _} -> List.iter args ~f:(push sps)
  in
  push Sp.Set.empty

let push_specs : Deduction.t =
 fun sk -> try push_specs_exn sk ; Some sk with Bottom -> None
