open Core.Std
open Core_extended.Std

open Synthesis_common
open Hypothesis
open Collections

module Sk = Skeleton
module Sp = Specification

exception Bottom

let push_specs_exn : Sp.t Sk.t -> unit = 
  let rec push sps sk =
    let spec = Sk.annotation sk in
    let sps = match Sp.spec spec with
      | Sp.Top -> sps
      | Examples.Examples _ | FunctionExamples.FunctionExamples _ ->
        if Sp.Set.mem sps spec then raise Bottom;
        Sp.Set.add sps spec
      | Sp.Bottom -> raise Bottom
      | _ -> sps
    in
    match sk with
    | Sk.Num_h _ | Sk.Bool_h _ | Sk.Id_h _ | Sk.Hole_h _ -> ()
    | Sk.List_h (l, _) -> List.iter l ~f:(push sps)
    | Sk.Tree_h (t, _) -> Tree.iter t ~f:(push sps)
    | Sk.Let_h ((bound, body), _) -> push sps bound; push sps body
    | Sk.Lambda_h ((_, body), _) -> push sps body
    | Sk.Op_h ((_, args), _)
    | Sk.Apply_h ((_, args), _) -> List.iter args ~f:(push sps)
  in
  push Sp.Set.empty

let push_specs : Deduction.t = fun sk ->
  try push_specs_exn sk; Some sk with Bottom -> None

