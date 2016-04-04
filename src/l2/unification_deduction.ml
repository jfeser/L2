open Core.Std

open Synthesis_common
open Collections
open Hypothesis

module Sk = Skeleton

let counter = Counter.empty ()
let () =
  let n = Counter.add_zero counter in
  n "symb_exec_tried" "Number of expressions where symbolic execution was tried.";
  n "symb_exec_failed" "Number of expressions where symbolic execution failed.";
  n "symb_exec_fatal" "Number of expressions where symbolic execution failed fatally.";
  n "unification_tried" "Number of expressions where unification was tried.";
  n "unification_failed" "Number of expressions where unification failed.";
  n "unification_pruned" "Number of times where an expression was pruned by unification.";
  n "unification_succeeded" "Number of times where unification succeeded.";
  n "push_spec_w_unification" "Tried to push spec using unification procedure."

let recursion_limit = 100

let sterm_of_result r =
  let open Expr.Op in
  let fresh_name = Util.Fresh.mk_fresh_name_fun () in
  let ctx = ref Hole.Id.Map.empty in
  let module U = Unify in
  let rec f r =
    let module SE = Symbolic_execution in
    let module Sk = Skeleton in
    match r with
    | SE.Num_r x -> U.K (Int.to_string x)
    | SE.Bool_r x -> U.K (if x then "true" else "false")
    | SE.List_r [] -> U.K "[]"
    | SE.List_r (x::xs) -> U.Cons (f x, f (SE.List_r xs))
    | SE.Id_r (Sk.Id.StaticDistance sd) -> U.V (StaticDistance.to_string sd)
    | SE.Id_r (Sk.Id.Name id) -> U.V id
    | SE.Op_r (RCons, [xs; x])
    | SE.Op_r (Cons, [x; xs]) -> U.Cons (f x, f xs)
    | SE.Symbol_r id -> 
      let var = match Hole.Id.Map.find !ctx id with
        | Some var -> var
        | None ->
          let var = fresh_name () in
          ctx := Hole.Id.Map.add !ctx ~key:id ~data:var; var
      in
      U.V var
    | SE.Apply_r _ -> U.V (fresh_name ())
    | SE.Closure_r _
    | SE.Tree_r _
    | SE.Op_r _ -> raise U.Unknown
  in
  try
    let sterm = f r in
    let ctx = Hole.Id.Map.to_alist !ctx |> List.map ~f:Tuple.T2.swap |> String.Map.of_alist_exn in
    Ok (sterm, ctx)
  with U.Unknown -> Error (Error.of_string "Unhandled construct.")

let rec value_of_term t : Value.t =
  let module U = Unify in
  match t with
  | U.Term ("[]", []) -> `List []
  | U.Term ("true", []) -> `Bool true
  | U.Term ("false", []) -> `Bool false
  | U.Term (s, []) -> `Num (Int.of_string s)
  | U.Term ("Cons", [x; y]) -> begin
      match value_of_term y with
      | `List y -> `List ((value_of_term x)::y)
      | _ -> failwith "Translation error"
    end
  | _ -> failwith "Translation error"

let push_specs s =
  if (!Config.config).Config.deduction then
    let module SE = Symbolic_execution in
    let module Sp = Specification in
    Counter.incr counter "push_spec_w_unification";
    match Skeleton.annotation s with
    | Sp.Examples exs ->
      let m_new_examples =
        List.fold (Sp.Examples.to_list exs) ~init:(Some Hole.Id.Map.empty) ~f:(fun m_exs (ins, out_e) ->
            Option.bind m_exs (fun exs -> 
                try
                  Counter.incr counter "symb_exec_tried";

                  (* Try symbolically executing the candidate in the example context. *)
                  let out_a = SE.partially_evaluate ~recursion_limit
                      ~ctx:(StaticDistance.Map.map ins ~f:SE.result_of_value) s
                  in

                  match out_a with
                  | SE.Symbol_r _ -> None
                  | SE.Apply_r _ ->
                    begin
                      match SE.skeleton_of_result out_a with
                      | Some skel ->
                        if (CostModel.cost_of_skeleton V2_engine.cost_model skel) <
                           (CostModel.cost_of_skeleton V2_engine.cost_model s)
                        then None else m_exs
                      | None -> m_exs
                    end
                  | _ -> begin
                      Counter.incr counter "unification_tried";

                      (* Convert output and expected output to terms and
                         unify. If unification fails, discard the candidate. *)
                      match sterm_of_result out_a with
                      | Ok (out_a, symbol_names) -> begin match Unify.sterm_of_value out_e with
                          | Some out_e -> begin try
                                let sub = Unify.unify_one (Unify.translate out_a) (Unify.translate out_e) in
                                Counter.incr counter "unification_succeeded";
                                Some (List.fold sub ~init:exs ~f:(fun exs (var, term) ->
                                    match String.Map.find symbol_names var with
                                    | Some id ->
                                      Hole.Id.Map.add_multi exs ~key:id ~data:(ins, value_of_term term)
                                    | None -> exs))
                              with Unify.Non_unifiable ->
                                Counter.incr counter "unification_pruned";
                                None
                            end
                          | None ->
                            Counter.incr counter "unification_failed";
                            m_exs
                        end
                      | Error _ ->
                        Counter.incr counter "unification_failed";
                        m_exs
                    end
                with
                (* These are non-fatal errors. We learn nothing about the
                   candidate, but we can't discard it either. *)
                | SE.EvalError `HitRecursionLimit
                | SE.EvalError `UnhandledConditional ->
                  Counter.incr counter "symb_exec_failed";
                  m_exs

                (* All other errors are fatal, so we discard the candidate. *)
                | SE.EvalError _ ->
                  Counter.incr counter "symb_exec_fatal";
                  None))
      in
      Option.bind m_new_examples (fun new_exs ->
          let new_exs = Hole.Id.Map.map new_exs ~f:Sp.Examples.of_list in
          if Hole.Id.Map.exists new_exs ~f:Result.is_error then None else
            Some (Hole.Id.Map.map new_exs ~f:Or_error.ok_exn))
      |>  Option.map ~f:(fun new_exs -> Skeleton.map_hole s ~f:(fun (hole, old_spec) ->
          let s = Sk.Hole_h (hole, old_spec) in
          match Hole.Id.Map.find new_exs hole.Hole.id with
          | Some exs -> begin match old_spec with
              | Sp.Top -> Skeleton.Hole_h (hole, Sp.Examples exs)
              | _ -> s
            end
          | None -> s))
    | _ -> Some s
  else Some s
