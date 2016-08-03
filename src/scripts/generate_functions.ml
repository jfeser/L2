#!/usr/bin/env ocaml
#use "topfind";;
#thread;;
#require "core.top";;
#ppx "ppx-jane -as-ppx";;
#require "l2";;

open Core.Std
open L2
    
open Collections
open Hypothesis
open Infer
open Synthesis_common
open V2_engine

module Sp = Specification

let rec generate_value : ?max_int:int -> ?max_len:int -> Type.t -> Value.t =
  let open Type in
  fun ?(max_int = 10) ?(max_len = 5) -> function
    | Const_t Num_t -> `Num (Random.int (max_int + 1))
    | App_t ("list", [t]) ->
      let len = Random.int (max_int + 1) in
      `List (List.init len ~f:(fun _ -> generate_value ~max_int ~max_len t))
    | t -> failwiths "Unsupported type." t [%sexp_of:Type.t]

let generate_inputs : Type.t -> Value.t list =
  let open Type in
  function
  | Arrow_t (input_ts, _) -> List.map input_ts ~f:generate_value
  | t -> failwiths "Not an arrow type." t [%sexp_of:Type.t]

let generate_expr : cost:int -> Library.t -> Type.t -> Expr.t list =
  let module H = Hypothesis in
  fun ~cost library type_ ->
    let cost_model = V2_engine.default_cost_model in
    
    let initial_hypo =
      H.hole
        cost_model
        (Hole.create type_ L2_Generalizer.Symbols.lambda)
        Specification.top
    in
    let gen = V2_engine.L2_Generalizer.With_components.create cost_model library in

    let rec loop hypo =
      let hypos = Generalizer.generalize_single { cost_model; library } gen hypo in
      print_endline "Generalizing:";
      print_endline (H.to_string hypo);
      
      let small_abstract = List.filter hypos ~f:(fun h ->
          H.cost h + (H.holes h |> List.length) <= cost && H.kind h = H.Abstract)
      in
      let concrete = List.filter hypos ~f:(fun h ->
          H.cost h >= cost && H.kind h = H.Concrete)
      in
      if List.length concrete > 0 then
        concrete |> List.map ~f:H.to_expr
      else
        List.concat_map small_abstract ~f:loop
      (* let choices = *)
      (*   (if List.length small_abstract > 0 then [`Abstract] else []) @ *)
      (*   (if List.length concrete > 0 then [`Concrete] else []) *)
      (* in *)
      (* printf "%d\n" (List.length choices); *)
      (* flush stdout; *)
      (* match List.random choices with *)
      (* | Some `Abstract -> *)
      (*   List.permute small_abstract *)
      (*   |> List.find_map ~f:loop *)
      (* | Some `Concrete -> Some (Option.value_exn (List.random concrete) |> H.to_expr) *)
      (* | None -> None *)
    in

    loop initial_hypo

let generate_exprs : cost:int -> Library.t -> Type.t -> Expr.t Sequence.t =
  let module H = Hypothesis in
  let module Seq = Sequence in
  fun ~cost library type_ ->
    let cost_model = V2_engine.default_cost_model in
    
    let initial_hypo =
      H.hole
        cost_model
        (Hole.create type_ L2_Generalizer.Symbols.lambda)
        Specification.top
    in
    let gen = V2_engine.L2_Generalizer.With_components.create cost_model library in

    let rec loop hypo =
      printf "Generalizing: %s\n" (H.to_string_hum hypo);
      let hypos =
        Generalizer.(generalize_single { cost_model; library } gen hypo)
      in
      
      let small_abstract =
        List.filter hypos ~f:(fun h ->
            H.cost h + (H.holes h |> List.length) <= cost && H.kind h = H.Abstract)
        |> List.permute
      in
      let concrete =
        List.filter hypos ~f:(fun h -> H.cost h = cost && H.kind h = H.Concrete)
      in
      if List.length concrete > 0 then
        Seq.of_list concrete
      else
        Seq.concat_map (Seq.of_list small_abstract) ~f:loop
      
      (* let choices = *)
      (*   (if List.length small_abstract > 0 then [`Abstract] else []) @ *)
      (*   (if List.length concrete > 0 then [`Concrete] else []) *)
      (* in *)
      (* printf "%d\n" (List.length choices); *)
      (* flush stdout; *)
      (* match List.random choices with *)
      (* | Some `Abstract -> *)
      (*   List.permute small_abstract *)
      (*   |> List.find_map ~f:loop *)
      (* | Some `Concrete -> Some (Option.value_exn (List.random concrete) |> H.to_expr) *)
      (* | None -> None *)
    in

    loop initial_hypo |> Seq.map ~f:H.to_expr

let generate_spec
  : (Value.t list) list -> Library.t -> Type.t -> Expr.t -> Sp.t =
  fun inputs l t e ->
    try
      List.map inputs ~f:(fun ins ->
          let ins = List.map ins ~f:Expr.of_value in
          let out =
            Eval.eval ~recursion_limit:100 (ref l.Library.value_ctx) (`Apply (e, ins))
          in
          (ins, out))
      |> FunctionExamples.of_input_output_list_exn
      |> FunctionExamples.to_spec
    with
    | Eval.HitRecursionLimit -> Sp.bottom
    | Eval.RuntimeError err -> Sp.bottom

let is_interesting : Sp.t -> bool =
  fun spec -> 
    match Sp.data spec with
    | Sp.Bottom -> false
    | FunctionExamples.FunctionExamples exs ->
      let outs =
        FunctionExamples.to_list exs
        |> List.map ~f:Tuple.T2.get2
      in
      not (List.all_equal outs)
    | _ -> true

type out = {
  function_ : Expr.t;
  spec : Sp.t;
} [@@deriving sexp]

let cmd =
  let spec =
    let open Command.Spec in
    empty
    +> flag "-v" ~aliases:["--verbose"] no_arg ~doc:" print verbose output"
    +> anon ("max-cost" %: int)
    +> anon ("library" %: file)
    +> anon ("type" %: string)
    +> anon ("out-dir" %: string)
  in

  let run verbose max_cost library_fn type_str out_dir () =
    let library = Library.from_file_exn library_fn in
    let type_ = Type.of_string_exn type_str in
    
    Status.disable ();

    let type_str = Type.to_string type_ in

    let num_examples = 10 in
    let inputs = List.init num_examples ~f:(fun _ -> generate_inputs type_) in
    let discarded = ref 0 in
    let duplicates = ref 0 in

    (* Memoizer.to_flat_sequence memoizer ~min_cost:0 ~max_cost initial_hypo *)

    (* Sequence.repeat () *)

    (* |> Sequence.map ~f:(fun _ -> *)
    (*     generate_expr ~cost:max_cost library type_ *)
    (*   ) *)
    (* |> Sequence.concat_map ~f:Sequence.of_list *)

    generate_exprs ~cost:max_cost library type_
      
    |> Sequence.map ~f:(fun e ->
        {
          function_ = e;
          spec = generate_spec inputs library type_ e;
        }
      )

    |> Sequence.mapi ~f:(fun i out ->
        if i % 100 = 0 then begin
          printf "%d discarded\n" !discarded;
          printf "%d duplicates\n" !duplicates;
        end;
        out)

    |> Sequence.filter ~f:(fun x ->
        if is_interesting x.spec then true else begin
          incr discarded;
          false
        end)

    |> Sequence.unfold_with ~init:Sp.Set.empty ~f:(fun specs x ->
        let open Sequence.Step in
        if Set.mem specs x.spec then begin
          incr duplicates;
          Skip specs
        end
        else
          Yield (x, Set.add specs x.spec)
      )
      
    |> Sequence.inspect ~f:(fun out ->
        print_endline (Expr.to_string out.function_);
        print_endline (Specification.to_string out.spec);
        print_newline ())
      
    |> Sequence.iteri ~f:(fun i out ->
        let fn = sprintf "%s/%s_%d.sexp" out_dir type_str i in
        Out_channel.with_file fn ~f:(fun ch ->
            [%sexp_of:out] out
            |> Sexp.to_string_hum
            |> Out_channel.output_string ch);

        let name = sprintf "f%d" i in
        let exs = match Sp.data out.spec with
          | FunctionExamples.FunctionExamples exs ->
            FunctionExamples.to_list exs
            |> List.map ~f:(fun ((_, ins), out) ->
                `Apply (`Id name, List.map ins ~f:Expr.of_value), Expr.of_value out)
        in
        let testcase = Testcase.({
            name; desc = ""; case = Examples (exs, []); blacklist = [];
          })
        in
        let fn = sprintf "%s/%s_%d.json" out_dir type_str i in
        Testcase.to_file_exn ~filename:fn testcase
      );
  in

  Command.basic ~summary:"Generate functions." spec run

let () =
  Command.run cmd

