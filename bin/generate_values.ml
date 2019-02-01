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
open Util
open Fast_example_deduction

module Seq = Sequence

module Sk = Skeleton
module Sp = Specification
module H = Hypothesis

type config = {
  verbose : bool;
  library : Library.t;
  domain : Fast_example_deduction.domain;
}

let rec normalize ctx count = function
  | `AbsInt _ 
  | `Bool _
  | `Bottom
  | `Top as x -> x
  | `AbsEq (Abstract_eq.Elem x) ->
    begin match Map.find !ctx x with
      | Some x' -> `AbsEq (Abstract_eq.Elem x')
      | None ->
        let x' = !count in
        incr count;
        ctx := Map.add !ctx ~key:x ~data:x';
        `AbsEq (Abstract_eq.Elem x')
    end
  | `AbsEq Abstract_eq.Omega -> `AbsEq Abstract_eq.Omega
  | `AbsList x -> `AbsList (Abstract_list.map ~f:(normalize ctx count) x)
  | `List x -> `List (List.map ~f:(normalize ctx count) x)
  | `Tree x -> `Tree (Tree.map ~f:(normalize ctx count) x)
  | x -> failwiths "Unsupported value." x [%sexp_of:Abstract_value.t]

let generate_abs_values : config -> ImmutableType.t -> Abstract_value.t Seq.t =
  let module IT = ImmutableType in
  fun config type_ ->
    let rec gen = function
      | IT.Const_i Num_t ->
        Abstract_int.enumerate config.domain.int
        |> Seq.map ~f:(fun v -> `AbsInt v)
      | IT.Const_i Bool_t -> Seq.of_list [`Bool true; `Bool false]
      | IT.Quant_i _ -> Abstract_eq.enumerate config.domain.eq |> Seq.map ~f:(fun v -> `AbsEq v)
      | IT.App_i ("list", [elem_type]) ->
        let elems = gen elem_type |> Seq.to_list in
        Abstract_list.enumerate config.domain.list elems
        |> Seq.map ~f:(fun v -> `AbsList v)
      | t -> failwiths "Unsupported type." t [%sexp_of:IT.t]
    in
    gen type_

let generate_examples : config -> Expr.t -> Type.t -> Abstract_example.t Sequence.t =
  let module IT = ImmutableType in
  fun config func type_ ->
    match IT.of_type type_ with
    | ImmutableType.Arrow_i (args_t, ret_t) ->
      let inputs =
        List.map args_t ~f:(generate_abs_values config)
        |> List.map ~f:Seq.memoize
        |> Seq.product
        |> Seq.map ~f:(fun vs -> 
            let ctx = ref Int.Map.empty in
            let count = ref 0 in
            List.map ~f:(fun v -> normalize ctx count v) vs)
        |> Seq.to_list
        |> List.dedup
        |> Seq.of_list
      in
      let ctx =
        List.fold_left config.library.Library.exprs
          ~init:String.Map.empty ~f:(fun ctx (name, expr) ->
              let ctx_ref = ref ctx in
              let abs_expr = Abstract_expr.of_expr expr in
              let value =
                Abstract_value.eval
                  ~recursion_limit:(`Limited 1000)
                  ~ctx:ctx_ref
                  ~int_domain:config.domain.int
                  ~list_domain:config.domain.list
                  (`Let (name, abs_expr, `Id name))
              in
              Map.add !ctx_ref ~key:name ~data:value)
      in

      let abs_func = Abstract_expr.of_expr func in
      Seq.map inputs ~f:(fun args ->
          let abs_args = List.map ~f:Abstract_value.to_expr args in
          let ret =
            Abstract_value.eval
              ~ctx:(ref ctx)
              ~recursion_limit:(`Limited 1000)
              ~int_domain:config.domain.int
              ~list_domain:config.domain.list
              (`Apply (abs_func, abs_args))
          in
          args, ret)
      |> Seq.concat_map ~f:(fun (ins, out) ->
          match out with
          | `Top ->
            generate_abs_values config ret_t
            |> Seq.map ~f:(fun out' -> (ins, out'))
          | _ -> Seq.singleton (ins, out))

    | t -> failwiths "Unexpected type." t [%sexp_of:IT.t]

let save_examples : file:string -> config:config -> Abstract_example.t Sequence.t -> unit =
  fun ~file ~config exs ->
    let exs = Seq.to_list exs in
    let fs = Function_spec.of_examples config.domain exs in
    print_endline (Function_spec.to_string fs);
    Function_spec.to_file fs file

let view_sequence : 'a Sequence.t -> f:('a -> string) -> 'a Sequence.t = fun s ~f ->
  Sequence.map s ~f:(fun x -> printf "%s\n" (f x); flush stdout; x)

let generate_for_func : config:config -> file:string -> Expr.t -> Type.t -> unit =
  fun ~config ~file func type_ ->
    let exs = generate_examples config func type_ in
    let exs = if config.verbose then 
        view_sequence exs ~f:(fun (ins, out) ->
            sprintf "(%s) -> %s"
              (List.map ins ~f:Abstract_value.to_string |> String.concat ~sep:", ")
              (Abstract_value.to_string out))
      else exs
    in
    save_examples ~file ~config exs

let spec =
  let open Command.Spec in
  empty
  +> flag "-v" ~aliases:["--verbose"] no_arg ~doc:" print verbose output"
  +> anon ("library" %: file)
  +> anon (sequence ("function" %: string))

let run verbose library_fn names () =
  let err =
    let module Let_syntax = Or_error.Let_syntax.Let_syntax in
    let%bind library = Library.from_file library_fn in

    let config = {
      verbose; library;
      domain = {
        int = { lower = 0; upper = 10 };
        eq = { max_distinct = 4 };
        list = { max_length = 4 };
      }
    } in

    let functions =
      library.Library.type_ctx |> Map.to_alist |> List.map ~f:(fun (name, type_) ->
          let args_names = List.init (Type.arity type_) ~f:(fun i -> Int.to_string i) in
          let args_ids = List.map args_names ~f:(fun n -> `Id n) in
          (name, type_, `Lambda (args_names, `Apply (`Id name, args_ids))))
    in

    let operators = Expr.Op.all |> List.map ~f:(fun op ->
        let name = Expr.Op.to_string op in
        let type_ = Expr.Op.typ op in
        let args_names = List.init (Expr.Op.arity op) ~f:(fun i -> Int.to_string i) in
        let args_ids = List.map args_names ~f:(fun n -> `Id n) in
        (name, type_, `Lambda (args_names, `Op (op, args_ids))))
    in

    let selected = 
      List.filter (functions @ operators) ~f:(fun (n, _, _) -> List.mem names n)
    in

    List.iter selected ~f:(fun (name, type_, expr) ->
        let file = name ^ "-examples.sexp" in
        generate_for_func ~config ~file expr type_);

    Ok ()
  in

  match err with
  | Ok () -> ()
  | Error err -> print_string (Error.to_string_hum err)

let cmd = Command.basic ~summary:"Generate specifications for functions." spec run

let () = Command.run cmd
