open Core
open Printf
open L2
open Synthesis_common
open Collections

let deduction_timer =
  let t = Timer.empty () in
  let n = Timer.add_zero t in
  n "higher_order" "Total time in higher-order deduction.";
  n "fast_example" "Total time in fast example deduction.";
  n "example" "Total time in example deduction.";
  t

let higher_order_deduction sk =
  Timer.run_with_time deduction_timer "higher_order" (fun () ->
      Higher_order_deduction.push_specs sk)

(** Get a JSON object containing all captured information from a single run. *)
let get_json testcase runtime solution config argv =
  let solution_str = match solution with `Solution s -> s | `NoSolution -> "" in
  let timers =
    [
      ("search", V1_solver_engine.timer);
      ("memoizer", Synthesis_common.timer);
      ("deduction", deduction_timer);
      ("fe_deduction", Fast_example_deduction.timer);
    ]
  in
  let counters =
    [
      ("search", V1_solver_engine.counter);
      ("memoizer", Synthesis_common.counter);
      ("fe_deduction", Fast_example_deduction.counter);
    ]
  in
  let sexp_logs = [ ("memoizer", Synthesis_common.sexp_log) ] in
  `Assoc
    [
      ( "timers",
        `List
          (List.map timers ~f:(fun (name, timer) ->
               `Assoc [ (name, Timer.to_json timer) ])) );
      ( "counters",
        `List
          (List.map counters ~f:(fun (name, counter) ->
               `Assoc [ (name, Counter.to_json counter) ])) );
      ( "sexp_logs",
        `List
          (List.map sexp_logs ~f:(fun (name, sexp_log) ->
               `Assoc [ (name, SexpLog.to_json sexp_log) ])) );
      ("testcase", Testcase.to_json testcase);
      ("solution", `String solution_str);
      ("runtime", `Float runtime);
      ("config", `String (Config.to_string config));
      ("argv", `List (Array.map argv ~f:(fun a -> `String a) |> Array.to_list));
    ]

let synthesize ?spec_dir ?max_cost engine deduction cost_model library testcase =
  let module T = Testcase in
  match testcase.T.case with
  | T.Examples (exs, bg) -> (
      let config = !Config.config in
      match engine with
      | `V1 ->
          let v1_config =
            {
              V1_engine.verbosity = config.Config.verbosity;
              V1_engine.untyped = config.Config.untyped;
              V1_engine.deduction = config.Config.deduction;
              V1_engine.infer_base = config.Config.infer_base;
              V1_engine.max_exhaustive_depth = config.Config.max_exhaustive_depth;
              V1_engine.flat_cost = config.Config.flat_cost;
            }
          in
          let solutions, runtime =
            Util.with_runtime (fun () ->
                V1_engine.solve ~init:V1_engine.default_init ~config:v1_config ~bk:bg
                  exs)
          in
          let solution_str =
            Ctx.to_alist solutions |> List.map ~f:Tuple.T2.get2
            |> List.map ~f:Expr.to_string |> String.concat ~sep:"\n"
          in
          (`Solution solution_str, runtime)
      | `V1_solver ->
          let solutions, runtime =
            Util.with_runtime (fun () ->
                V1_solver_engine.solve ~init:V1_solver_engine.extended_init ~config
                  ~bk:bg exs)
          in
          let solution_str =
            Ctx.to_alist solutions |> List.map ~f:Tuple.T2.get2
            |> List.map ~f:Expr.to_string |> String.concat ~sep:"\n"
          in
          (`Solution solution_str, runtime)
      | `V2 -> (
          let open V2_engine in
          let open Hypothesis in
          let deduce =
            List.fold_left deduction ~init:Deduction.no_op ~f:(fun d ->
              function
              | `None -> Deduction.no_op
              | `Higher_order -> Deduction.compose d higher_order_deduction
              | `Random -> Deduction.compose d Random_deduction.push_specs
              | `Recursive_spec ->
                  Deduction.compose d Recursive_spec_deduction.push_specs
              | `Input_ctx -> Deduction.compose d Input_deduction.push_specs
              | `Fast_example ->
                  let open Fast_example_deduction in
                  let push_specs =
                    match spec_dir with
                    | Some dir -> create dir library
                    | None -> failwith "Must pass spec-dir parameter."
                  in
                  let push_specs sk =
                    Timer.run_with_time deduction_timer "fast_example" (fun () ->
                        push_specs sk)
                  in
                  Deduction.compose d push_specs)
          in
          let m_solution, runtime =
            Util.with_runtime (fun () ->
                let synth = L2_Synthesizer.create deduce ?cost_model library in
                let hypo = L2_Synthesizer.initial_hypothesis synth exs in
                L2_Synthesizer.synthesize ?max_cost synth hypo)
          in
          match m_solution with
          | Ok (Some s) ->
              let hypo_str =
                Format.set_margin 70;
                Skeleton.pp Format.str_formatter (Hypothesis.skeleton s);
                Format.flush_str_formatter ()
              in
              (`Solution hypo_str, runtime)
          | Ok None -> (`NoSolution, runtime)
          | Error err ->
              print_endline (Error.to_string_hum err);
              (`NoSolution, runtime) ) )

let parse_symbol_exn symbols s =
  match List.Assoc.find ~equal:( = ) symbols s with
  | Some sym -> sym
  | None ->
      Error.createf "Unexpected parameter '%s'. Expected one of: %s." s
        ( [%sexp_of: string list] (List.map ~f:Tuple.T2.get1 symbols)
        |> Sexp.to_string_hum )
      |> Error.raise

let parse_symbol_list_exn symbols str =
  String.split str ~on:','
  |> List.filter ~f:(fun s -> not (String.is_empty s))
  |> List.map ~f:(parse_symbol_exn symbols)

let symbol : 'a. (string * 'a) list -> 'a Command.Arg_type.t =
 fun symbols ->
  Command.Arg_type.create
    ~complete:(fun _ ~part ->
      List.filter symbols ~f:(fun (name, _) -> String.is_prefix ~prefix:part name)
      |> List.map ~f:Tuple.T2.get1)
    (parse_symbol_exn symbols)

let nonempty_symbol_list : 'a. (string * 'a) list -> 'a list Command.Arg_type.t =
 fun symbols ->
  Command.Arg_type.create
    ~complete:(fun _ ~part ->
      let last_part = Option.value_exn (String.split part ~on:' ' |> List.last) in
      List.filter symbols ~f:(fun (name, _) ->
          String.is_prefix ~prefix:last_part name)
      |> List.map ~f:Tuple.T2.get1)
    (fun str ->
      match parse_symbol_list_exn symbols str with
      | [] ->
          Error.createf "No parameters provided. Expected one of: %s."
            ( [%sexp_of: string list] (List.map ~f:Tuple.T2.get1 symbols)
            |> Sexp.to_string_hum )
          |> Error.raise
      | l -> l)

let directory =
  Command.Arg_type.create (fun str ->
      if Sys.is_directory str = `Yes then str
      else Error.create "Not a directory." str [%sexp_of: string] |> Error.raise)

let synth_command =
  let spec =
    let open Command.Spec in
    empty
    +> flag "-c" ~aliases:[ "--config" ] (optional string)
         ~doc:" read configuration from file"
    +> flag "-d" ~aliases:[ "--debug" ] (optional string)
         ~doc:" write debugging information to file in JSON format"
    +> flag "--flat-cost" no_arg ~doc:" use a flat cost metric (v1 engine only)"
    +> flag "--cost" (optional string)
         ~doc:
           " load cost function parameters from file (only only applies when using \
            v2 engine)"
    +> flag "--max-cost" (optional int)
         ~doc:" set the maximum cost of functions to be explored"
    +> flag "-dd" ~aliases:[ "--deduction" ]
         (optional_with_default [ `Higher_order ]
            (nonempty_symbol_list
               [
                 ("fast_example", `Fast_example);
                 ("higher_order", `Higher_order);
                 ("recursive_spec", `Recursive_spec);
                 ("input_ctx", `Input_ctx);
                 ("random", `Random);
                 ("none", `None);
               ]))
         ~doc:
           " deduction routines to use during synthesis (only applies when using v2 \
            engine)"
    +> flag "-e" ~aliases:[ "--engine" ]
         (optional_with_default `V2
            (symbol [ ("v1", `V1); ("v1_solver", `V1_solver); ("v2", `V2) ]))
         ~doc:" the synthesis algorithm to use"
    +> flag "-l" ~aliases:[ "--library" ] (optional string)
         ~doc:" file containing components to use for synthesis"
    +> flag "--spec-dir" (optional directory)
         ~doc:" directory containing component specifications"
    +> flag "-q" ~aliases:[ "--quiet" ] no_arg ~doc:" no output while searching"
    +> flag "-v" ~aliases:[ "--verbose" ] no_arg
         ~doc:" print progress messages while searching"
    +> flag "-V" ~aliases:[ "--very-verbose" ] no_arg
         ~doc:" print many progress messages while searching"
    +> flag "-z" ~aliases:[ "--use-z3" ] no_arg ~doc:" use Z3 for pruning"
    +> anon (maybe ("testcase" %: string))
  in
  let run config_file json_file flat_cost cost_file max_cost deduction engine
      m_library spec_dir quiet verbose very_verbose use_solver m_testcase_name () =
    let initial_config =
      match config_file with
      | Some file -> In_channel.read_all file |> Config.of_string
      | None -> Config.default
    in
    Config.config :=
      {
        initial_config with
        Config.verbosity =
          (if verbose || very_verbose then if very_verbose then 2 else 1 else 0);
        Config.use_solver;
        Config.flat_cost;
      };
    let err =
      let module Let_syntax = Or_error.Let_syntax.Let_syntax in
      let%bind testcase =
        match m_testcase_name with
        | Some testcase_name -> Testcase.from_file ~filename:testcase_name
        | None -> Testcase.from_channel In_channel.stdin
      in
      let cost_model =
        Option.map cost_file ~f:(fun f ->
            Hypothesis.PerFunctionCostModel.of_json (Json.from_file f)
            |> Hypothesis.PerFunctionCostModel.to_cost_model)
      in
      let%bind library =
        match m_library with
        | Some fn -> Library.from_file fn
        | None -> Ok Library.empty
      in
      (* Remove functions on the blacklist from the library. *)
      let library =
        Library.filter_keys library ~f:(fun k ->
            not (List.mem ~equal:( = ) testcase.Testcase.blacklist k))
      in
      if quiet then Status.disable ();
      let m_solution, solve_time =
        synthesize ?spec_dir ?max_cost engine deduction cost_model library testcase
      in
      if quiet then
        match m_solution with `Solution s -> print_endline s | `NoSolution -> ()
      else (
        printf "Runtime: %s\n" (Time.Span.to_short_string solve_time);
        match m_solution with
        | `Solution s -> printf "Found solution:\n%s" s
        | `NoSolution -> printf "No solution found." );
      (* Write debug information to a file, if requested. *)
      ( match json_file with
      | Some file ->
          Out_channel.with_file file ~f:(fun ch ->
              get_json testcase
                (Time.Span.to_sec solve_time)
                m_solution !Config.config Sys.argv
              |> Json.pretty_to_channel ~std:true ch)
      | None -> () );
      Ok ()
    in
    match err with
    | Ok () -> ()
    | Error err -> print_string (Error.to_string_hum err)
  in
  Command.basic_spec ~summary:"Synthesize programs from specifications." spec run

let eval_command =
  let spec =
    let open Command.Spec in
    empty
    +> flag "--untyped" no_arg ~doc:" disable type-checking before evaluation"
    +> flag "--syntax"
         (optional_with_default `Ml (symbol [ ("sexp", `Sexp); ("ml", `Ml) ]))
         ~doc:" syntax to use for parsing expressions"
    +> flag "--library" (optional string)
         ~doc:" component library to load before evaluating"
    +> anon (maybe ("source" %: string))
  in
  let run untyped syntax library_fn m_source_fn () =
    let source =
      match m_source_fn with
      | Some fn -> In_channel.read_all fn
      | None -> In_channel.input_all In_channel.stdin
    in
    let output =
      let open Or_error.Let_syntax in
      let%bind library =
        match library_fn with
        | Some fn -> Library.from_file fn
        | None -> Library.empty |> Or_error.return
      in
      let%bind expr = Expr.of_string ~syntax source in
      let%bind () =
        if untyped then Ok ()
        else
          try
            Infer.Type.of_expr ~ctx:library.Library.type_ctx expr |> ignore;
            Ok ()
          with Infer.TypeError msg -> Error msg
      in
      try Ok (Eval.eval (ref library.Library.value_ctx) expr)
      with Eval.RuntimeError err -> Error err
    in
    match output with
    | Ok v -> [%sexp_of: Ast.evalue] v |> print_s
    | Error err -> print_string ("Error: " ^ Error.to_string_hum err ^ "\n")
  in
  Command.basic_spec ~summary:"Run L2 source code." spec run

let library_command =
  let spec =
    let open Command.Spec in
    empty +> anon (maybe ("source" %: string))
  in
  let run m_source_fn () =
    let m_library =
      match m_source_fn with
      | Some fn -> Library.from_file fn
      | None -> Library.from_channel ~file:"stdin" In_channel.stdin
    in
    match m_library with
    | Ok library ->
        printf "Builtins: %s\n\n"
          ( List.map library.Library.builtins ~f:Expr.Op.to_string
          |> String.concat ~sep:", " );
        printf "Functions:\n";
        List.iter (String.Map.keys library.Library.expr_ctx) ~f:(fun name ->
            let type_ = String.Map.find_exn library.Library.type_ctx name in
            let expr = String.Map.find_exn library.Library.expr_ctx name in
            printf "%s: %s\n" name (Infer.Type.to_string type_);
            print_endline (Expr.to_string expr);
            Out_channel.newline stdout);
        printf "Summary: %d values" (String.Map.length library.Library.expr_ctx)
    | Error err -> print_endline (Error.to_string_hum err)
  in
  Command.basic_spec ~summary:"Load a library and print." spec run

let commands =
  Command.group ~summary:"A suite of tools for synthesizing and running L2 programs."
    [
      ("synth", synth_command); ("eval", eval_command); ("library", library_command);
    ]

let () = Command.run commands
