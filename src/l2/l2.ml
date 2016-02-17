open Core.Std
open Printf

open Collections

(** Get a JSON object containing all captured information from a single run. *)
let get_json testcase runtime solution config : Json.json =
  let solution_str = match solution with
    | `Solution s -> s
    | `NoSolution -> ""
  in
  let timers = [
    "search", V1_solver_engine.timer;
    (* "deduction", Deduction.timer; *)
  ] in
  let counters = [
    "search", V1_solver_engine.counter;
    "improved_search", V2_engine.counter;
    (* "deduction", Deduction.counter; *)
  ] in
  `Assoc [
    "timers", `List (List.map timers ~f:(fun (name, timer) -> `Assoc [name, Timer.to_json timer]));
    "counters", `List (List.map counters ~f:(fun (name, counter) -> `Assoc [name, Counter.to_json counter]));
    "testcase", Testcase.to_json testcase;
    "solution", `String solution_str;
    "runtime", `Float runtime;
    "config", `String (Config.to_string config);
  ]

let synthesize engine testcase =
  let module T = Testcase in
  match testcase.T.case with
  | T.Examples (exs, bg) ->
    let config = !Config.config in

    begin match engine with
      | `V1 ->
        let v1_config = {
          V1_engine.verbosity = config.Config.verbosity;
          V1_engine.untyped = config.Config.untyped;
          V1_engine.deduction = config.Config.deduction;
          V1_engine.infer_base = config.Config.infer_base;
          V1_engine.max_exhaustive_depth = config.Config.max_exhaustive_depth;
        } in
        let (solutions, runtime) = Util.with_runtime (fun () ->
            V1_engine.solve ~init:V1_engine.default_init ~config:v1_config ~bk:bg exs)
        in
        let solution_str =
          Ctx.to_alist solutions
          |> List.map ~f:Tuple.T2.get2
          |> List.map ~f:Expr.to_string
          |> String.concat ~sep:"\n"
        in
        (`Solution solution_str, runtime)

      | `V1_solver ->
        let (solutions, runtime) = Util.with_runtime (fun () ->
            V1_solver_engine.solve ~init:V1_solver_engine.extended_init ~config ~bk:bg exs)
        in
        let solution_str =
          Ctx.to_alist solutions
          |> List.map ~f:Tuple.T2.get2
          |> List.map ~f:Expr.to_string
          |> String.concat ~sep:"\n"
        in
        (`Solution solution_str, runtime)
      
      | `V2 -> begin
          let open V2_engine in
          let open Hypothesis in
          let (m_solution, runtime) = Util.with_runtime (fun () ->
              let hypo = L2_Synthesizer.initial_hypothesis exs in
              L2_Synthesizer.synthesize hypo ~cost:50)
          in
          match m_solution with
          | Ok (Some s) -> (`Solution (Hypothesis.to_string s), runtime)
          | Ok None -> (`NoSolution, runtime)
          | Error err -> print_endline (Error.to_string_hum err); (`NoSolution, runtime)
        end

      | `Automata -> begin
          let open Hypothesis in
          let (m_solution, runtime) = Util.with_runtime (fun () ->
              Automaton.Synthesizer.synthesize_from_examples ~max_cost:50 Component.stdlib exs)
          in
          match m_solution with
          | Ok (Some s) -> (`Solution (Hypothesis.to_string s), runtime)
          | Ok None -> (`NoSolution, runtime)
          | Error err -> print_endline (Error.to_string_hum err); (`NoSolution, runtime)
        end
    end

let synth_command =
  let spec =
    let open Command.Spec in
    empty
    +> flag "-c" ~aliases:["--config"] (optional string) ~doc:" read configuration from file"
    +> flag "-d" ~aliases:["--debug"] (optional string) ~doc:" write debugging information to file in JSON format"
    +> flag "-e" ~aliases:["--engine"] (optional_with_default "v1" string) ~doc:" the synthesis algorithm to use"
    +> flag "-v" ~aliases:["--verbose"] no_arg ~doc:" print progress messages while searching"
    +> flag "-V" ~aliases:["--very-verbose"] no_arg ~doc:" print many progress messages while searching"
    +> flag "-z" ~aliases:["--use-z3"] no_arg ~doc:" use Z3 for pruning"
    +> anon (maybe ("testcase" %: string))
  in

  let run config_file json_file engine_str verbose very_verbose use_solver m_testcase_name () =
    let initial_config = 
      match config_file with
      | Some file -> In_channel.read_all file |> Config.of_string
      | None -> Config.default
    in
    Config.config := {
      initial_config with
      Config.verbosity =
        if verbose || very_verbose then
          if very_verbose then 2 else 1
        else 0;
      Config.use_solver;
    };

    let module Let_syntax = Or_error.Let_syntax in
    let err = 
      let%bind testcase = match m_testcase_name with
        | Some testcase_name -> Testcase.from_file ~filename:testcase_name
        | None -> Testcase.from_channel In_channel.stdin
      in

      let%bind engine = match engine_str with
        | "v1" -> Ok `V1
        | "v1_solver" -> Ok `V1_solver
        | "v2" -> Ok `V2
        | "automata" -> Ok `Automata
        | _ -> error "Unexpected engine parameter." engine_str [%sexp_of:string]
      in

      let m_solution, solve_time = synthesize engine testcase in

      printf "Runtime: %s\n" (Time.Span.to_short_string solve_time);
      begin
        match m_solution with
        | `Solution s -> printf "Found solution:\n%s" s
        | `NoSolution -> printf "No solution found."
      end;

      (* Write debug information to a file, if requested. *)
      begin
        match json_file with
        | Some file -> 
          get_json testcase (Time.Span.to_sec solve_time) m_solution !Config.config
          |> Json.to_file ~std:true file
        | None -> ()
      end;
      
      Ok ()
    in

    match err with
    | Ok () -> ()
    | Error err -> print_string (Error.to_string_hum err)
  in

  Command.basic ~summary:"Synthesize programs from specifications." spec run

let eval_command =
  let spec =
    let open Command.Spec in
    empty
    +> flag "--untyped" no_arg ~doc:" disable type-checking before evaluation"
    +> anon (maybe ("source" %: string))
  in

  let run untyped m_source_fn () =
    let source = match m_source_fn with
      | Some fn -> In_channel.read_all fn
      | None -> In_channel.input_all In_channel.stdin
    in

    let open Or_error.Monad_infix in

    let m_output = 
      Expr.of_string source
      >>= (fun expr -> (* Perform type inference and report type errors, unless disabled. *)
          if untyped then Ok expr else
            Infer.infer (Ctx.empty ()) expr |> Or_error.map ~f:(fun _ -> expr))
      >>| fun expr -> Eval.eval (Ctx.empty ()) expr |> Eval.value_to_string
    in

    match m_output with
    | Ok value_str -> print_string value_str
    | Error err -> print_string ("Error: " ^ (Error.to_string_hum err) ^ "\n")
  in
  
  Command.basic ~summary:"Run L2 source code." spec run

let commands =
  Command.group ~summary:"A suite of tools for synthesizing and running L2 programs." [
    "synth", synth_command;
    "eval", eval_command;
  ]

let () = Command.run commands
