open Core.Std
open Printf

open Collections

(** Get a JSON object containing all captured information from a single run. *)
let get_json testcase runtime solution config : Json.json =
  let timers = [
    "search", Search.timer;
    (* "deduction", Deduction.timer; *)
  ] in
  let counters = [
    "search", Search.counter;
    "improved_search", Improved_search.counter;
    (* "deduction", Deduction.counter; *)
  ] in
  `Assoc [
    "timers", `List (List.map timers ~f:(fun (name, timer) -> `Assoc [name, Timer.to_json timer]));
    "counters", `List (List.map counters ~f:(fun (name, counter) -> `Assoc [name, Counter.to_json counter]));
    "testcase", Testcase.to_json testcase;
    "solution", `String solution;
    "runtime", `Float runtime;
    "config", `String (Config.to_string config);
  ]  

let time_solve testcase : (Expr.t list * Time.Span.t) =
  let module T = Testcase in
  match testcase.T.case with
  | T.Examples (exs, bg) -> 
    let config = !Config.config in

    (* Attempt to synthesize from specification. *)
    if config.Config.improved_search then
      let open Improved_search in
      let open Hypothesis in
      Util.with_runtime (fun () ->
          let hypo = L2_Synthesizer.initial_hypothesis exs in
          match L2_Synthesizer.synthesize hypo ~cost:50 with
          | Some s -> printf "%s\n" (Hypothesis.to_string s); []
          | None -> printf "No solution\n"; [])
    else
      Util.with_runtime (fun () ->
          let solutions = Search.solve ~init:Search.extended_init ~config ~bk:bg exs in
          Ctx.to_alist solutions
          |> List.map ~f:(fun (name, lambda) ->
              `Let (name, lambda, `Id "_")))

let synth_command =
  let spec =
    let open Command.Spec in
    empty
    +> flag "-c" ~aliases:["--config"] (optional string) ~doc:" read configuration from file"
    +> flag "-d" ~aliases:["--debug"] (optional string) ~doc:" write debugging information to file in JSON format"
    +> flag "-i" no_arg ~doc:" use improved search"
    +> flag "-v" ~aliases:["--verbose"] no_arg ~doc:" print progress messages while searching"
    +> flag "-V" ~aliases:["--very-verbose"] no_arg ~doc:" print many progress messages while searching"
    +> flag "-z" ~aliases:["--use-z3"] no_arg ~doc:" use Z3 for pruning"
    +> anon (maybe ("testcase" %: string))
  in

  let run config_file json_file use_improved_search verbose very_verbose use_solver m_testcase_name () =
    let () = Config.config :=
        let open Config in
        (* Either load the initial config from a file or use the default config. *)
        let initial_config = 
          match config_file with
          | Some file -> In_channel.read_all file |> of_string
          | None -> default
        in
        (* Apply any changes from command line flags. *)
        {
          initial_config with
          verbosity =
            if verbose || very_verbose then
              if very_verbose then 2 else 1
            else 0;
          use_solver;
          improved_search = use_improved_search;
        }in

    let m_testcase = match m_testcase_name with
      | Some testcase_name -> Testcase.from_file testcase_name
      | None -> Testcase.from_channel In_channel.stdin
    in

    match m_testcase with
    | Ok testcase -> begin
        let (solutions, solve_time) = time_solve testcase in
        let solutions_str = List.map solutions ~f:Expr.to_string |> String.concat ~sep:"\n" in
        let solve_time_str = Time.Span.to_short_string solve_time in

        (* Print out results summary. *)
        printf "Solved %s in %s. Solutions:\n%s\n" testcase.Testcase.name solve_time_str solutions_str;

        (* Write debug information to a file, if requested. *)
        match json_file with
        | Some file ->
          Json.to_file ~std:true file
            (get_json
               testcase
               (Time.Span.to_sec solve_time)
               solutions_str
               !Config.config)
        | None -> ()
      end
    | Error err ->
      print_string "Error: Loading testcase failed.\n";
      print_string (Error.to_string_hum err)
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
