open Core
open Printf

let time_solve csv config testcase =
  let examples, bk =
    match testcase.Testcase.case with
    | Testcase.Examples (exs, bk) -> (exs, bk)
  in
  let name = testcase.name in
  let desc = testcase.desc in
  let start_time = Time.now () in
  let solutions = Search.solve ~config ~bk examples in
  let end_time = Time.now () in
  let solve_time = Time.diff end_time start_time in
  let solutions_str =
    Util.Ctx.to_alist solutions
    |> List.map ~f:(fun (name, lambda) ->
        let lambda = Expr.normalize lambda in
        Expr.to_string (`Let (name, lambda, `Id "_")))
    |> String.concat ~sep:"\n"
  in
  begin
    if csv then
      printf "%s,%f,%s\n" name (Time.Span.to_sec solve_time) solutions_str
    else
      printf "Solved %s in %s. Solutions:\n%s\n\n"
        name (Time.Span.to_short_string solve_time) solutions_str;
    Out_channel.flush stdout;
    name, solve_time, solutions_str, desc
  end

let command =
  let spec =
    let open Command.Spec in
    empty
    (* +> flag "-t" ~aliases:["--table"] no_arg ~doc:" print out a result table in LaTeX format" *)
    +> flag "-c" ~aliases:["--csv"] no_arg ~doc:" print out results in csv format"
    +> flag "-v" ~aliases:["--verbose"] no_arg ~doc:" print progress messages while searching"
    +> flag "-V" ~aliases:["--very-verbose"] no_arg ~doc:" print _so many_ progress messages while searching"
    +> flag "-u" ~aliases:["--untyped"] no_arg ~doc:" use a type-unsafe exhaustive search"
    +> flag "-x" ~aliases:["--no-examples"] no_arg ~doc:" do not deduce examples when generalizing"
    +> flag "-i" ~aliases:["--infer-base"] no_arg ~doc:" infer the base case of folds (unsound)"
    (* +> flag "-r" ~aliases:["--repeat"] int ~doc:" repeat the synthesis n times and report the average runtime" *)
    +> flag "-s" ~aliases:["--stdin"] no_arg ~doc:" read specification from standard input"
    +> flag "-b" ~aliases:["--background"] (listed string) ~doc:" use background knowledge"
    +> anon (sequence ("testcase" %: string))
  in
  Command.basic
    ~summary:"Run test cases and print timing results"
    spec
    (fun csv verbose very_verbose untyped no_deduce
         infer_base use_stdin bk_strs testcase_names () ->
       let open Search in
       let config = {
         default_config with
         untyped; deduction=(not no_deduce); infer_base;
         verbosity =
           if verbose || very_verbose then
             if very_verbose then 2 else 1
           else 0;
       } in
       let m_testcases =
         (if
           use_stdin then [Testcase.from_channel In_channel.stdin]
          else
            List.map testcase_names ~f:(fun n -> Testcase.from_file ~filename:n))
         |> Or_error.all
       in
       match m_testcases with
       | Ok testcases ->
         List.iter testcases ~f:(fun case ->
             time_solve csv config case |> ignore)
       | Error err -> Error.to_string_hum err |> print_endline)

let () = Command.run command
