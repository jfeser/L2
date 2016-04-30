open Core.Std
module Json = Yojson.Safe

module Make (Process : Limited_process.S) = struct
  let print_stats result =
    print_newline ();
    begin match result.Process.status with
      | `Success -> printf "Child exited with return code 0.\n";
      | `Exit_or_signal (`Exit_non_zero code) -> printf "Child exited with return code %d.\n" code
      | `Exit_or_signal (`Signal s) -> printf "Child received signal %s.\n" (Signal.to_string s)
      | `Killed_memory -> printf "Child killed for violating memory limit.\n"
      | `Killed_runtime -> printf "Child killed for violating runtime limit.\n"
    end;
    if result.Process.peak_memory <> Int64.min_value then
      printf "Peak memory: %s Mb\n"
        (Int64.(/) result.Process.peak_memory (Int64.of_int 1000000) |> Int64.to_string);
    printf "Runtime: %s" (Time_ns.Span.to_short_string result.Process.runtime)

  let print_machine result =
    let read_file fn = In_channel.with_file fn ~f:In_channel.input_all in
    `Assoc [
      "runtime", `Float (Time_ns.Span.to_sec result.Process.runtime);
      "peak_memory", `Intlit (Int64.(/) result.Process.peak_memory (Int64.of_int 1000000) |> Int64.to_string);
      "status", `String begin match result.Process.status with
        | `Success -> "success"
        | `Killed_memory -> "killed_memory"
        | `Killed_runtime -> "killed_runtime"
        | `Exit_or_signal _ -> "exited"
      end;
      "stdout", `String (read_file (Option.value_exn result.Process.stdout_fn));
      "stderr", `String (read_file (Option.value_exn result.Process.stderr_fn));
    ] |> Json.pretty_to_channel ~std:true Out_channel.stdout
  
  let main
      (memory_limit: int option)
      (time_limit: float option)
      (machine_readable: bool)
      (silence_child: bool)
      (command: string list option)
      (_: unit) =
    match command with
    | Some (prog::args) -> begin
        let mem_limit = Option.map ~f:(fun mb -> mb * 1000000) memory_limit in
        let time_limit = Option.map ~f:Time_ns.Span.of_sec time_limit in
        let output =
          if silence_child then `None else
          if machine_readable then `Saved else `Standard
        in
        let result = Process.run ~output ?mem_limit ?time_limit (`Program (prog, args)) in
        if machine_readable then
          print_machine result
        else
          print_stats result
      end
    | None | Some [] -> failwith "Error: No command specified."

  let () =
    let spec =
      let open Command.Spec in
      empty
      +> flag "-m" ~aliases:["--memory"] (optional int) ~doc:" process memory limit (Mb) (default: unlimited)"
      +> flag "-t" ~aliases:["--time"] (optional float) ~doc:" process time limit (sec) (default: unlimited)"
      +> flag "--machine-readable" no_arg ~doc:" produce a summary in machine readable format"
      +> flag "-q" ~aliases:["--quiet"] no_arg ~doc:" silence all output from the child process"
      +> flag "--" escape ~doc:" use the remaining arguments as the command to run"
    in
    let command = Command.basic ~summary:"Run a command with time and memory limits." spec main in
    Command.run command
end
