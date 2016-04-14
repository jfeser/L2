open Core.Std
open Core_extended

module Make (PI : Process_info.S) = struct
  let ticks_per_second = 100
  let sleep_time = Float.(/) 1.0 (Float.of_int ticks_per_second)

  let peak_memory = ref Int64.min_value
  let start_time = ref Time_ns.epoch
  let end_time = ref Time_ns.epoch

  let check_limits (pid: Pid.t) (memory: int option) (time: Time_ns.Span.t option) : bool =
    match PI.of_pid pid with
    | Some info ->
      let passed_memory = match memory with
        | Some limit -> info.PI.memory_size <= (Int64.of_int limit)
        | None -> true
      in
      let passed_time = match time with
        | Some limit -> Time_ns.diff (Time_ns.now ()) !start_time <= limit
        | None -> true
      in
      passed_memory && passed_time
    | None -> (printf "ERROR: Getting process info failed.\n"; false)

  let save_stats (pid: Pid.t) : unit =
    match PI.of_pid pid with
    | Some info ->
      if Int64.(>) info.PI.memory_size !peak_memory then
        peak_memory := info.PI.memory_size
    | None -> printf "ERROR: Getting process info failed.\n"

  let print_stats () =
    if !peak_memory <> Int64.min_value then
      printf "Peak memory: %s Mb\n"
        (Int64.(/) !peak_memory (Int64.of_int 1000000) |> Int64.to_string);
    let runtime = Time_ns.diff !end_time !start_time in
    printf "Runtime: %s" (Time_ns.Span.to_short_string runtime)

  let rec run (pid: Pid.t) (memory_limit: int option) (time_limit: Time_ns.Span.t option) : unit =
    match Unix.wait_nohang (`Pid pid) with
    | Some (_, result) -> begin
        end_time := Time_ns.now ();
        (match result with
         | Ok () -> printf "Child exited with return code 0.\n"
         | Error err -> begin
             match err with
             | `Exit_non_zero code -> printf "Child exited with return code %d.\n" code
             | `Signal s -> printf "Child received signal %s.\n" (Signal.to_string s)
           end);
        print_stats ()
      end
    | None ->
      save_stats pid;
      if check_limits pid memory_limit time_limit then begin
        let remaining_sleep = ref sleep_time in
        while !remaining_sleep > 0.0 do
          remaining_sleep := Unix.nanosleep sleep_time
        done;
        run pid memory_limit time_limit
      end else begin
        printf "Killing child process...\n";
        Process.kill ~is_child:true pid
      end

  let silence_output () =
    let null = Unix.openfile ~mode:[Unix.O_WRONLY] "/dev/null" in
    Unix.dup2 ~src:null ~dst:Unix.stdout;
    Unix.dup2 ~src:null ~dst:Unix.stderr

  let main
      (memory_limit: int option)
      (time_limit: int option)
      (silence_child: bool)
      (command: string list option)
      (_: unit) =
    match command with
    | Some (prog::args) -> begin
        let byte_limit = Option.map ~f:(fun mb -> mb * 1000000) memory_limit in
        let time_span_limit =
          Option.map ~f:(fun sec -> Time_ns.Span.of_int_sec sec) time_limit
        in
        start_time := Time_ns.now ();
        match Unix.fork () with
        | `In_the_child ->
          if silence_child then silence_output ();
          never_returns (Unix.exec ~prog ~args:(prog::args) ~use_path:true ())
        | `In_the_parent child_pid -> 
          run child_pid byte_limit time_span_limit
      end
    | None | Some [] -> printf "Error: No command specified."

  let () =
    let spec =
      let open Command.Spec in
      empty
      +> flag "-m" ~aliases:["--memory"] (optional int) ~doc:" process memory limit (Mb) (default: unlimited)"
      +> flag "-t" ~aliases:["--time"] (optional int) ~doc:" process time limit (sec) (default: unlimited)"
      +> flag "-q" ~aliases:["--quiet"] no_arg ~doc:" silence all output from the child process"
      +> flag "--" escape ~doc:" use the remaining arguments as the command to run"
    in
    let command = Command.basic ~summary:"Run a command with time and memory limits." spec main in
    Command.run command
end
