open Core.Std
open Core_extended
module Json = Yojson.Safe

module Make (PI : Process_info.S) = struct
  type result = {
    runtime : Time_ns.Span.t;
    peak_memory : Int64.t;
    status : [`Success | `Killed_memory | `Killed_runtime | `Exit_or_signal of Unix.Exit_or_signal.error ]
  }

  let ticks_per_second = 100
  let sleep_time = Float.(/) 1.0 (Float.of_int ticks_per_second)

  let peak_memory = ref Int64.min_value
  let start_time = ref Time_ns.epoch
  let end_time = ref Time_ns.epoch

  let check_limits (pid: Pid.t) (memory: int option) (time: Time_ns.Span.t option) : [`Ok | `Memory | `Runtime] =
    match PI.of_pid pid with
    | Some info ->
      let passed_memory = Option.value_map memory ~default:`Ok ~f:(fun limit ->
          if info.PI.memory_size <= (Int64.of_int limit) then `Ok else `Memory)
      in
      if passed_memory = `Ok then
        let passed_time = Option.value_map time ~default:`Ok ~f:(fun limit ->
            if Time_ns.diff (Time_ns.now ()) !start_time <= limit then `Ok else `Runtime)
        in
        passed_time
      else passed_memory
    | None -> failwith "ERROR: Getting process info failed.\n"

  let save_stats (pid: Pid.t) : unit =
    match PI.of_pid pid with
    | Some info ->
      if Int64.(>) info.PI.memory_size !peak_memory then
        peak_memory := info.PI.memory_size
    | None -> failwith "ERROR: Getting process info failed.\n"

  let print_stats result =
    begin match result.status with
      | `Success -> printf "Child exited with return code 0.\n";
      | `Exit_or_signal (`Exit_non_zero code) -> printf "Child exited with return code %d.\n" code
      | `Exit_or_signal (`Signal s) -> printf "Child received signal %s.\n" (Signal.to_string s)
      | `Killed_memory -> printf "Child killed for violating memory limit.\n"
      | `Killed_runtime -> printf "Child killed for violating runtime limit.\n"
    end;
    if result.peak_memory <> Int64.min_value then
      printf "Peak memory: %s Mb\n"
        (Int64.(/) !peak_memory (Int64.of_int 1000000) |> Int64.to_string);
    printf "Runtime: %s" (Time_ns.Span.to_short_string result.runtime)

  let print_machine result stdout_fn stderr_fn =
    let read_file fn = In_channel.with_file fn ~f:In_channel.input_all in
    `Assoc [
      "runtime", `Float (Time_ns.Span.to_sec result.runtime);
      "peak_memory", `Intlit (Int64.(/) !peak_memory (Int64.of_int 1000000) |> Int64.to_string);
      "status", `String begin match result.status with
        | `Success -> "success"
        | `Killed_memory -> "killed_memory"
        | `Killed_runtime -> "killed_runtime"
        | `Exit_or_signal _ -> "exited"
      end;
      "stdout", `String (read_file stdout_fn);
      "stderr", `String (read_file stderr_fn);
    ] |> Json.pretty_to_channel ~std:true Out_channel.stdout

  let get_result status =
    {
      status;
      runtime = Time_ns.diff !end_time !start_time;
      peak_memory = !peak_memory;
    }

  let rec run (pid: Pid.t) (memory_limit: int option) (time_limit: Time_ns.Span.t option) : result =
    save_stats pid;
    end_time := Time_ns.now ();
    match Unix.wait_nohang (`Pid pid) with
    (* If the child process has exited, check return value and return result. *)
    | Some (_, result) -> begin
        (match result with
         | Ok () -> get_result `Success
         | Error err -> get_result (`Exit_or_signal err));
      end

    (* If not, check whether child should be killed, otherwise sleep. *)
    | None ->
      begin
        match check_limits pid memory_limit time_limit with
        | `Ok ->
          let remaining_sleep = ref sleep_time in
          while !remaining_sleep > 0.0 do
            remaining_sleep := Unix.nanosleep sleep_time
          done;
          run pid memory_limit time_limit
        | `Memory ->
          Process.kill ~is_child:true pid;
          get_result `Killed_memory
        | `Runtime ->
          Process.kill ~is_child:true pid;
          get_result `Killed_runtime
      end

  let silence_output () =
    let null = Unix.openfile ~mode:[Unix.O_WRONLY] "/dev/null" in
    Unix.dup2 ~src:null ~dst:Unix.stdout;
    Unix.dup2 ~src:null ~dst:Unix.stderr

  let main
      (memory_limit: int option)
      (time_limit: float option)
      (machine_readable: bool)
      (silence_child: bool)
      (command: string list option)
      (_: unit) =
    match command with
    | Some (prog::args) -> begin
        let byte_limit = Option.map ~f:(fun mb -> mb * 1000000) memory_limit in
        let time_span_limit = Option.map ~f:Time_ns.Span.of_sec time_limit in
        
        let (stdout_fn, stdout_fd) = Unix.mkstemp "stdout" in
        let (stderr_fn, stderr_fd) = Unix.mkstemp "stderr" in
        at_exit (fun () -> Unix.remove stdout_fn; Unix.remove stderr_fn);
        
        start_time := Time_ns.now ();
        match Unix.fork () with
        | `In_the_child ->
          if silence_child then
            silence_output ()
          else if machine_readable then begin
            Unix.dup2 ~src:stdout_fd ~dst:Unix.stdout;
            Unix.dup2 ~src:stderr_fd ~dst:Unix.stderr;
          end;
          
          never_returns (Unix.exec ~prog ~args:(prog::args) ~use_path:true ())

        | `In_the_parent child_pid ->
          let result = run child_pid byte_limit time_span_limit in
          if machine_readable then
            print_machine result stdout_fn stderr_fn
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
