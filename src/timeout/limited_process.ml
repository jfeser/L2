open Core.Std
open Core_extended

module type S = sig
  type result = {
    runtime : Time_ns.Span.t;
    peak_memory : Int64.t;
    status : [
      | `Exit_or_signal of Unix.Exit_or_signal.error
      | `Killed_memory
      | `Killed_runtime
      | `Success
    ];
    stdout_fn : string option;
    stderr_fn : string option;
  }

  val run :
    ?output:[ `None | `Saved | `Standard ]
    -> ?mem_limit:int
    -> ?time_limit:Time_ns.Span.t
    -> [ `Program of (string * string list) | `Closure of unit -> unit ]
    -> result
end

module Make (PI : Process_info.S) : S = struct
  type result = {
    runtime : Time_ns.Span.t;
    peak_memory : Int64.t;
    status : [`Success | `Killed_memory | `Killed_runtime | `Exit_or_signal of Unix.Exit_or_signal.error ];
    stdout_fn : string option;
    stderr_fn : string option;
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

  let get_result status =
    {
      status;
      stdout_fn = None;
      stderr_fn = None;
      runtime = Time_ns.diff !end_time !start_time;
      peak_memory = !peak_memory;
    }

  let rec wait_for_child memory_limit time_limit pid = 
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
          wait_for_child memory_limit time_limit pid
        | `Memory ->
          Process.kill ~is_child:true pid;
          get_result `Killed_memory
        | `Runtime ->
          Process.kill ~is_child:true pid;
          get_result `Killed_runtime
      end

  let rec run = fun ?(output=`Standard) ?mem_limit ?time_limit runnable ->
    (* Generate temporary files for the child's output. *)
    let (stdout_fn, stdout_fd) = Unix.mkstemp "/tmp/stdout" in
    let (stderr_fn, stderr_fd) = Unix.mkstemp "/tmp/stderr" in

    start_time := Time_ns.now ();
    
    match Unix.fork () with
    | `In_the_child ->
      begin match output with
        | `None ->
          let null = Unix.openfile ~mode:[Unix.O_WRONLY] "/dev/null" in
          Unix.dup2 ~src:null ~dst:Unix.stdout;
          Unix.dup2 ~src:null ~dst:Unix.stderr
        | `Saved ->
          Unix.dup2 ~src:stdout_fd ~dst:Unix.stdout;
          Unix.dup2 ~src:stderr_fd ~dst:Unix.stderr
        | `Standard -> ()
      end;

      begin match runnable with
        | `Program (program, args) ->
          never_returns (Unix.exec ~prog:program ~args:(program::args) ~use_path:true ())
        | `Closure func -> func (); exit 0
      end

    | `In_the_parent child_pid ->
      let result = wait_for_child mem_limit time_limit child_pid in
      let result = if output = `Saved then
          { result with stdout_fn = Some stdout_fn; stderr_fn = Some stderr_fn; }
        else result
      in
      start_time := Time_ns.epoch;
      end_time := Time_ns.epoch;
      peak_memory := Int64.min_value;
      result
end
