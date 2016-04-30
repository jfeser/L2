open Core.Std

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

module Make : functor (PI : Process_info.S) -> S
