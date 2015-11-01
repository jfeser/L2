module ProcessInfo :
  sig
    type t = {
      user_time : Core_kernel.Time_ns.Span.t;
      system_time : Core_kernel.Time_ns.Span.t;
      wired_size : int64;
      resident_size : int64;
    }
    val of_pid : Core_kernel.Pid.t -> t option
    val to_string : t -> string
  end
