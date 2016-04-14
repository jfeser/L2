open Core.Std

module type S = sig
  type t = {
    user_time : Time_ns.Span.t;
    system_time : Time_ns.Span.t;
    memory_size : int64;
  }

  include Sexpable.S with type t := t

  val of_pid : Pid.t -> t option
  val to_string : t -> string
end
