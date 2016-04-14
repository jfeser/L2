open Core.Std
open Core_extended.Std

let page_size = Int64.of_int 4096

type t = {
  user_time : Time_ns.Span.t;
  system_time : Time_ns.Span.t;
  memory_size : int64;
} [@@deriving sexp]

let seconds_of_jiffies js =
  let jps = Procfs.jiffies_per_second_exn () in
  let js_int = Big_int.int64_of_big_int js in
  Float.((Int64.to_float js_int) / jps)
  |> Core.Std.Time_ns.Span.of_sec

let of_pid pid =
  Option.map (Procfs.with_pid pid) ~f:(fun proc -> {
        user_time = seconds_of_jiffies
            proc.Procfs.Process.stat.Procfs.Process.Stat.utime;
        system_time = seconds_of_jiffies
            proc.Procfs.Process.stat.Procfs.Process.Stat.stime;
        memory_size =
          let rss =
            proc.Procfs.Process.stat.Procfs.Process.Stat.rss
            |> Big_int.int64_of_big_int
          in
          Int64.(rss * page_size);
      })

let to_string info = Sexp.to_string_hum (sexp_of_t info)
