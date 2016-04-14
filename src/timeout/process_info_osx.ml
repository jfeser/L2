open Core.Std
open Ctypes
open Foreign

(* let libproc = Dl.dlopen ~filename:"libproc.dylib" ~flags:[] *)

(* 
struct rusage_info_v3 {
	uint8_t  ri_uuid[16];
	uint64_t ri_user_time;
	uint64_t ri_system_time;
	uint64_t ri_pkg_idle_wkups;
	uint64_t ri_interrupt_wkups;
	uint64_t ri_pageins;
	uint64_t ri_wired_size;
	uint64_t ri_resident_size;	
	uint64_t ri_phys_footprint;
	uint64_t ri_proc_start_abstime;
	uint64_t ri_proc_exit_abstime;
	uint64_t ri_child_user_time;
	uint64_t ri_child_system_time;
	uint64_t ri_child_pkg_idle_wkups;
	uint64_t ri_child_interrupt_wkups;
	uint64_t ri_child_pageins;
	uint64_t ri_child_elapsed_abstime;
	uint64_t ri_diskio_bytesread;
	uint64_t ri_diskio_byteswritten;
	uint64_t ri_cpu_time_qos_default;
	uint64_t ri_cpu_time_qos_maintenance;
	uint64_t ri_cpu_time_qos_background;
	uint64_t ri_cpu_time_qos_utility;
	uint64_t ri_cpu_time_qos_legacy;
	uint64_t ri_cpu_time_qos_user_initiated;
	uint64_t ri_cpu_time_qos_user_interactive;
	uint64_t ri_billed_system_time;
	uint64_t ri_serviced_system_time;
};
*)

type rusage_info_v3
let rusage_info_v3 : rusage_info_v3 structure typ = structure "rusage_info_v3"
let ri_uuid = field rusage_info_v3 "ri_uuid" (array 16 uint8_t)
let ri_user_time = field rusage_info_v3 "ri_user_time" uint64_t
let ri_system_time = field rusage_info_v3 "ri_system_time" uint64_t
let ri_pkg_idle_wkups = field rusage_info_v3 "ri_pkg_idle_wkups" uint64_t
let ri_interrupt_wkups = field rusage_info_v3 "ri_interrupt_wkups" uint64_t
let ri_pageins = field rusage_info_v3 "ri_pageins" uint64_t
let ri_wired_size = field rusage_info_v3 "ri_wired_size" uint64_t
let ri_resident_size = field rusage_info_v3 "ri_resident_size" uint64_t	
let ri_phys_footprint = field rusage_info_v3 "ri_phys_footprint" uint64_t
let ri_proc_start_abstime = field rusage_info_v3 "ri_proc_start_abstime" uint64_t
let ri_proc_exit_abstime = field rusage_info_v3 "ri_proc_exit_abstime" uint64_t
let ri_child_user_time = field rusage_info_v3 "ri_child_user_time" uint64_t
let ri_child_system_time = field rusage_info_v3 "ri_child_system_time" uint64_t
let ri_child_pkg_idle_wkups = field rusage_info_v3 "ri_child_pkg_idle_wkups" uint64_t
let ri_child_interrupt_wkups = field rusage_info_v3 "ri_child_interrupt_wkups" uint64_t
let ri_child_pageins = field rusage_info_v3 "ri_child_pageins" uint64_t
let ri_child_elapsed_abstime = field rusage_info_v3 "ri_child_elapsed_abstime" uint64_t
let ri_diskio_bytesread = field rusage_info_v3 "ri_diskio_bytesread" uint64_t
let ri_diskio_byteswritten = field rusage_info_v3 "ri_diskio_byteswritten" uint64_t
let ri_cpu_time_qos_default = field rusage_info_v3 "ri_cpu_time_qos_default" uint64_t
let ri_cpu_time_qos_maintenance = field rusage_info_v3 "ri_cpu_time_qos_maintenance" uint64_t
let ri_cpu_time_qos_background = field rusage_info_v3 "ri_cpu_time_qos_background" uint64_t
let ri_cpu_time_qos_utility = field rusage_info_v3 "ri_cpu_time_qos_utility" uint64_t
let ri_cpu_time_qos_legacy = field rusage_info_v3 "ri_cpu_time_qos_legacy" uint64_t
let ri_cpu_time_qos_user_initiated = field rusage_info_v3 "ri_cpu_time_qos_user_initiated" uint64_t
let ri_cpu_time_qos_user_interactive = field rusage_info_v3 "ri_cpu_time_qos_user_interactive" uint64_t
let ri_billed_system_time = field rusage_info_v3 "ri_billed_system_time" uint64_t
let ri_serviced_system_time = field rusage_info_v3 "ri_serviced_system_time" uint64_t
let () = seal rusage_info_v3

(* typedef void *rusage_info_t; *)
type rusage_info_t = unit ptr
let rusage_info_t : rusage_info_t typ = ptr void

(* 
int proc_pid_rusage(int pid, int flavor, rusage_info_t *buffer) __OSX_AVAILABLE_STARTING(__MAC_10_9, __IPHONE_7_0);
*)

let proc_pid_rusage =
  foreign "proc_pid_rusage"
    (int @-> int @-> ptr rusage_info_t @-> returning int)

type t = {
  user_time: Time_ns.Span.t;
  system_time: Time_ns.Span.t;
  memory_size: int64;
} [@@deriving sexp]

let ticks_to_ns ticks = (Int.of_int64_exn ticks) * 100
let get_time_as_int info field =
  let user_time_ticks = getf info field |> Unsigned.UInt64.to_int64 in
  Time_ns.Span.of_int_ns (ticks_to_ns user_time_ticks)

let of_rusage_info_v3 info =
  {
    (* Assuming that ri_*_time fields are in 100ns ticks. *)
    user_time = get_time_as_int info ri_user_time;
    system_time = get_time_as_int info ri_system_time;

    memory_size = Unsigned.UInt64.to_int64 (getf info ri_resident_size);
  }

let of_pid pid =
  let info_v3_ptr = allocate_n rusage_info_v3 ~count:1 in
  let info_ptr = coerce (ptr rusage_info_v3) (ptr rusage_info_t) info_v3_ptr in
  let ret = proc_pid_rusage (Pid.to_int pid) 3 info_ptr in
  if ret = 0 then
    Some (of_rusage_info_v3 (!@ info_v3_ptr))
  else None

let to_string info = Sexp.to_string_hum (sexp_of_t info)
