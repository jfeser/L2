open Collections

type status = {synthesis: Counter.t; hashcons: Counter.t}

val enable : unit -> unit

val disable : unit -> unit

val print_status : status -> unit
