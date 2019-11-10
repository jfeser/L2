open! Core

(** Module for creating fresh names and numbers. *)

let count = ref (-1)

let int () =
  incr count;
  !count

let name prefix = Printf.sprintf "%s%d" prefix (int ()) |> Name.of_string

let names prefix num = List.range 0 num |> List.map ~f:(fun _ -> name prefix)

(** Create a function for returning fresh integers. *)
let mk_fresh_int_fun () =
  let count = ref (-1) in
  fun () ->
    incr count;
    let n = !count in
    if n < 0 then failwith "Out of fresh integers." else n

(** Create a function for returning fresh names. These names will be
    of the form [a-z][0-9]*. *)
let mk_fresh_name_fun () =
  let fresh_int = mk_fresh_int_fun () in
  fun () ->
    let n = fresh_int () in
    let prefix = Char.of_int_exn ((n mod 26) + 97) in
    let suffix = if n >= 26 then Int.to_string ((n - 26) mod 26) else "" in
    Printf.sprintf "%c%s" prefix suffix |> Name.of_string
