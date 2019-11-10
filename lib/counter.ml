open! Core

let debug = true

type count = Simple of int ref | Func of (unit -> int)

type counter_info = { count : count; desc : string }

type t = counter_info String.Table.t

let empty () = String.Table.create ()

let add_zero t name desc =
  if debug then Hashtbl.set t ~key:name ~data:{ count = Simple (ref 0); desc }
  else ()

let add_func t name desc f =
  if debug then Hashtbl.set t ~key:name ~data:{ count = Func f; desc } else ()

let get_count x =
  if debug then match x with Simple c -> !c | Func f -> f () else -1

let get t name = if debug then get_count (Hashtbl.find_exn t name).count else -1

let set t name v =
  if debug then
    match (Hashtbl.find_exn t name).count with
    | Simple c -> c := v
    | Func _ -> failwith "Cannot set a function counter."
  else ()

let incr t name =
  if debug then
    match (Hashtbl.find_exn t name).count with
    | Simple c -> incr c
    | Func _ -> failwith "Cannot incr a function counter."
  else ()

let to_strings : t -> string list =
 fun t ->
  Hashtbl.data t
  |> List.map ~f:(fun { desc = d; count = c } -> sprintf "%s: %d" d (get_count c))

(** Serialize a counter to JSON. This creates an object of the form
      \{ name: count, ... \}. *)
let to_json t =
  `Assoc
    ( Hashtbl.to_alist t
    |> List.map ~f:(fun (k, v) ->
           ( k,
             `Assoc
               [
                 ("count", `Int (get_count v.count)); ("description", `String v.desc);
               ] )) )
