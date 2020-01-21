open! Core

type 'a t = 'a Map.M(Name).t [@@deriving compare, sexp]

exception UnboundError of Name.t

(** Return an empty context. *)
let empty () = Map.empty (module Name)

(** Look up an id in a context. *)
let lookup ctx id = Map.find ctx id

let lookup_exn ctx id =
  match lookup ctx id with Some v -> v | None -> raise (UnboundError id)

(** Bind a type or value to an id, returning a new context. *)
let bind ctx id data = Map.set ctx ~key:id ~data

let bind_alist ctx alist =
  List.fold alist ~init:ctx ~f:(fun ctx' (id, data) -> bind ctx' id data)

(** Remove a binding from a context, returning a new context. *)
let unbind ctx id = Map.remove ctx id

let merge c1 c2 ~f = Map.merge c1 c2 ~f

let merge_right (c1 : 'a t) (c2 : 'a t) : 'a t =
  merge
    ~f:(fun ~key:_ v -> match v with `Both (_, v) | `Left v | `Right v -> Some v)
    c1 c2

let map ctx ~f = Map.map ctx ~f

let mapi ctx ~f = Map.mapi ctx ~f

let filter ctx ~f = Map.filteri ctx ~f

let filter_mapi ctx ~f = Map.filter_mapi ctx ~f

let equal cmp c1 c2 = Map.equal cmp c1 c2

let keys ctx = Map.keys ctx

let data ctx = Map.data ctx

let of_alist alist = Map.of_alist alist

let of_alist_exn alist = Map.of_alist_exn (module Name) alist

let of_alist_mult alist = Map.of_alist_multi (module Name) alist

let of_string_map = Fun.id

let to_string_map ctx = ctx

let to_alist ctx = Map.to_alist ctx

let to_string (ctx : 'a t) (str : 'a -> string) : string =
  to_alist ctx
  |> List.map ~f:(fun (key, value) -> Name.to_string key ^ ": " ^ str value)
  |> String.concat ~sep:", "
  |> fun s -> "{ " ^ s ^ " }"
