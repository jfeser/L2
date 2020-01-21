open! Core

type 'a t = 'a Map.M(Name).t ref [@@deriving compare, sexp]

exception UnboundError of Name.t

(** Return an empty context. *)
let empty () = ref (Map.empty (module Name))

(** Look up an id in a context. *)
let lookup ctx id = Map.find !ctx id

let lookup_exn ctx id =
  match lookup ctx id with Some v -> v | None -> raise (UnboundError id)

(** Bind a type or value to an id, returning a new context. *)
let bind ctx id data = ref (Map.set !ctx ~key:id ~data)

let bind_alist ctx alist =
  List.fold alist ~init:ctx ~f:(fun ctx' (id, data) -> bind ctx' id data)

(** Remove a binding from a context, returning a new context. *)
let unbind ctx id = ref (Map.remove !ctx id)

(** Bind a type or value to an id, updating the context in place. *)
let update ctx id data = ctx := Map.set !ctx ~key:id ~data

(** Remove a binding from a context, updating the context in place. *)
let remove ctx id = ctx := Map.remove !ctx id

let merge c1 c2 ~f = ref (Map.merge !c1 !c2 ~f)

let merge_right (c1 : 'a t) (c2 : 'a t) : 'a t =
  merge
    ~f:(fun ~key:_ v -> match v with `Both (_, v) | `Left v | `Right v -> Some v)
    c1 c2

let map ctx ~f = ref (Map.map !ctx ~f)

let mapi ctx ~f = ref (Map.mapi !ctx ~f)

let filter ctx ~f = ref (Map.filteri !ctx ~f)

let filter_mapi ctx ~f = ref (Map.filter_mapi !ctx ~f)

let equal cmp c1 c2 = Map.equal cmp !c1 !c2

let keys ctx = Map.keys !ctx

let data ctx = Map.data !ctx

let of_alist alist = ref (Map.of_alist alist)

let of_alist_exn alist = ref (Map.of_alist_exn (module Name) alist)

let of_alist_mult alist = ref (Map.of_alist_multi (module Name) alist)

let of_string_map = ref

let to_string_map ctx = !ctx

let to_alist ctx = Map.to_alist !ctx

let to_string (ctx : 'a t) (str : 'a -> string) : string =
  to_alist ctx
  |> List.map ~f:(fun (key, value) -> Name.to_string key ^ ": " ^ str value)
  |> String.concat ~sep:", "
  |> fun s -> "{ " ^ s ^ " }"

let of_ctx = ref

let to_ctx c = lazy !c
