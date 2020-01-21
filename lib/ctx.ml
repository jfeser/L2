open! Core

type 'a t = 'a Map.M(Name).t [@@deriving compare, sexp]

(** Return an empty context. *)
let empty = Map.empty (module Name)

let merge_right =
  Map.merge ~f:(fun ~key:_ v ->
      match v with `Both (_, v) | `Left v | `Right v -> Some v)

let of_alist_exn x = Map.of_alist_exn (module Name) x

let to_string ctx str =
  Map.to_alist ctx
  |> List.map ~f:(fun (key, value) -> Name.to_string key ^ ": " ^ str value)
  |> String.concat ~sep:", "
  |> fun s -> "{ " ^ s ^ " }"
