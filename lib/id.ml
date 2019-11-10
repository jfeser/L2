open! Core

module Make () = struct
  module T = struct
    type t = { id : int; name : string [@compare.ignore] }
    [@@deriving compare, hash, sexp]
  end

  include T
  include Comparator.Make (T)

  module O : Comparisons.Infix with type t := t = Comparable.Make (T)

  let table = Hashtbl.create (module String)

  let ctr = ref 0

  let of_string s =
    match Hashtbl.find table s with
    | Some id -> id
    | None ->
        incr ctr;
        let id = { id = !ctr; name = s } in
        Hashtbl.set table ~key:s ~data:id;
        id

  let to_string { name; _ } = name

  let pp fmt x = Format.fprintf fmt "%s" x.name

  let fmt () x = sprintf "%s" x.name
end
