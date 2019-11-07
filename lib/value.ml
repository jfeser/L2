open Core
open Collections

module T = struct
  type t = Ast.ivalue [@@deriving compare]

  let rec sexp_of_t : t -> Sexp.t =
    let list x = Sexp.List x in
    let atom x = Sexp.Atom x in
    function
    | `Num x -> list [ atom "Num"; [%sexp_of: int] x ]
    | `Bool x -> list [ atom "Bool"; [%sexp_of: bool] x ]
    | `List x -> list [ atom "List"; [%sexp_of: t list] x ]
    | `Tree x -> list [ atom "Tree"; [%sexp_of: t Tree.t] x ]

  let t_of_sexp : Sexp.t -> t =
   fun _ -> Or_error.unimplemented "Value.t_of_sexp" |> Or_error.ok_exn
end

include T

let rec to_string : t -> string = function
  | `Num x -> sprintf "%d" x
  | `Bool true -> "true"
  | `Bool false -> "false"
  | `Tree x -> Tree.to_string x ~str:to_string
  | `List x -> "[" ^ (List.map x ~f:to_string |> String.concat ~sep:"; ") ^ "]"

include Comparable.Make (T)

let rec of_evalue_exn = function
  | `Num x -> `Num x
  | `Bool x -> `Bool x
  | `List x -> `List (List.map ~f:of_evalue_exn x)
  | `Tree x -> `Tree (Tree.map ~f:of_evalue_exn x)
  | `Closure _ | `Unit -> failwith "Not an ivalue."

let rec to_evalue = function
  | `Num x -> `Num x
  | `Bool x -> `Bool x
  | `List x -> `List (List.map ~f:to_evalue x)
  | `Tree x -> `Tree (Tree.map ~f:to_evalue x)
