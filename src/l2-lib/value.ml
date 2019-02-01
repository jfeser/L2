open Core
open Collections

module T = struct
  type t = Ast.value [@@deriving compare]

  let rec sexp_of_t : t -> Sexp.t =
    let list x = Sexp.List x in
    let atom x = Sexp.Atom x in
    function
    | `Num x -> list [atom "Num"; [%sexp_of: int] x]
    | `Bool x -> list [atom "Bool"; [%sexp_of: bool] x]
    | `List x -> list [atom "List"; [%sexp_of: t list] x]
    | `Tree x -> list [atom "Tree"; [%sexp_of: t Tree.t] x]
    | `Closure (expr, ctx) ->
        let ctx_sexp = [%sexp_of: string list] (Ctx.keys ctx) in
        list [atom "Closure"; [%sexp_of: Expr.t] expr; ctx_sexp]
    | `Unit -> atom "Unit"

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
  | `Closure _ -> "<closure>"
  | `Unit -> "()"

include Comparable.Make (T)
