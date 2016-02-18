open Core.Std

open Collections

type t = Ast.value [@@deriving compare, sexp]

module ExprValue = struct
  type t = [
    | `Unit
    | `Num of int
    | `Bool of bool
    | `List of t list
    | `Tree of t Tree.t
    | `Closure of t * (t Ctx.t)
    | `Id of Expr.id
    | `Let of Expr.id * t * t
    | `Lambda of Expr.id list * t
    | `Apply of t * (t list)
    | `Op of Expr.Op.t * (t list)
  ] [@@deriving compare, sexp]

  let rec to_string (e: t) : string =
    let list_to_string l = String.concat ~sep:" " (List.map ~f:to_string l) in
    match e with
    | `Num x -> Int.to_string x
    | `Bool true -> "#t"
    | `Bool false -> "#f"
    | `Id x -> x
    | `List x -> sprintf "[%s]" (list_to_string x)
    | `Tree x -> Tree.to_string x ~str:to_string
    | `Op (op, args) -> sprintf "(%s %s)" (Expr.Op.to_string op) (list_to_string args)
    | `Let (x, y, z) -> sprintf "(let %s %s %s)" x (to_string y) (to_string z)
    | `Apply (x, y) -> sprintf "(%s %s)" (to_string x) (list_to_string y)
    | `Lambda (args, body) ->
      sprintf "(lambda (%s) %s)" (String.concat ~sep:" " args) (to_string body)
    | `Closure _ -> "*closure*"
    | `Unit -> "unit"

  let rec of_expr (e: Expr.t) : t = match e with
    | `Num x -> `Num x
    | `Bool x -> `Bool x
    | `Id x -> `Id x
    | `List x -> `List (List.map x ~f:of_expr)
    | `Tree x -> `Tree (Tree.map x ~f:of_expr)
    | `Op (op, args) -> `Op (op, List.map args ~f:of_expr)
    | `Let (x, y, z) -> `Let (x, of_expr y, of_expr z)
    | `Apply (x, y) -> `Apply (of_expr x, List.map y ~f:of_expr)
    | `Lambda (x, y) -> `Lambda (x, of_expr y)

  let rec of_value e = match e with
    | `Num x -> `Num x
    | `Bool x -> `Bool x
    | `List x -> `List (List.map x ~f:of_value)
    | `Tree x -> `Tree (Tree.map x ~f:of_value)
    | `Closure (x, ctx) -> `Closure (of_expr x, Ctx.map ctx ~f:of_value)
    | `Unit -> `Unit
end

