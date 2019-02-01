open Core
open Collections

module T = struct
  type t =
    [ `Unit
    | `Num of int
    | `Bool of bool
    | `List of t list
    | `Tree of t Tree.t
    | `Closure of t * t Ctx.t
    | `Id of Expr.id
    | `Let of Expr.id * t * t
    | `Lambda of Expr.id list * t
    | `Apply of t * t list
    | `Op of Expr.Op.t * t list ]
  [@@deriving compare, sexp, bin_io]
end

include T

let rec to_string (e : t) : string =
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

let rec of_expr (e : Expr.t) : t =
  match e with
  | `Num x -> `Num x
  | `Bool x -> `Bool x
  | `Id x -> `Id x
  | `List x -> `List (List.map x ~f:of_expr)
  | `Tree x -> `Tree (Tree.map x ~f:of_expr)
  | `Op (op, args) -> `Op (op, List.map args ~f:of_expr)
  | `Let (x, y, z) -> `Let (x, of_expr y, of_expr z)
  | `Apply (x, y) -> `Apply (of_expr x, List.map y ~f:of_expr)
  | `Lambda (x, y) -> `Lambda (x, of_expr y)

let rec of_value : Value.t -> t = function
  | `Num x -> `Num x
  | `Bool x -> `Bool x
  | `List x -> `List (List.map x ~f:of_value)
  | `Tree x -> `Tree (Tree.map x ~f:of_value)
  | `Closure (x, ctx) -> `Closure (of_expr x, Ctx.map ctx ~f:of_value)
  | `Unit -> `Unit

let rec to_expr_exn : t -> Expr.t = function
  | `Num x -> `Num x
  | `Bool x -> `Bool x
  | `List x -> `List (List.map x ~f:to_expr_exn)
  | `Tree x -> `Tree (Tree.map x ~f:to_expr_exn)
  | `Op (op, args) -> `Op (op, List.map args ~f:to_expr_exn)
  | `Let (x, y, z) -> `Let (x, to_expr_exn y, to_expr_exn z)
  | `Apply (x, y) -> `Apply (to_expr_exn x, List.map y ~f:to_expr_exn)
  | `Lambda (x, y) -> `Lambda (x, to_expr_exn y)
  | e -> failwiths "Cannot convert to value." e [%sexp_of: t]

let rec to_value_exn : t -> Value.t = function
  | `Num x -> `Num x
  | `Bool x -> `Bool x
  | `Op (Expr.Op.Cons, [hd; tl]) as e -> (
    match to_value_exn tl with
    | `List tl' -> `List (to_value_exn hd :: tl')
    | _ -> failwiths "Cannot convert to value." e [%sexp_of: t] )
  | `List x -> `List (List.map x ~f:to_value_exn)
  | `Tree x -> `Tree (Tree.map x ~f:to_value_exn)
  | `Closure (x, ctx) -> `Closure (to_expr_exn x, Ctx.map ~f:to_value_exn ctx)
  | `Unit -> `Unit
  | e -> failwiths "Cannot convert to value." e [%sexp_of: t]

let to_value : t -> Value.t Or_error.t =
 fun e -> Or_error.try_with (fun () -> to_value_exn e)

include Comparable.Make (T)
