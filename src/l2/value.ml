open Core.Std

type t = Ast.value [@@deriving compare]

let rec sexp_of_t : t -> Sexp.t =
  let list = fun x -> Sexp.List x in
  let atom = fun x -> Sexp.Atom x in
  function
  | `Num x -> list [atom "Num"; [%sexp_of:int] x]
  | `Bool x -> list [atom "Bool"; [%sexp_of:bool] x]
  | `List x -> list [atom "List"; [%sexp_of:t list] x]
  | `Tree x -> list [atom "Tree"; [%sexp_of:t Collections.Tree.t] x]
  | `Closure (expr, ctx) ->
    let ctx_sexp = [%sexp_of:string list] (Collections.Ctx.keys ctx) in
    list [atom "Closure"; [%sexp_of:Expr.t] expr; ctx_sexp]
  | `Unit -> atom "Unit"

