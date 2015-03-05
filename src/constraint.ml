open Core.Std

open Ast
open Infer
open Util

type t = constr with compare, sexp

let of_string (s: string) : t = parse_constr s
let to_string (x: t) : string =
  let e, names = x in
  let names_str = String.concat ~sep:" " names in
  sprintf "(forall (%s) %s)" names_str (Expr.to_string e)

let to_typed_expr (x: t) : typed_expr =
  let e, names = x in
  let ctx =
    List.fold_left
      ~f:(fun ctx name -> Ctx.bind ctx name (fresh_free 0))
      ~init:(Ctx.empty ()) names
  in
  infer ctx e
