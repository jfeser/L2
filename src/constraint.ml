open Core.Std

open Ast
open Infer
open Util

type t = constr with compare, sexp

(** Parse a constraint from a string. *)
let of_string (s: string) : t =
  let lexbuf = Lexing.from_string s in
  try Parser.constr_eof Lexer.token lexbuf with
  | Parser.Error -> raise (Parser.ParseError s)
  | Lexer.SyntaxError _ -> raise (Parser.ParseError s)
  | Parsing.Parse_error -> raise (Parser.ParseError s)

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
