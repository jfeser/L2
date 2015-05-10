open Core.Std

open Ast
open Collections

type t = typ with compare, sexp

(** Return the nesting depth of this type. For example, the type
    "int" has a nesting depth of 1, and the type "list[int]" has a
    nesting depth of 2. *)
let rec nesting_depth (t: t) : int =
  match t with
  | Const_t _ | Var_t _ -> 1
  | App_t (_, args) -> 1 + (List.max (List.map ~f:nesting_depth args))
  | Arrow_t (args, ret) ->
    let args_max = (List.max (List.map ~f:nesting_depth args)) in
    let ret_depth = nesting_depth ret in
    if args_max > ret_depth then args_max else ret_depth

(** Normalize a type by renaming each of its quantified type variables. *)
let normalize (t: t) : t =
  let count = ref (-1) in
  let fresh_name () = incr count; "t" ^ (Int.to_string !count) in
  let rec norm ctx typ = match typ with
    | Const_t _
    | Var_t {contents = Free _} -> typ
    | Var_t {contents = Link typ'} -> norm ctx typ'
    | Var_t {contents = Quant name} ->
      (match Ctx.lookup ctx name with
       | Some name' -> Var_t (ref (Quant name'))
       | None -> let name' = fresh_name () in
         Ctx.update ctx name name'; Var_t (ref (Quant name')))
    | App_t (const, args) -> App_t (const, List.map args ~f:(norm ctx))
    | Arrow_t (args, ret) -> Arrow_t (List.map args ~f:(norm ctx), norm ctx ret)
  in
  norm (Ctx.empty ()) t

(** Parse a type from a string. *)
let of_string (s: string) : t =
  let lexbuf = Lexing.from_string s in
  try Parser.typ_eof Lexer.token lexbuf with
  | Parser.Error -> raise (ParseError s)
  | Lexer.SyntaxError _ -> raise (ParseError s)
  | Parsing.Parse_error -> raise (ParseError s)

(** Convert a type to a string. *)
let rec to_string (t: t) : string =
  let tlist_str typs =
    typs |> List.map ~f:to_string |> String.concat ~sep:", "
  in
  match t with
  | Const_t Num_t -> "num"
  | Const_t Bool_t -> "bool"
  | Var_t {contents = Free (id, _)} -> "ft" ^ (Int.to_string id)
  | Var_t {contents = Quant name} -> name
  | Var_t {contents = Link typ'} -> to_string typ'
  | App_t (id, args) -> sprintf "%s[%s]" id (tlist_str args)
  | Arrow_t ([arg], ret) -> sprintf "(%s -> %s)" (to_string arg) (to_string ret)
  | Arrow_t (args, ret) -> sprintf "((%s) -> %s)" (tlist_str args) (to_string ret)
