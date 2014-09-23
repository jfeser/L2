open Core.Std

open Ast
open Util

(** Module to manage built in operators and their metadata. *)
module Op = struct
  type t = op with compare, sexp

  (** Type for storing operator metadata. *)
  type metadata = {
    typ    : typ;
    commut : bool;
    assoc  : bool;
    str    : string;
  }

  let metadata_by_op = 
    let t = Util.parse_typ in
    [
      Plus,  { typ = t "(num, num) -> num"; commut = true;  assoc = true;  str = "+"; };
      Minus, { typ = t "(num, num) -> num"; commut = false; assoc = false; str = "-"; };
      Mul,   { typ = t "(num, num) -> num"; commut = true;  assoc = true;  str = "*"; };
      Div,   { typ = t "(num, num) -> num"; commut = false; assoc = false; str = "/"; };
      Mod,   { typ = t "(num, num) -> num"; commut = false; assoc = false; str = "%"; };
      Eq,    { typ = t "(a, a) -> bool"; commut = true;  assoc = false; str = "="; };
      Neq,   { typ = t "(a, a) -> bool"; commut = true;  assoc = false; str = "!="; };
      Lt,    { typ = t "(num, num) -> bool"; commut = false; assoc = false; str = "<"; };
      Leq,   { typ = t "(num, num) -> bool"; commut = false; assoc = false; str = "<="; };
      Gt,    { typ = t "(num, num) -> bool"; commut = false; assoc = false; str = ">"; };
      Geq,   { typ = t "(num, num) -> bool"; commut = false; assoc = false; str = ">="; };
      And,   { typ = t "(bool, bool) -> bool"; commut = true;  assoc = true;  str = "&"; };
      Or,    { typ = t "(bool, bool) -> bool"; commut = true;  assoc = true;  str = "|"; };
      Not,   { typ = t "(bool) -> bool"; commut = false; assoc = false; str = "~"; };
      If,    { typ = t "(bool, a, a) -> a"; commut = false; assoc = false; str = "if"; };
      Cons,  { typ = t "(a, list[a]) -> list[a]"; commut = false; assoc = false; str = "cons"; };
      Car,   { typ = t "(list[a]) -> a"; commut = false; assoc = false; str = "car"; };
      Cdr,   { typ = t "(list[a]) -> list[a]"; commut = false; assoc = false; str = "cdr"; };
      Tree,  { typ = t "(a, list[tree[a]]) -> tree[a]"; commut = false; assoc = false; str = "tree"};
      Children, { typ = t "(tree[a]) -> list[tree[a]]"; commut = false; assoc = false; str = "children" };
      Value, { typ = t "(tree[a]) -> a"; commut = false; assoc = false; str = "value" };
    ]

  let op_by_str = metadata_by_op
                  |> List.map ~f:(fun (op, meta) -> meta.str, op)
                  |> String.Map.of_alist_exn

  (** Get operator record from operator. *)
  let meta op = 
    let (_, meta) = List.find_exn metadata_by_op ~f:(fun (op', _) -> op = op') in
    meta

  let typ op = (meta op).typ
  let arity op = match (meta op).typ with
    | Arrow_t (args, _) -> List.length args
    | _ -> raise Not_found
  let assoc op = (meta op).assoc
  let commut op = (meta op).commut

  let to_string op = (meta op).str
  let of_string str = String.Map.find_exn op_by_str str
end

(** Calculate the size of an expression. *)
let rec size (e: expr) : int =
  let sum = List.fold_left ~init:0 ~f:(+) in
  match e with
  | `Id _
  | `Num _
  | `Bool _ -> 1
  | `Op (_, args) -> 1 + (sum (List.map args ~f:size))
  | `List l -> 1 + (sum (List.map l ~f:size))
  | `Tree t -> Tree.size t
  | `Let (_, a, b) -> 1 + size a + size b
  | `Lambda (args, body) -> 1 + (List.length args) + size body
  | `Apply (a, l) -> 1 + size a + (sum (List.map l ~f:size))

let normalize_expr (expr: expr) : expr = 
  let count = ref (-1) in
  let fresh_name () =
    let n = incr count; !count in
    let prefix = Char.of_int_exn ((n mod 26) + 97) in
    let suffix = if n >= 26 then Int.to_string ((n - 26) mod 26) else "" in
    Printf.sprintf "%c%s" prefix suffix
  in
  let rec norm ctx e =
    let norm_all = List.map ~f:(norm ctx) in
    match e with
    | `Num _
    | `Bool _ -> e
    | `Id x ->
       (match Ctx.lookup ctx x with
        | Some x' -> `Id x'
        | None -> `Id x)
    | `List x -> `List (norm_all x)
    | `Tree x -> `Tree (Tree.map x ~f:(norm ctx))
    | `Op (op, args) -> `Op (op, norm_all args)
    | `Apply (func, args) -> `Apply (norm ctx func, norm_all args)
    | `Let (name, x, y) ->
       let name' = fresh_name () in
       let ctx' = Ctx.bind ctx name name' in
       `Let (name', norm ctx' x, norm ctx' y)
    | `Lambda (args, body) ->
       let ctx', args' =
         List.fold_right args
                         ~init:(ctx, [])
                         ~f:(fun arg (ctx', args') ->
                             let arg' = fresh_name () in
                             Ctx.bind ctx' arg arg', arg'::args')
       in `Lambda (args', norm ctx' body)
  in norm (Ctx.empty ()) expr

(** Create an S-expression from the provided string list and brackets. *)
let sexp lb strs rb = lb ^ (String.concat ~sep:" " strs) ^ rb

(** Convert a type to a string. *)
let rec typ_to_string typ =
  let tlist_str typs =
    typs |> List.map ~f:typ_to_string |> String.concat ~sep:", "
  in
  match typ with
  | Const_t Num_t -> "num"
  | Const_t Bool_t -> "bool"
  | Var_t {contents = Free (id, _)} -> "ft" ^ (Int.to_string id)
  | Var_t {contents = Quant name} -> name
  | Var_t {contents = Link typ'} -> typ_to_string typ'
  | App_t (id, args) -> 
     Printf.sprintf "%s[%s]" id (tlist_str args)
  | Arrow_t ([arg], ret) -> 
     Printf.sprintf "(%s -> %s)" (typ_to_string arg) (typ_to_string ret)
  | Arrow_t (args, ret) -> 
     Printf.sprintf "((%s) -> %s)" (tlist_str args) (typ_to_string ret)

(** Convert and expression to a string. *)
let rec expr_to_string (expr: expr) : string =
  let str_all l = List.map ~f:expr_to_string l in
  match expr with
  | `Num x  -> Int.to_string x
  | `Bool true -> "#t"
  | `Bool false -> "#f"
  | `List x -> sexp "[" (List.map ~f:expr_to_string x) "]"
  | `Tree x -> Tree.to_string x ~str:expr_to_string
  | `Id x -> x
  | `Op (op, args) -> sexp "(" ((Op.to_string op)::(str_all args)) ")"
  | `Let (x, y, z) -> sexp "(" ["let"; x; expr_to_string y; expr_to_string z] ")"
  | `Apply (x, y)  -> sexp "(" ((expr_to_string x)::(str_all y)) ")"
  | `Lambda (args, body) -> sexp "(" ["lambda"; sexp "(" args ")"; expr_to_string body] ")"

let example_to_string (ex: example) : string =
  let e1, e2 = ex in
  (expr_to_string e1) ^ " -> " ^ (expr_to_string e2)

let equal_expr e1 e2 = (compare_expr e1 e2) = 0
