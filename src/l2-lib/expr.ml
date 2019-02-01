open Core
open Printf
open Ast
open Collections
open Util

module Map = Core.Map.Make (struct
  type t = expr [@@deriving compare, sexp]
end)

type t = Ast.expr [@@deriving compare, sexp]

type id = Ast.id [@@deriving compare, sexp, bin_io]

(** Module to manage built in operators and their metadata. *)
module Op = struct
  module Map = Core.Map.Make (struct
    type t = op

    let t_of_sexp = op_of_sexp

    let sexp_of_t = sexp_of_op

    let compare = compare_op
  end)

  type t = Ast.op =
    | Plus
    | Minus
    | Mul
    | Div
    | Mod
    | Eq
    | Neq
    | Lt
    | Leq
    | Gt
    | Geq
    | And
    | Or
    | Not
    | If
    | RCons
    | Cons
    | Car
    | Cdr
    | Tree
    | Value
    | Children
  [@@deriving compare, sexp, bin_io, hash]

  (** Type for storing operator metadata. *)
  type metadata = {typ: typ; commut: bool; assoc: bool; str: string; cost: int}

  let equal o1 o2 = compare_op o1 o2 = 0

  let hash = Hashtbl.hash

  let metadata_by_op =
    let t s =
      let lexbuf = Lexing.from_string s in
      try Parser_sexp.typ_eof Lexer_sexp.token lexbuf with
      | Parser_sexp.Error -> raise (ParseError s)
      | Lexer_sexp.SyntaxError _ -> raise (ParseError s)
      | Parsing.Parse_error -> raise (ParseError s)
    in
    [ ( Plus
      , {typ= t "(num, num) -> num"; commut= true; assoc= true; str= "+"; cost= 1}
      )
    ; ( Minus
      , {typ= t "(num, num) -> num"; commut= false; assoc= false; str= "-"; cost= 1}
      )
    ; ( Mul
      , {typ= t "(num, num) -> num"; commut= true; assoc= true; str= "*"; cost= 1}
      )
    ; ( Div
      , {typ= t "(num, num) -> num"; commut= false; assoc= false; str= "/"; cost= 1}
      )
    ; ( Mod
      , {typ= t "(num, num) -> num"; commut= false; assoc= false; str= "%"; cost= 1}
      )
    ; (Eq, {typ= t "(a, a) -> bool"; commut= true; assoc= false; str= "="; cost= 1})
    ; ( Neq
      , {typ= t "(a, a) -> bool"; commut= true; assoc= false; str= "!="; cost= 1} )
    ; ( Lt
      , {typ= t "(num, num) -> bool"; commut= false; assoc= false; str= "<"; cost= 1}
      )
    ; ( Leq
      , { typ= t "(num, num) -> bool"
        ; commut= false
        ; assoc= false
        ; str= "<="
        ; cost= 1 } )
    ; ( Gt
      , {typ= t "(num, num) -> bool"; commut= false; assoc= false; str= ">"; cost= 1}
      )
    ; ( Geq
      , { typ= t "(num, num) -> bool"
        ; commut= false
        ; assoc= false
        ; str= ">="
        ; cost= 1 } )
    ; ( And
      , {typ= t "(bool, bool) -> bool"; commut= true; assoc= true; str= "&"; cost= 1}
      )
    ; ( Or
      , {typ= t "(bool, bool) -> bool"; commut= true; assoc= true; str= "|"; cost= 1}
      )
    ; ( Not
      , {typ= t "(bool) -> bool"; commut= false; assoc= false; str= "~"; cost= 1} )
    ; ( If
      , {typ= t "(bool, a, a) -> a"; commut= false; assoc= false; str= "if"; cost= 1}
      )
    ; ( RCons
      , { typ= t "(list[a], a) -> list[a]"
        ; commut= false
        ; assoc= false
        ; str= "rcons"
        ; cost= 1 } )
    ; ( Cons
      , { typ= t "(a, list[a]) -> list[a]"
        ; commut= false
        ; assoc= false
        ; str= "cons"
        ; cost= 1 } )
    ; ( Car
      , {typ= t "(list[a]) -> a"; commut= false; assoc= false; str= "car"; cost= 1}
      )
    ; ( Cdr
      , { typ= t "(list[a]) -> list[a]"
        ; commut= false
        ; assoc= false
        ; str= "cdr"
        ; cost= 1 } )
    ; ( Tree
      , { typ= t "(a, list[tree[a]]) -> tree[a]"
        ; commut= false
        ; assoc= false
        ; str= "tree"
        ; cost= 1 } )
    ; ( Children
      , { typ= t "(tree[a]) -> list[tree[a]]"
        ; commut= false
        ; assoc= false
        ; str= "children"
        ; cost= 1 } )
    ; ( Value
      , {typ= t "(tree[a]) -> a"; commut= false; assoc= false; str= "value"; cost= 1}
      ) ]
    |> Map.of_alist_exn

  let all = Map.keys metadata_by_op

  let control = [If]

  let cmp = [Eq; Neq; Lt; Leq; Gt; Geq]

  let logic = [And; Or; Not]

  let list = [Cons; Car; Cdr]

  let tree = [Tree; Children; Value]

  let simple_arith = [Plus; Minus]

  let arith = [Plus; Minus; Mul; Div; Mod]

  let op_by_str =
    metadata_by_op |> Map.to_alist
    |> List.map ~f:(fun (op, meta) -> (meta.str, op))
    |> String.Map.of_alist_exn

  (** Get operator record from operator. *)
  let meta = Map.find_exn metadata_by_op

  let typ op = (meta op).typ

  let arity op =
    match (meta op).typ with
    | Arrow_t (args, _) -> List.length args
    | _ -> failwith "Not a function."

  let assoc op = (meta op).assoc

  let commut op = (meta op).commut

  let cost op = (meta op).cost

  let to_string op = (meta op).str

  let of_string str = String.Map.find_exn op_by_str str
end

let rec cost ?(op_cost = Op.cost) (e : t) : int =
  let sum = List.fold_left ~init:0 ~f:( + ) in
  match e with
  | `Id _ | `Num _ | `Bool _ -> 1
  | `Op (op, args) -> op_cost op + sum (List.map args ~f:cost)
  | `List l -> 1 + sum (List.map l ~f:cost)
  | `Tree t -> Tree.size t
  | `Let (_, a, b) -> 1 + cost a + cost b
  | `Lambda (args, body) -> 1 + List.length args + cost body
  | `Apply (a, l) -> 1 + cost a + sum (List.map l ~f:cost)

let size = cost ~op_cost:(fun _ -> 1)

let normalize ?(bound = String.Set.empty) (expr : t) : expr =
  let fresh_name = Fresh.mk_fresh_name_fun () in
  let rec norm ctx e =
    let norm_all = List.map ~f:(norm ctx) in
    match e with
    | `Num _ | `Bool _ -> e
    | `Id x -> (
      match Ctx.lookup ctx x with
      | Some x' -> `Id x'
      | None -> if String.Set.mem bound x then `Id x else `Id (fresh_name ()) )
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
          List.fold_right args ~init:(ctx, []) ~f:(fun arg (ctx', args') ->
              let arg' = fresh_name () in
              (Ctx.bind ctx' arg arg', arg' :: args') )
        in
        `Lambda (args', norm ctx' body)
  in
  norm (Ctx.empty ()) expr

let rec of_value = function
  | `Num x -> `Num x
  | `Bool x -> `Bool x
  | `List x -> `List (List.map ~f:of_value x)
  | `Tree x -> `Tree (Tree.map ~f:of_value x)
  | `Unit -> failwith "Tried to convert unit to expression."
  | `Closure _ -> failwith "Tried to convert closure to expression."

(** Parse an expression from a string. *)
let of_string_exn ?(syntax = `Sexp) (s : string) : t =
  let lexbuf = Lexing.from_string s in
  try
    match syntax with
    | `Sexp -> Parser_sexp.expr_eof Lexer_sexp.token lexbuf
    | `Ml -> Parser_ml.expr_ml_eof Lexer_ml.token lexbuf
  with
  | Parser_sexp.Error -> raise (ParseError s)
  | Lexer_sexp.SyntaxError _ -> raise (ParseError s)
  | Parser_ml.Error -> raise (ParseError s)
  | Lexer_ml.SyntaxError _ -> raise (ParseError s)
  | Parsing.Parse_error -> raise (ParseError s)

let of_string ?(syntax = `Sexp) (s : string) : t Or_error.t =
  try Ok (of_string_exn ~syntax s) with ParseError s ->
    error "Parsing Expr.t failed." s [%sexp_of: string]

(** Convert an expression to a string. *)
let rec to_string (expr : t) : string =
  let list_to_string l = String.concat ~sep:" " (List.map ~f:to_string l) in
  match expr with
  | `Num x -> Int.to_string x
  | `Bool true -> "#t"
  | `Bool false -> "#f"
  | `Id x -> x
  | `List x -> sprintf "[%s]" (list_to_string x)
  | `Tree x -> Tree.to_string x ~str:to_string
  | `Op (op, args) -> sprintf "(%s %s)" (Op.to_string op) (list_to_string args)
  | `Let (x, y, z) -> sprintf "(let %s %s %s)" x (to_string y) (to_string z)
  | `Apply (x, y) -> sprintf "(%s %s)" (to_string x) (list_to_string y)
  | `Lambda (args, body) ->
      sprintf "(lambda (%s) %s)" (String.concat ~sep:" " args) (to_string body)

let equal (e1 : t) (e2 : t) = compare_expr e1 e2 = 0

(** Return true if all the names in an expression are free. *)
let all_abstract (e : t) : bool =
  let rec f (b : String.Set.t) (e : t) : bool =
    match e with
    | `Num _ | `Bool _ | `List [] -> false
    | `Id x -> not (String.Set.mem b x)
    | `List x -> List.for_all ~f:(f b) x
    | `Tree x -> Tree.flatten x |> List.for_all ~f:(f b)
    | `Op (_, x) -> List.for_all ~f:(f b) x
    | `Let (x, y, z) ->
        let b' = String.Set.add b x in
        f b' y && f b' z
    | `Apply (x, y) -> f b x && List.for_all ~f:(f b) y
    | `Lambda (_, x) -> f b x
  in
  f String.Set.empty e
