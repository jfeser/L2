open Core.Std

module Tree = struct
  type 'a t =
    | Empty
    | Node of 'a * 'a t list
    with compare, sexp
    
  let rec to_string t ~str =
    match t with
    | Empty -> "{}"
    | Node (x, []) -> sprintf "{%s}" (str x)
    | Node (x, y) -> sprintf "{%s %s}" (str x) (String.concat ~sep:" " (List.map y ~f:(to_string ~str:str)))

  let rec size = function
    | Empty -> 1
    | Node (_, c) -> List.fold ~init:1 (List.map c ~f:size) ~f:(+)

  let rec map (t: 'a t) ~f : 'b t = match t with
    | Empty -> Empty
    | Node (x, children) -> Node (f x, List.map children ~f:(map ~f:f))

  let rec equal t1 t2 ~cmp = match t1, t2 with
    | Empty, Empty -> true
    | Node (x1, c1), Node (x2, c2) -> 
       if cmp x1 x2
       then (match List.zip c1 c2 with
             | Some pairs -> List.for_all pairs ~f:(fun (ce1, ce2) -> equal ce1 ce2 ~cmp:cmp)
             | None -> false)
       else false
    | _ -> false

  let rec flatten (t: 'a t) : 'a list = match t with
    | Empty -> []
    | Node (x, y) -> [x] @ List.concat_map y ~f:flatten
end

type id = string with compare, sexp

module Ctx = struct
  module StringMap = Map.Make(String)
  type 'a t = 'a StringMap.t ref
  exception UnboundError of id

  (** Return an empty context. *)
  let empty () : 'a t = ref StringMap.empty

  (** Look up an id in a context. *)
  let lookup ctx id = StringMap.find !ctx id
  let lookup_exn ctx id = match lookup ctx id with
    | Some v -> v
    | None -> raise (UnboundError id)

  (** Bind a type or value to an id, returning a new context. *)
  let bind ctx id data = ref (StringMap.add !ctx ~key:id ~data:data)
  let bind_alist ctx alist = 
    List.fold alist ~init:ctx ~f:(fun ctx' (id, data) -> bind ctx' id data)

  (** Remove a binding from a context, returning a new context. *)
  let unbind ctx id = ref (StringMap.remove !ctx id)

  (** Bind a type or value to an id, updating the context in place. *)
  let update ctx id data = ctx := StringMap.add !ctx ~key:id ~data:data

  (** Remove a binding from a context, updating the context in place. *)
  let remove ctx id = ctx := StringMap.remove !ctx id

  let merge c1 c2 ~f:f = ref (StringMap.merge !c1 !c2 ~f:f)
  let map ctx ~f:f = ref (StringMap.map !ctx ~f:f)
  let filter ctx ~f:f = ref (StringMap.filter !ctx ~f:f)
  let filter_mapi ctx ~f:f = ref (StringMap.filter_mapi !ctx ~f:f)

  let keys ctx = StringMap.keys !ctx

  let of_alist alist = ref (StringMap.of_alist alist)
  let of_alist_exn alist = ref (StringMap.of_alist_exn alist)
  let to_alist ctx = StringMap.to_alist !ctx
  let to_string ctx (str: 'a -> string) =
    to_alist ctx
    |> List.map ~f:(fun (key, value) -> key ^ ": " ^ (str value))
    |> String.concat ~sep:", "
    |> fun s -> "{ " ^ s ^ " }"
end

(** Represents the type of a value or expression. *)
type typ =
  | Const_t of const_typ
  | App_t of id * typ list
  | Arrow_t of typ list * typ
  | Var_t of var_typ ref
and const_typ = Num_t | Bool_t

(** Type variables can be either free or quantified. A type scheme
cannot contain free type variables. *)
and var_typ =
  | Free of int * level
  | Link of typ
  | Quant of string
and level = int
with compare, sexp

(** Module to manage built in operators and their metadata. *)
module Op = struct
  type t =
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
    | Cons
    | Car
    | Cdr
    | Tree
    | Value
    | Children
    with compare, sexp

  (** Type for storing operator metadata. *)
  type metadata = {
    typ    : typ;
    commut : bool;
    assoc  : bool;
    str    : string;
  }

  let metadata_by_op = 
    let quant name = ref (Quant name) in
    [
    Plus,  { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Num_t);
             commut = true;  assoc = true;  str = "+"; };
    Minus, { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Num_t);
             commut = false; assoc = false; str = "-"; };
    Mul,   { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Num_t);
             commut = true;  assoc = true;  str = "*"; };
    Div,   { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Num_t);
             commut = false; assoc = false; str = "/"; };
    Mod,   { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Num_t);
             commut = false; assoc = false; str = "%"; };
    Eq,    { typ = Arrow_t ([Var_t (quant "a"); Var_t (quant "a")], Const_t Bool_t);
             commut = true;  assoc = false; str = "="; };
    Neq,   { typ = Arrow_t ([Var_t (quant "a"); Var_t (quant "a")], Const_t Bool_t);
             commut = true;  assoc = false; str = "!="; };
    Lt,    { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Bool_t);
             commut = false; assoc = false; str = "<"; };
    Leq,   { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Bool_t);
             commut = false; assoc = false; str = "<="; };
    Gt,    { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Bool_t);
             commut = false; assoc = false; str = ">"; };
    Geq,   { typ = Arrow_t ([Const_t Num_t; Const_t Num_t], Const_t Bool_t);
             commut = false; assoc = false; str = ">="; };
    And,   { typ = Arrow_t ([Const_t Bool_t; Const_t Bool_t], Const_t Bool_t);
             commut = true;  assoc = true;  str = "&"; };
    Or,    { typ = Arrow_t ([Const_t Bool_t; Const_t Bool_t], Const_t Bool_t);
             commut = true;  assoc = true;  str = "|"; };
    Not,   { typ = Arrow_t ([Const_t Bool_t], Const_t Bool_t);
             commut = false; assoc = false; str = "~"; };
    If,    { typ = Arrow_t ([Const_t Bool_t; Var_t (quant "a"); Var_t (quant "a")], Var_t (quant "a"));
             commut = false; assoc = false; str = "if"; };
    Cons,  { typ = Arrow_t ([Var_t (quant "a"); App_t ("list", [Var_t (quant "a")])], 
                            App_t ("list", [Var_t (quant "a")]));
             commut = false; assoc = false; str = "cons"; };
    Car,   { typ = Arrow_t ([App_t ("list", [Var_t (quant "a")])], Var_t (quant "a"));
             commut = false; assoc = false; str = "car"; };
    Cdr,   { typ = Arrow_t ([App_t ("list", [Var_t (quant "a")])], App_t ("list", [Var_t (quant "a")]));
             commut = false; assoc = false; str = "cdr"; };
    Tree,  { typ = Arrow_t ([Var_t (quant "a"); App_t ("list", [App_t ("tree", [Var_t (quant "a")])])],
                            App_t ("tree", [Var_t (quant "a")]));
             commut = false; assoc = false; str = "tree"};
    Children, { typ = Arrow_t ([App_t ("tree", [Var_t (quant "a")])],
                               App_t ("list", [App_t ("tree", [Var_t (quant "a")])]));
                commut = false; assoc = false; str = "children" };
    Value, { typ = Arrow_t ([App_t ("tree", [Var_t (quant "a")])], Var_t (quant "a"));
             commut = false; assoc = false; str = "value" };
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

type expr = 
  [ `Num of int
  | `Bool of bool
  | `List of expr list
  | `Tree of expr Tree.t
  | `Id of id
  | `Let of id * expr * expr
  | `Lambda of id list * expr
  | `Apply of expr * (expr list)
  | `Op of Op.t * (expr list)
  ] with compare, sexp

type example = expr * expr with compare, sexp
type constr = expr * (id list)

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
