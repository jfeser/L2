open Core.Std

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

  (** Remove a binding from a context, returning a new context. *)
  let unbind ctx id = ref (StringMap.remove !ctx id)

  (** Bind a type or value to an id, updating the context in place. *)
  let update ctx id data = ctx := StringMap.add !ctx ~key:id ~data:data

  (** Remove a binding from a context, updating the context in place. *)
  let remove ctx id = ctx := StringMap.remove !ctx id

  let merge c1 c2 ~f:f = ref (StringMap.merge !c1 !c2 ~f:f)
  let filter ctx ~f:f = ref (StringMap.filter !ctx ~f:f)
  let filter_mapi ctx ~f:f = ref (StringMap.filter_mapi !ctx ~f:f)

  let keys ctx = StringMap.keys !ctx

  let of_alist alist = ref (StringMap.of_alist alist)
  let of_alist_exn alist = ref (StringMap.of_alist_exn alist)
  let to_alist ctx = StringMap.to_alist !ctx
end

(** Represents the type of a value or expression. *)
type typ =
  | Num_t
  | Bool_t
  | Unit_t
  | List_t of typ
  | Arrow_t of (typ list) * typ with compare, sexp

(** Represents identifiers and typed identifiers. *)
type typed_id = id * typ with compare, sexp

(** Keys for each built in operator. Operator metadata is stored separately. *)
type op =
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
  | Cons
  | Car
  | Cdr
  | If
  | Map
  | Fold
  | Foldl
  | Filter with compare, sexp

(** Constants are a subset of expressions that does not allow names or
lambdas. *)
type const = [ `Num of int
             | `Bool of bool
             | `List of (const list) * typ ] with compare, sexp

(** An example is the application of a function to some constants and
the constant that should result. E.g. (f 1 2) -> 3 would be an example
for the function f. The target function can be applied to constants or
to recursive invocations of itself. (Invoking other functions cannot
be disallowed by the type system, but is not allowed.) *)
type const_app = [ const | `Apply of [`Id of id] * (const_app list) ] with compare, sexp
type example_lhs = [ `Apply of [ `Id of id ] * (const_app list) ] with compare, sexp
type example = example_lhs * const with compare, sexp

(** Types for expressions and values. *)
type expr = [ const
            | `Id of id
            | `Let of id * expr * expr
            | `Define of id * expr
            | `Lambda of typed_id list * typ * expr
            | `Apply of expr * (expr list)
            | `Op of op * (expr list) ] with compare, sexp

type function_def = [ `Define of id * [ `Lambda of typed_id list * typ * expr ] ]

type program = expr list

type constr = expr * (typed_id list)

type value = [ const
             | `Closure of expr * (value Ctx.t)
             | `Unit ]

type typed_expr = expr * typ with compare, sexp

 (** An evaluation context maps identifiers to values. *)
type type_ctx = typ String.Map.t ref

type type_pred = typ list -> typ -> bool

(** Type for storing operator metadata. *)
type op_data = {
  name   : op;
  arity  : int;
  commut : bool;
  assoc  : bool;
  str    : string;
  input_types : type_pred list;
}

(** Type predicates used to select operator arguments. *)
let match_num _ t = match t with Num_t -> true | _ -> false
let match_bool _ t = match t with Bool_t -> true | _ -> false
let match_list _ t = match t with List_t _ -> true | _ -> false
let match_any _ _ = true
let match_cons prev t = match t with
  | List_t ct -> (List.last_exn prev) = ct
  | _ -> false
let match_prev prev t = (List.last_exn prev) = t

let match_fold_f prev t = match prev, t with
  | [List_t et1], Arrow_t ([at1; et2], at2) -> (at1 = at2) && (et1 = et2)
  | _ -> false

let match_fold_init prev t = match prev with
  | [_; Arrow_t ([at1; _], at2)] -> (at1 = at2) && (t = at1)
  | _ -> false

let match_filter_f prev t = match prev, t with
  | [List_t et1], Arrow_t ([et2], Bool_t) -> et1 = et2
  | _ -> false

let match_map_f prev t = match prev, t with
  | [List_t et1], Arrow_t ([et2], _) -> et1 = et2
  | _ -> false

let operators = [
  { name = Plus;  arity = 2; commut = true; assoc = true;   str = "+";
    input_types = [match_num; match_num]; };
  { name = Minus; arity = 2; commut = false; assoc = false; str = "-";
    input_types = [match_num; match_num]; };
  { name = Mul;   arity = 2; commut = true; assoc = true;   str = "*";
    input_types = [match_num; match_num]; };
  { name = Div;   arity = 2; commut = false; assoc = false; str = "/";
    input_types = [match_num; match_num]; };
  { name = Mod;   arity = 2; commut = false; assoc = false; str = "%";
    input_types = [match_num; match_num]; };
  { name = Eq;    arity = 2; commut = true; assoc = false;  str = "=";
    input_types = [match_any; match_prev]; };
  { name = Neq;   arity = 2; commut = true; assoc = false;  str = "!=";
    input_types = [match_any; match_prev]; };
  { name = Lt;    arity = 2; commut = false; assoc = false; str = "<";
    input_types = [match_num; match_num]; };
  { name = Leq;   arity = 2; commut = false; assoc = false; str = "<=";
    input_types = [match_num; match_num]; };
  { name = Gt;    arity = 2; commut = false; assoc = false; str = ">";
    input_types = [match_num; match_num]; };
  { name = Geq;   arity = 2; commut = false; assoc = false; str = ">=";
    input_types = [match_num; match_num]; };
  { name = And;   arity = 2; commut = true; assoc = true;   str = "&";
    input_types = [match_bool; match_bool]; };
  { name = Or;    arity = 2; commut = true; assoc = true;   str = "|";
    input_types = [match_bool; match_bool]; };
  { name = Not;   arity = 1; commut = false; assoc = false; str = "~";
    input_types = [match_bool]; };
  { name = Cons;  arity = 2; commut = false; assoc = false; str = "cons";
    input_types = [match_any; match_cons]; };
  { name = Car;   arity = 1; commut = false; assoc = false; str = "car";
    input_types = [match_list]; };
  { name = Cdr;   arity = 1; commut = false; assoc = false; str = "cdr";
    input_types = [match_list]; };
  { name = If;    arity = 3; commut = false; assoc = false; str = "if";
    input_types = [match_bool; match_any; match_prev]; };
  { name = Fold;  arity = 3; commut = false; assoc = false; str = "fold";
    input_types = [match_list; match_fold_f; match_fold_init]; };
  { name = Foldl; arity = 3; commut = false; assoc = false; str = "foldl";
    input_types = [match_list; match_fold_f; match_fold_init]; };
  { name = Filter; arity = 2; commut = false; assoc = false; str = "filter";
    input_types = [match_list; match_filter_f]; };
  { name = Map; arity = 2; commut = false; assoc = false; str = "map";
    input_types = [match_list; match_filter_f]; };
]

(** Get operator record from operator name. *)
let operator_data op =
  match List.find ~f:(fun od -> od.name = op) operators with
  | Some op_data -> op_data
  | None -> raise Not_found

(** Get operator string from operator name. *)
let operator_to_str op = (operator_data op).str

(** Get operator arity from operator name. *)
let operator_to_arity op = (operator_data op).arity

(** Get operator name from operator string. *)
let operator_from_str op_str =
  match List.find ~f:(fun od -> od.str = op_str) operators with
  | Some op_data -> Some op_data.name
  | None -> None

(** Calculate the size of an expression. *)
let rec size (e: expr) : int =
  let sum_sizes = List.fold_left ~init:0 ~f:(fun acc e -> acc + size e) in
  match e with
  | `Id _
  | `Num _
  | `Bool _ -> 1
  | `Op (_, args) -> 1 + sum_sizes args
  | `List (l, _) -> 1 + (List.fold l ~init:0 ~f:(fun acc c -> acc + size (c :> expr)))
  | `Let (_, a, b) -> 1 + size a + size b
  | `Define (_, a) -> 1 + size a
  | `Lambda (args, _, expr) -> 1 + (List.length args) + size expr
  | `Apply (a, l) -> 1 + size a + sum_sizes l

(** Create an S-expression from the provided string list and brackets. *)
let sexp lb strs rb = lb ^ (String.concat ~sep:" " strs) ^ rb

(** Convert a type to a string. *)
let rec typ_to_string = function
  | Num_t -> "num"
  | Bool_t -> "bool"
  | Unit_t -> "unit"
  | List_t ct -> "[" ^ (typ_to_string ct) ^ "]"
  | Arrow_t (it, ot) ->
     (sexp "(" (List.map ~f:typ_to_string it) ")") ^ " -> " ^ (typ_to_string ot)

let rec const_to_string = function
  | `Num x -> Int.to_string x
  | `Bool true -> "#t"
  | `Bool false -> "#f"
  | `List ([], t) -> "[]:" ^ (typ_to_string t)
  | `List (x, _) -> sexp "[" (List.map ~f:const_to_string x) "]"

(** Convert and expression to a string. *)
let rec expr_to_string (e: expr) : string =
  let str_all l = List.map ~f:expr_to_string l in
  match e with
  | `Num x  -> const_to_string (`Num x)
  | `Bool x -> const_to_string (`Bool x)
  | `List x -> const_to_string (`List x)
  | `Id x -> x
  | `Op (op, args) -> sexp "(" ((operator_to_str op)::(str_all args)) ")"
  | `Let (x, y, z) -> sexp "(" ["let"; x; expr_to_string y; expr_to_string z] ")"
  | `Define (x, y) -> sexp "(" ["define"; x; expr_to_string y] ")"
  | `Apply (x, y)  -> sexp "(" ((expr_to_string x)::(str_all y)) ")"
  | `Lambda (x, y, z) ->
     let args_str = x
                    |> List.map ~f:(fun (n, t) -> n ^ ":" ^ typ_to_string t)
                    |> String.concat ~sep:" " in
     sexp "(" ["lambda"; "(" ^ args_str ^ "):" ^ (typ_to_string y); expr_to_string z] ")"

let prog_to_string p = List.map p ~f:expr_to_string |> String.concat ~sep:"\n"

let value_to_string (v: value) : string =
  match v with
  | `Num x  -> const_to_string (`Num x)
  | `Bool x -> const_to_string (`Bool x)
  | `List x -> const_to_string (`List x)
  | `Unit -> "unit"
  | `Closure (e, _) -> expr_to_string e

let example_to_string (ex: example) : string =
  let e1, e2 = ex in
  (expr_to_string (e1 :> expr)) ^ " -> " ^ (expr_to_string (e2 :> expr))
