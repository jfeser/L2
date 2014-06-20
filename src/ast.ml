open Core.Std

(** Represents the type of a value or expression. *)
type typ =
  | Num_t
  | Bool_t
  | Unit_t
  | List_t of typ
  | Nil_t
  | Arrow_t of (typ list) * typ

 (** Represents identifiers. *)
 and id = string

 (** Typed identifiers and typed expressions. *)
 and typed_id = id * typ
 and typed_expr = expr * typ

 (** Keys for each built in operator. Operator metadata is stored
 separately. *)
 and op =
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
   | Foldl

 (** Types for expressions and values. *)
 and expr = [ `Num of int 
            | `Bool of bool 
            | `List of expr list 
            | `Nil 
            | `Id of id 
            | `Let of id * expr * expr 
            | `Define of id * expr 
            | `Lambda of typed_id list * expr 
            | `Apply of expr * (expr list) 
            | `Op of op * (expr list) ]
 and value = [ `Num of int
             | `Bool of bool 
             | `List of value list 
             | `Nil 
             | `Closure of expr * eval_ctx
             | `Unit ]

 (** An evaluation context maps identifiers to values. *)
 and eval_ctx = value String.Map.t ref
 and type_ctx = typ String.Map.t ref

 and type_pred = typ list -> typ -> bool

(** Type for storing operator metadata. *)
type op_data = {
  name   : op;
  arity  : int;
  commut : bool;
  assoc  : bool;
  str    : string;
  input_types : (typ list -> typ -> bool) list;
}

(** Determine whether t1 and t2 are compatible types. *)
let rec type_equal t1 t2 = match t1 with
  | Num_t  -> (match t2 with 
               | Num_t -> true 
               | Bool_t | Unit_t | List_t _ | Nil_t | Arrow_t _ -> false)
  | Bool_t -> (match t2 with 
               | Bool_t -> true 
               | Num_t | Unit_t | List_t _ | Nil_t | Arrow_t _ -> false)
  | Nil_t  -> (match t2 with 
               | List_t _ | Nil_t -> true 
               | Num_t | Bool_t | Unit_t | Arrow_t _ -> false)
  | Unit_t -> (match t2 with 
               | Unit_t -> true 
               | Num_t | Bool_t | List_t _ | Nil_t | Arrow_t _ -> false)
  | List_t ct1 -> (match t2 with
                   | List_t ct2 -> type_equal ct1 ct2 
                   | Nil_t -> true
                   | Num_t | Bool_t | Unit_t | Arrow_t _ -> false)
  | Arrow_t (it1, ot1) -> 
     (match t2 with 
      | Arrow_t (it2, ot2) -> 
         (type_equal ot1 ot2) &&
           (match List.zip it1 it2 with
            | Some it -> List.for_all it ~f:(fun (i1, i2) -> type_equal i1 i2)
            | None -> false)
      | Num_t | Bool_t | Unit_t | List_t _ | Nil_t -> false)

(** Type predicates used to select operator arguments. *)
let match_num _ t = match t with Num_t -> true | _ -> false
let match_bool _ t = match t with Bool_t -> true | _ -> false
let match_list _ t = match t with  Nil_t | List_t _ -> true | _ -> false
let match_any _ _ = true
let match_cons prev t = match t with
  | Nil_t -> true
  | List_t ct -> (List.last_exn prev) = ct
  | _ -> false
let match_prev prev t = (List.last_exn prev) = t

let match_foldl_f prev t = match prev, t with
  | [Nil_t], Arrow_t ([at1; _], at2) -> type_equal at1 at2
  | [List_t et1], Arrow_t ([at1; et2], at2) -> (type_equal at1 at2) &&
                                                 (type_equal et1 et2)
  | _ -> false

let match_foldl_init prev t = match prev with
  | [_; Arrow_t ([at1; _], at2)] -> (type_equal at1 at2) && (type_equal t at1)
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
  { name = Foldl; arity = 3; commut = false; assoc = false; str = "foldl";
    input_types = [match_list; match_foldl_f; match_foldl_init]; };
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
let rec size e =
  let sum_sizes = List.fold_left ~init:0 ~f:(fun acc e -> acc + size e) in
  match e with
  | `Id _
  | `Num _
  | `Bool _ 
  | `Nil -> 1
  | `Op (_, args) -> 1 + sum_sizes args
  | `List l -> 1 + sum_sizes l
  | `Let (_, a, b) -> 1 + size a + size b
  | `Define (_, a) -> 1 + size a
  | `Lambda (args, expr) -> 1 + (List.length args) + size expr
  | `Apply (a, l) -> 1 + size a + sum_sizes l

(** Create an S-expression from the provided string list and brackets. *)
let sexp lb strs rb = lb ^ (String.concat ~sep:" " strs) ^ rb

(** Convert a type to a string. *)
let rec typ_to_string t =
  let str_all l = List.map ~f:typ_to_string l in
  match t with
  | Num_t -> "num"
  | Bool_t -> "bool"
  | Unit_t -> "unit"
  | Nil_t -> "nil"
  | List_t ct -> "[" ^ (typ_to_string ct) ^ "]"
  | Arrow_t (it, ot) -> 
     (sexp "(" (str_all it) ")") ^ " -> " ^ (typ_to_string ot)

(** Convert and expression to a string. *)
let rec expr_to_string e =
  let str_all l = List.map ~f:expr_to_string l in
  match e with
  | `Id x -> x
  | `Num x -> Int.to_string x
  | `Bool x -> Bool.to_string x
  | `Nil -> "nil"
  | `Op (op, args) -> sexp "(" ((operator_to_str op)::(str_all args)) ")"
  | `List l -> sexp "[" (str_all l) "]"
  | `Let (x, y, z) -> 
     sexp "(" ["let"; x; expr_to_string y; expr_to_string z] ")"
  | `Define (x, y) -> sexp "(" ["define"; x; expr_to_string y] ")"
  | `Lambda (x, y) ->
     let arg_strs l = List.map ~f:(fun (n, t) -> n ^ ":" ^ typ_to_string t) l in
     sexp "(" ["lambda"; sexp "(" (arg_strs x) ")"; expr_to_string y] ")"
  | `Apply (x, y) -> sexp "(" ((expr_to_string x)::(str_all y)) ")"

let rec value_to_string v = 
  let str_all l = List.map ~f:value_to_string l in
  match v with
  | `Id x -> x
  | `Num x -> Int.to_string x
  | `Bool x -> Bool.to_string x
  | `Nil -> "nil"
  | `Unit -> "unit"
  | `List l -> sexp "[" (str_all l) "]"
  | `Closure (e, _) -> expr_to_string e
