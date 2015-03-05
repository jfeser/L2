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
    | Node (x, y) ->
       sprintf "{%s %s}" (str x) (String.concat ~sep:" " (List.map y ~f:(to_string ~str:str)))

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
  | If 
  | Cons
  | Car
  | Cdr
  | Tree
  | Value
  | Children
  with compare, sexp

type expr = 
  [ `Num of int
  | `Bool of bool
  | `List of expr list
  | `Tree of expr Tree.t
  | `Id of id
  | `Let of id * expr * expr
  | `Lambda of id list * expr
  | `Apply of expr * (expr list)
  | `Op of op * (expr list)
  ] with compare, sexp

type example = expr * expr with compare, sexp
type constr = expr * (id list) with compare, sexp
