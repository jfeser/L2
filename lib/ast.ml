open Core
open Collections

exception ParseError of string

type id = string [@@deriving compare, sexp, bin_io]

(** Represents the type of a value or expression. *)
type typ =
  | Const_t of const_typ
  | App_t of id * typ list
  | Arrow_t of typ list * typ
  | Var_t of var_typ ref

and const_typ = Num_t | Bool_t

(** Type variables can be either free or quantified. A type scheme
cannot contain free type variables. *)
and var_typ = Free of int * level | Link of typ | Quant of string

and level = int [@@deriving compare, sexp]

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
  | RCons
  | Cons
  | Car
  | Cdr
  | Tree
  | Value
  | Children
[@@deriving compare, sexp]

type expr =
  [ `Num of int
  | `Bool of bool
  | `List of expr list
  | `Tree of expr Tree.t
  | `Id of id
  | `Let of id * expr * expr
  | `Lambda of id list * expr
  | `Apply of expr * expr list
  | `Op of op * expr list ]
[@@deriving compare, sexp]

type example = expr * expr [@@deriving compare, sexp]

type constr = expr * id list [@@deriving compare, sexp]

type value =
  [ `Num of int
  | `Bool of bool
  | `List of value list
  | `Tree of value Tree.t
  | `Closure of expr * value Ctx.t
  | `Unit ]
[@@deriving compare, sexp]
