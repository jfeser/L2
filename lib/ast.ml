open Core
open Collections

exception ParseError of string

type id = Name.t [@@deriving compare, hash, sexp]

type const_typ = Num_t | Bool_t [@@deriving compare, hash, sexp]

type level = int [@@deriving compare, hash, sexp]

(** Represents the type of a value or expression. *)
type typ =
  | Const_t of const_typ
  | App_t of id * typ list
  | Arrow_t of typ list * typ
  | Var_t of var_typ ref
[@@deriving compare, sexp]

(** Type variables can be either free or quantified. A type scheme
cannot contain free type variables. *)
and var_typ = Free of int * level | Link of typ | Quant of id

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
[@@deriving compare, hash, sexp]

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
[@@deriving compare, hash, sexp]

type example = expr * expr [@@deriving compare, sexp]

type constr = expr * id list [@@deriving compare, sexp]

type 'a value =
  [ `Num of int | `Bool of bool | `List of 'a list | `Tree of 'a Tree.t ]
[@@deriving compare, hash, sexp]

type ivalue = ivalue value [@@deriving compare, hash, sexp]

type evalue = [ evalue value | `Unit | `Closure of expr * evalue Ctx.t ]
[@@deriving sexp]
