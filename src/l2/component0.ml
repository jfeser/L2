open Core.Std

type sort =
  | Int
  | Bool
  | List
  | String
with sexp

type variable =
  | Free of string
  | Input of int
  | Output
with sexp, compare

type constant =
  | Bool of bool
  | Int of int
  | Nil
  | Bottom
with sexp, compare

type term =
  | Constant of constant
  | Variable of variable
  | Apply of string * term list
with sexp, compare

type binary_operator =
  | Eq
  | Neq
  | Gt
  | Lt
  | Ge
  | Le
  | Superset
  | Subset
  | NotSuperset
  | NotSubset
with sexp

type predicate =
  | Binary of binary_operator * term * term
with sexp

type conjunct = predicate list with sexp

type parsed_specification = conjunct * ((variable * sort) list)

(* module type S = sig *)
(*   type sort = *)
(*     | Int *)
(*     | Bool *)
(*     | List *)
(*     | String *)

(*   type variable = *)
(*     | Free of string *)
(*     | Input of int *)
(*     | Output *)
(*   with sexp, compare *)

(*   type constant = *)
(*     | Bool of bool *)
(*     | Int of int *)
(*     | Nil *)
(*     | Bottom *)
(*   with sexp, compare *)

(*   type term = *)
(*     | Constant of constant *)
(*     | Variable of variable *)
(*     | Apply of string * term list *)
(*   with sexp, compare *)

(*   type binary_operator = *)
(*     | Eq *)
(*     | Neq *)
(*     | Gt *)
(*     | Lt *)
(*     | Ge *)
(*     | Le *)
(*     | Superset *)
(*     | Subset *)
(*     | NotSuperset *)
(*     | NotSubset *)
(*   with sexp *)

(*   type predicate = *)
(*     | Binary of binary_operator * term * term *)
(*   with sexp *)

(*   type conjunct = predicate list with sexp *)
(* end *)
