open Core.Std

type variable =
  | Free of string
  | Input of int
  | Output
with sexp

type constant =
  | Bool of bool
  | Int of int
  | Nil
  | Bottom
with sexp

type term =
  | Constant of constant
  | Variable of variable
  | Apply of string * term list
with sexp

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

type specification = {
  phi : conjunct list;
  constraints : conjunct;
} with sexp

module type S = sig
  type variable =
    | Free of string
    | Input of int
    | Output
  with sexp

  type constant =
    | Bool of bool
    | Int of int
    | Nil
    | Bottom
  with sexp

  type term =
    | Constant of constant
    | Variable of variable
    | Apply of string * term list
  with sexp

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

  type specification = {
    phi : conjunct list;
    constraints : conjunct;
  } with sexp
end
