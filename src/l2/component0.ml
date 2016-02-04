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
with sexp, compare

type term =
  | Constant of constant
  | Variable of variable
  | Apply of string * term list
with sexp, compare

type parsed_specification = term * ((variable * sort) list)
