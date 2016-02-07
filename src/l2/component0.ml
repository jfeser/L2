open Core.Std

type sort =
  | Int
  | Bool
  | List
  | String
[@@deriving sexp]

type variable =
  | Free of string
  | Input of int
  | Output
[@@deriving sexp, compare]

type constant =
  | Bool of bool
  | Int of int
  | Nil
[@@deriving sexp, compare]

type term =
  | Constant of constant
  | Variable of variable
  | Apply of string * term list
[@@deriving sexp, compare]

type parsed_specification = term * ((variable * sort) list)
