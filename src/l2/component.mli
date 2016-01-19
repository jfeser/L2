open Core.Std

open Collections
open Infer

module Z3_Defs : sig
  module Symbols :
    sig
      val list : Z3.context -> Z3.Symbol.symbol
      val string : Z3.context -> Z3.Symbol.symbol
      val len : Z3.context -> Z3.Symbol.symbol
      val subset : Z3.context -> Z3.Symbol.symbol
      val superset : Z3.context -> Z3.Symbol.symbol
    end

  module Sorts :
    sig
      val int : Z3.context -> Z3.Sort.sort
      val bool : Z3.context -> Z3.Sort.sort
      val list : Z3.context -> Z3.Sort.sort
      val string : Z3.context -> Z3.Sort.sort

      val mapping : Z3.context -> (Z3.Symbol.symbol * Z3.Sort.sort) list
    end

  module Functions :
    sig
      val len : Z3.context -> Z3.FuncDecl.func_decl
      val subset : Z3.context -> Z3.FuncDecl.func_decl
      val superset : Z3.context -> Z3.FuncDecl.func_decl

      val mapping : Z3.context -> (Z3.Symbol.symbol * Z3.FuncDecl.func_decl) list
    end
end

module Sort : sig
  type t =
    | Int
    | Bool
    | List
    | String
  with sexp, compare

  include Equal.S with type t := t

  val of_type : Type.t -> t Or_error.t
  val of_value : Ast.value -> t Or_error.t
  val of_values : Ast.value List.t -> t Or_error.t
  val to_z3 : Z3.context -> t -> Z3.Sort.sort
end

module Variable : sig
  type t =
    | Free of string
    | Input of int
    | Output
  with sexp, compare

  include Comparable.S with type t := t

  val to_z3 : Z3.context -> Z3.Sort.sort -> t -> Z3.Expr.expr
end

module Constant : sig
  type t =
    | Bool of bool
    | Int of int
    | Nil
    | Bottom
  with sexp, compare

  val to_z3 : Z3.context -> t -> Z3.Expr.expr Or_error.t
end
  
module Term : sig
  type t =
    | Constant of Constant.t
    | Variable of Variable.t
    | Apply of string * t list
  with sexp, compare

  include Comparable.S with type t := t
                 
  val evaluate : t Variable.Map.t -> t -> t Or_error.t
      
  val substitute : t Map.t -> t -> t
  val substitute_var : Variable.t Variable.Map.t -> t -> t
    
  val of_value : Ast.value -> t
  val to_z3 : Sort.t Variable.Map.t -> Z3.context -> t -> Z3.Expr.expr Or_error.t
end

module Predicate : sig
  type operator =
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
  with sexp, compare
      
  type t =
    | Binary of operator * Term.t * Term.t
  with sexp, compare
       
  val of_string : String.t -> t Or_error.t
  val substitute : Term.t Term.Map.t -> t -> t
  val substitute_var : Variable.t Variable.Map.t -> t -> t
  val evaluate : Term.t Variable.Map.t -> t -> Term.t Or_error.t
  val to_z3 : Sort.t Variable.Map.t -> Z3.context -> t -> Z3.Expr.expr Or_error.t
end                       

module Specification : sig
  type t = {
    constraints : Predicate.t list;
    sorts : Sort.t Variable.Map.t;
  } with sexp

  include Equal.S with type t := t
    
  val of_string : String.t -> t Or_error.t
      
  val top : t
    
  val of_examples : ?predicates:Predicate.t List.t ->
    Hypothesis.Specification.Examples.t -> t Hypothesis.StaticDistance.Map.t Or_error.t
  val to_z3 : Z3.context -> t -> Z3.Expr.expr list Or_error.t
  val substitute_var : Variable.t Variable.Map.t -> t -> t
end

type t = {
  name : string;
  spec : Specification.t;
  type_ : Type.t;
}

include Sexpable.S with type t := t

val create : string -> string -> string -> t Or_error.t
val stdlib : t String.Map.t
