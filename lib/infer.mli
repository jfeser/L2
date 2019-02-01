open Core
open Ast
open Collections

exception TypeError of Error.t

val total_infer_time : Time.Span.t ref

module Type : sig
  type const = const_typ = Num_t | Bool_t

  type level = int

  type t = typ =
    | Const_t of const_typ
    | App_t of id * typ list
    | Arrow_t of typ list * typ
    | Var_t of var_typ ref

  and var = var_typ = Free of int * level | Link of typ | Quant of string

  include Sexpable.S with type t := t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val nesting_depth : t -> int

  val normalize : t -> t

  val are_unifiable : t -> t -> bool

  val arity : t -> int

  val of_string_exn : string -> t

  val of_string : string -> t Or_error.t

  val to_string : t -> string

  val of_expr : ?ctx:t String.Map.t -> Expr.t -> t * t Int.Map.t

  val num : t

  val bool : t

  val list : t -> t

  val tree : t -> t

  val quant : id -> t

  val free : int -> level -> t

  val arrow1 : t -> t -> t

  val arrow2 : t -> t -> t -> t
end

module Unifier : sig
  type t = Type.t Int.Map.t

  include Sexpable.S with type t := t

  val empty : t

  val apply : t -> Type.t -> Type.t

  val compose : outer:t -> inner:t -> t

  val equal : t -> t -> bool

  val relevant_to : t -> Type.t -> t

  val of_types_exn : Type.t -> Type.t -> t

  val of_types : Type.t -> Type.t -> t option

  val to_alist : t -> (int * Type.t) list

  val of_alist_exn : (int * Type.t) list -> t

  val to_string : t -> string
end

module ImmutableType : sig
  type t =
    | Const_i of const_typ
    | App_i of id * t list
    | Arrow_i of t list * t
    | Quant_i of string
    | Free_i of int * level

  include Sexpable.S with type t := t

  module Table : Hashtbl.S with type key = t

  val compare : t -> t -> int

  val hash : t -> int

  val of_type : Type.t -> t

  val to_type : t -> Type.t
end

module TypedExpr : sig
  type t =
    | Num of int * Type.t
    | Bool of bool * Type.t
    | List of t list * Type.t
    | Tree of t Tree.t * Type.t
    | Id of id * Type.t
    | Let of (id * t * t) * Type.t
    | Lambda of (id list * t) * Type.t
    | Apply of (t * t list) * Type.t
    | Op of (Expr.Op.t * t list) * Type.t

  include Comparable.S with type t := t

  include Sexpable.S with type t := t

  val normalize : t -> t

  val map : f:(Type.t -> Type.t) -> t -> t

  val to_expr : t -> Expr.t

  val to_type : t -> Type.t

  val to_string : t -> string
end

val fresh_free : int -> Type.t

val normalize : Type.t -> Type.t

val occurs : int -> int -> Type.t -> unit

val generalize : int -> Type.t -> Type.t

val instantiate : ?ctx:Type.t Ctx.t -> int -> Type.t -> Type.t

val unify_exn : Type.t -> Type.t -> unit

val unify : Type.t -> Type.t -> Type.t option

val is_unifiable : Type.t -> Type.t -> bool

val typeof : Type.t Ctx.t -> int -> Expr.t -> TypedExpr.t

val stdlib_tctx : Type.t Ctx.t

val infer_exn : Type.t Ctx.t -> Expr.t -> TypedExpr.t

val infer : Type.t Ctx.t -> Expr.t -> TypedExpr.t Or_error.t

val typed_expr_of_string : string -> TypedExpr.t

val stdlib_names : String.Set.t

val free : ?bound:String.Set.t -> TypedExpr.t -> (string * Type.t) list
