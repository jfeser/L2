open Core.Std

open Ast
open Collections

module Hole : sig
  type t = {
    id : int;
    ctx : typ Ctx.t;
    type_ : typ;
  }
  val to_sexp : t -> Sexp.t
  val of_sexp : Sexp.t -> t
  val to_string : t -> string
  val compare : t -> t -> int
  val create : typ Ctx.t -> typ -> t
end

module Skeleton : sig
  type 'a t =
      Num_h of int * 'a
    | Bool_h of bool * 'a
    | List_h of 'a t list * 'a
    | Tree_h of 'a t Tree.t * 'a
    | Id_h of id * 'a
    | Let_h of (id * 'a t * 'a t) * 'a
    | Lambda_h of (id list * 'a t) * 'a
    | Apply_h of ('a t * 'a t list) * 'a
    | Op_h of (op * 'a t list) * 'a
    | Hole_h of Hole.t * 'a

  val of_sexp : (Sexp.t -> 'a) -> Sexp.t -> 'a t
  val to_sexp : ('a -> Sexp.t) -> 'a t -> Sexp.t

  val to_string_hum : 'a t -> string
  val to_expr : 'a t -> Expr.t
                          
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val hash : 'a -> int
  val fill_hole : Hole.t -> parent:('a t) -> child:('a t) -> 'a t
  val annotation : 'a t -> 'a
end

module Specification : sig
  type t =
      Bottom
    | Top
    | Examples of (value Ctx.t * value) list
    | FunctionExamples of (value Ctx.t * value list * value) list

  val of_sexp : Sexp.t -> t
  val to_sexp : t -> Sexp.t

  val to_string : t -> string
  
  val hash : 'a -> int
  val compare : t -> t -> int
  val verify : t -> expr -> bool
end

module Hypothesis : sig
  type kind = Abstract | Concrete
  type t = {
    skeleton : Specification.t Skeleton.t Hashcons.hash_consed;
    cost : int;
    kind : kind;
    holes : (Hole.t * Specification.t) list;
  }

  val num : int -> Specification.t -> t
  val bool : bool -> Specification.t -> t
  val id : id -> Specification.t -> t
  val hole : Hole.t -> Specification.t -> t
  val list : t list -> Specification.t -> t
  val tree : t Collections.Tree.t -> Specification.t -> t
  val _let : id * t * t -> Specification.t -> t
  val lambda : id list * t -> Specification.t -> t
  val apply : t * t list -> Specification.t -> t
  val op : Ast.op * t list -> Specification.t -> t
    
  val compare_cost : t -> t -> int
  val spec : t -> Specification.t
  val to_expr : t -> Expr.t
  val to_string : t -> string
  val fill_hole : Hole.t -> parent:t -> child:t -> t
end

val generate_concrete_hypotheses :
  Hole.t -> Specification.t -> Hypothesis.t list
val generate_abstract_hypotheses :
  Hole.t -> Specification.t -> Hypothesis.t list
type result = Solution of Hypothesis.t | NoSolution
exception SynthesisException of result
val synthesize : Hypothesis.t -> result
