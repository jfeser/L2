open Core.Std

open Infer

module StaticDistance : sig
  type t

  include Sexpable.S with type t := t
  include Comparable.S with type t := t

  val increment_scope : t -> t
  val map_increment_scope : 'a Map.t -> 'a Map.t
  val create : distance:int -> index:int -> t
  val distance : t -> int
  val index : t -> int
  val args : int -> t list
  val to_string : t -> string
end

module Symbol : sig
  type t

  include Sexpable.S with type t := t
    
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val create : string -> t
end

module Hole : sig
  module Id : sig
    type t
    include Sexpable.S with type t := t
    include Comparable.S with type t := t
    include Stringable.S with type t := t
  end
  
  type t = {
    id : Id.t;
    ctx : Type.t StaticDistance.Map.t;
    type_ : Type.t;
    symbol : Symbol.t;
  }

  include Sexpable.S with type t := t
    
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val to_string : t -> string
  val create : Type.t StaticDistance.Map.t -> Type.t -> Symbol.t -> t
  val apply_unifier : Unifier.t -> t -> t
end

module Skeleton : sig
  type id =
    | StaticDistance of StaticDistance.t
    | Name of string
              
  type 'a t =
    | Num_h of int * 'a
    | Bool_h of bool * 'a
    | List_h of 'a t list * 'a
    | Tree_h of 'a t Collections.Tree.t * 'a
    | Id_h of id * 'a
    | Let_h of ('a t * 'a t) * 'a
    | Lambda_h of (int * 'a t) * 'a
    | Apply_h of ('a t * 'a t list) * 'a
    | Op_h of (Expr.Op.t * 'a t list) * 'a
    | Hole_h of Hole.t * 'a

  include Sexpable.S1 with type 'a t := 'a t
  val id_of_sexp : Sexp.t -> id
  val sexp_of_id : id -> Sexp.t
  val compare_id : id -> id -> int

  val equal : equal:('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val to_string_hum : 'a t -> string
  val to_expr :
    ?ctx:string StaticDistance.Map.t -> ?fresh_name:(unit -> string) -> (Hole.t -> Expr.t) ->
    'a t -> Expr.t
  val to_expr_exn :
    ?ctx:string StaticDistance.Map.t -> ?fresh_name:(unit -> string) -> 'a t -> Expr.t
  val of_expr : 'a -> Expr.t -> 'a t
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val hash : 'a -> int
  val fill_hole : Hole.t -> parent:'a t -> child:'a t -> 'a t
  val annotation : 'a t -> 'a
  val map_hole : f:(Hole.t * 'a -> 'a t) -> 'a t -> 'a t
  val map_annotation : f:('a -> 'a) -> 'a t -> 'a t
end

module Specification : sig
  module Examples : sig
    type t

    include Sexpable.S with type t := t

    val of_list : (Ast.value StaticDistance.Map.t * Ast.value) list -> t Or_error.t
    val of_list_exn : (Ast.value StaticDistance.Map.t * Ast.value) list -> t
    val to_list : t -> (Ast.value StaticDistance.Map.t * Ast.value) list

    val context : t -> StaticDistance.t list
  end

  module FunctionExamples : sig
    type t

    include Sexpable.S with type t := t
    
    val of_list : ((Ast.value StaticDistance.Map.t * Ast.value list) * Ast.value) list -> t Or_error.t
    val of_list_exn : ((Ast.value StaticDistance.Map.t * Ast.value list) * Ast.value) list -> t
    val to_list : t -> ((Ast.value StaticDistance.Map.t * Ast.value list) * Ast.value) list
  end
  
  type t =
    | Bottom
    | Top
    | Examples of Examples.t
    | FunctionExamples of FunctionExamples.t

  include Sexpable.S with type t := t

  val hash : t -> int
  val compare : t -> t -> int
  val to_string : t -> string
  val verify : t -> 'a Skeleton.t -> bool
  val increment_scope : t -> t
end

module type CostModel_Intf = sig
  val id_cost : Skeleton.id -> int
  val op_cost : Expr.Op.t -> int
  val lambda_cost : int
  val num_cost : int
  val bool_cost : int
  val hole_cost : int
  val let_cost : int
  val list_cost : int
  val tree_cost : int
end

module Hypothesis : sig
  type skeleton = Specification.t Skeleton.t

  type kind =
    | Abstract
    | Concrete

  type t

  include Sexpable with type t := t

  val skeleton : t -> skeleton
  val cost : t -> int
  val kind : t -> kind
  val holes : t -> (Hole.t * Specification.t) list
  val spec : t -> Specification.t

  val to_expr : t -> Expr.t
  val to_string : t -> string
  val to_string_hum : t -> string
  
  val compare_cost : t -> t -> int
  val apply_unifier : t -> Unifier.t -> t
  val fill_hole : Hole.t -> parent:t -> child:t -> t
  val verify : t -> bool

  (** Create a Hypothesis module that depends on a cost model. The
      functions that modify the hypothesis costs are located here. *)
  module Make : functor (CostModel : CostModel_Intf) -> sig
    val compute_cost : 'a Skeleton.t -> int
    val of_skeleton : skeleton -> t

    (** Constructors *)
    val num : int -> Specification.t -> t
    val bool : bool -> Specification.t -> t
    val id_sd : StaticDistance.t -> Specification.t -> t
    val id_name : string -> Specification.t -> t
    val hole : Hole.t -> Specification.t -> t
    val list : t list -> Specification.t -> t
    val tree : t Collections.Tree.t -> Specification.t -> t
    val _let : t * t -> Specification.t -> t
    val lambda : int * t -> Specification.t -> t
    val apply : t * t list -> Specification.t -> t
    val op : Ast.op * t list -> Specification.t -> t
  end
end
