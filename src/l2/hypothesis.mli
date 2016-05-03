open Core.Std
open Collections

open Infer

(** Modules for constructing hypotheses. *)

(** Static distance coordinates. *)
module StaticDistance : sig
  type t

  include Sexpable.S with type t := t
  include Comparable.S with type t := t

  (** Increment the scope of a coordinate. *)
  val increment_scope : t -> t

  (** Increment the scope of every coordinate in a Map.t. *)
  val map_increment_scope : 'a Map.t -> 'a Map.t

  (** Create a static distance coordinate.
      @param distance The distance of the coordinate from its binding site, in number of bindings.
      @param index The binding index. *)
  val create : distance:int -> index:int -> t

  (** Get the distance of a static distance coordinate. *)
  val distance : t -> int

  (** Get the index of a static distance coordinate. *)
  val index : t -> int

  (** Generate an arguments list with {i n} arguments. *)
  val args : int -> t list

  (** Convert static distance coordinate to string. *)
  val to_string : t -> string
end

(** Symbols are constant strings with a fast comparison function. Used
    as identifiers. *)
module Symbol : sig
  type t

  include Sexpable.S with type t := t
  include Comparable.S with type t := t
    
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val to_string : t -> string
  val create : string -> t
end

(** Holes are subproblems within a {! Hypothesis}. They have a type, a
    type context, and a symbol which defines the set of expressions which
    can be used to fill the hole. *)
module Hole : sig
  module Id : sig
    type t
    include Sexpable.S with type t := t
    include Comparable.S with type t := t
    include Stringable.S with type t := t
    module Table : Hashtbl.S with type key := t
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
  val create : ?ctx:Type.t StaticDistance.Map.t -> Type.t -> Symbol.t -> t
  val apply_unifier : Unifier.t -> t -> t
end

(** Skeletons are expressions, with holes, that can be annotated. *)
module Skeleton : sig
  module Id : sig
    type t =
      | StaticDistance of StaticDistance.t
      | Name of string

    include Sexpable.S with type t := t
    include Comparable.S with type t := t
  end

  type 'a t =
    | Num_h of int * 'a
    | Bool_h of bool * 'a
    | List_h of 'a t list * 'a
    | Tree_h of 'a t Tree.t * 'a
    | Id_h of Id.t * 'a
    | Let_h of ('a t * 'a t) * 'a
    | Lambda_h of (int * 'a t) * 'a
    | Apply_h of ('a t * 'a t list) * 'a
    | Op_h of (Expr.Op.t * 'a t list) * 'a
    | Hole_h of Hole.t * 'a

  include Sexpable.S1 with type 'a t := 'a t

  val equal : equal:('a -> 'a -> bool) -> 'a t -> 'a t -> bool
  val to_string_hum : 'a t -> string

  (** Convert a skeleton to an {!Expr.t}.
      @param ctx A mapping from static distance variables to expressions. All SD variables will be replaced according to this mapping.
      @param fresh_name A function which generates a fresh name.
      @param of_hole A function which converts a {!Hole.t} into an {!Expr.t}. All holes will be converted according to this function. *)
  val to_expr :
    ?ctx:Expr.t StaticDistance.Map.t
    -> ?fresh_name:(unit -> string)
    -> ?of_hole:(Hole.t -> Expr.t)
    -> 'a t
    -> Expr.t
         
  (** Convert a skeleton to an {!Expr.t}. Throws an exception if a {!Hole.t} is encountered.
      @param ctx A mapping from static distance variables to expressions. All SD variables will be replaced according to this mapping.
      @param fresh_name A function which generates a fresh name. *)
  val to_expr_exn :
    ?ctx:Expr.t StaticDistance.Map.t
    -> ?fresh_name:(unit -> string)
    -> 'a t
    -> Expr.t

  val of_expr : 'a -> Expr.t -> 'a t
  val of_string : 'a -> string -> 'a t Or_error.t
  val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val hash : 'a -> int

  (** Fill a hole in a skeleton with another skeleton.
      @param parent The skeleton which contains the hole.
      @param child The skeleton used to fill the hole. *)
  val fill_hole : Hole.t -> parent:'a t -> child:'a t -> 'a t

  (** Get the annotation on the root node of a skeleton. *)
  val annotation : 'a t -> 'a

  (** Map over the holes in a skeleton. *)
  val map_hole : f:(Hole.t * 'a -> 'a t) -> 'a t -> 'a t

  (** Map over the annotations in a skeleton. *)
  val map_annotation : f:('a -> 'a) -> 'a t -> 'a t

  (** Map over all variants of a skeleton. *)
  val map :
    ?num:(int -> 'a -> int * 'a) ->
    ?bool:(bool -> 'a -> bool * 'a) ->
    ?id:(Id.t -> 'a -> Id.t * 'a) ->
    ?hole:(Hole.t -> 'a -> Hole.t * 'a) ->
    ?list:('a t list -> 'a -> 'a t list * 'a) ->
    ?tree:('a t Tree.t -> 'a -> 'a t Tree.t * 'a) ->
    ?let_:('a t * 'a t -> 'a -> ('a t * 'a t) * 'a) ->
    ?lambda:(int * 'a t -> 'a -> (int * 'a t) * 'a) ->
    ?op:(Expr.Op.t * 'a t list -> 'a -> (Expr.Op.t * 'a t list) * 'a) ->
    ?apply:('a t * 'a t list -> 'a -> ('a t * 'a t list) * 'a) -> 'a t -> 'a t
end

(** A CostModel assigns a cost to each variant of a skeleton. The
    total cost is the sum of the costs of the nodes. *)
module CostModel : sig
  type t = {
    num : int -> int;
    bool : bool -> int;
    hole : Hole.t -> int;
    id : Skeleton.Id.t -> int;
    list : 'a. 'a list -> int;
    tree : 'a. 'a Tree.t -> int;
    _let : 'a. 'a -> 'a -> int;
    lambda : 'a. int -> 'a -> int;
    apply : 'a. 'a -> 'a list -> int;
    op : 'a. Expr.Op.t -> 'a list -> int;
  }

  (** A cost model where variant has a constant cost. *)
  val constant : int -> t

  (** A cost model where variant has a cost of zero. *)
  val zero : t

  (** Compute the cost of a skeleton. *)
  val cost_of_skeleton : t -> 'a Skeleton.t -> int
end

module PerFunctionCostModel : sig
  type t
  val to_cost_model : t -> CostModel.t
  val to_json : t -> Json.json
  val of_json : Json.json -> t
end

module Specification : sig
  module Examples : sig
    type t
    type example = Value.t StaticDistance.Map.t * Value.t [@@deriving sexp]

    include Sexpable.S with type t := t

    val of_list : example list -> t Or_error.t
    val of_list_exn : example list -> t
    val to_list : t -> example list
    val singleton : example -> t

    val context : t -> StaticDistance.t list
  end

  module FunctionExamples : sig
    type t
    type example = (Value.t StaticDistance.Map.t * Value.t list) * Value.t [@@deriving sexp]

    include Sexpable.S with type t := t
    
    val of_list : example list -> t Or_error.t
    val of_list_exn : example list -> t
    val to_list : t -> example list
    val singleton : example -> t
  end
  
  type t =
    | Bottom
    | Top
    | Examples of Examples.t
    | FunctionExamples of FunctionExamples.t

  include Sexpable.S with type t := t
  include Comparable.S with type t := t

  val hash : t -> int
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val to_string : t -> string
  val verify : t -> 'a Skeleton.t -> bool
  val increment_scope : t -> t
end

(** Hypotheses are {! Skeleton}s which are annotated with {!Specification}s. *)
module Hypothesis : sig
  type skeleton = Specification.t Skeleton.t

  type kind =
    | Abstract
    | Concrete

  type t

  include Sexpable.S with type t := t

  val skeleton : t -> skeleton
  val cost : t -> int
  val kind : t -> kind
  val holes : t -> (Hole.t * Specification.t) list
  val spec : t -> Specification.t

  val to_expr : t -> Expr.t
  val to_string : t -> string
  val to_string_hum : t -> string
  
  val compare_cost : t -> t -> int
  val compare_skeleton : t -> t -> int
    
  val apply_unifier : t -> Unifier.t -> t
  val fill_hole : CostModel.t -> Hole.t -> parent:t -> child:t -> t
  val verify : t -> bool

  val of_skeleton : CostModel.t -> skeleton -> t

  (** Constructors *)
  val num : CostModel.t -> int -> Specification.t -> t
  val bool : CostModel.t -> bool -> Specification.t -> t
  val id_sd : CostModel.t -> StaticDistance.t -> Specification.t -> t
  val id_name : CostModel.t -> string -> Specification.t -> t
  val hole : CostModel.t -> Hole.t -> Specification.t -> t
  val list : CostModel.t -> t list -> Specification.t -> t
  val tree : CostModel.t -> t Tree.t -> Specification.t -> t
  val _let : CostModel.t -> t -> t -> Specification.t -> t
  val lambda : CostModel.t -> int -> t -> Specification.t -> t
  val apply : CostModel.t -> t -> t list -> Specification.t -> t
  val op : CostModel.t -> Expr.Op.t -> t list -> Specification.t -> t
end
