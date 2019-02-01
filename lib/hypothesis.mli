open Core
open Core_extended.Std
open Collections

open Infer

(** Modules for constructing hypotheses. *)

(** Static distance coordinates. *)
module StaticDistance : sig
  type t

  include Sexpable.S with type t := t

  module Map : sig
    include Map.S with type Key.t = t

    val increment_scope : 'a t -> 'a t
    val to_string : ('a -> string) -> 'a t -> string
  end
  
  (* include Comparable.S with type t := t and module Map := Map *)

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
  type t = private {
    id : int;
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

(** Skeletons are expressions with {!Hole}s that are annotated with
    {!Specification}s. *)
module Skeleton : sig
  module Id : sig
    type t =
      | StaticDistance of StaticDistance.t
      | Name of string

    include Sexpable.S with type t := t
    include Comparable.S with type t := t
  end

  type spec_data = ..

  type ast = private
    | Num    of int
    | Bool   of bool
    | List   of t list
    | Tree   of t Tree.t
    | Id     of Id.t
    | Hole   of Hole.t
    | Let    of { bound : t; body : t }
    | Lambda of { num_args : int; body : t }
    | Apply  of { func : t; args : t list }
    | Op     of { op : Expr.Op.t; args : t list }
  and spec = {
    verify : Library.t -> t -> bool;
    compare : spec -> int;
    to_sexp : unit -> Sexp.t;
    to_string : unit -> string;
    data : spec_data;
  }
  and skel = {
    spec : spec;
    ast : ast;
  }
  and t = skel Hashcons.hash_consed

  (** Accessor functions for record fields. *)
  val spec : t -> spec
  val ast : t -> ast

  (** Replacement functions for record fields. *)
  val replace_spec : t -> spec -> t

  (** Constructors for variants. *)
  val num : int -> spec -> t
  val bool : bool -> spec -> t
  val list : t list -> spec -> t
  val tree : t Tree.t -> spec -> t
  val id : Id.t -> spec -> t
  val hole : Hole.t -> spec -> t
  val let_ : t -> t -> spec -> t
  val lambda : int -> t -> spec -> t
  val apply : t -> t List.t -> spec -> t
  val op : Expr.Op.t -> t List.t -> spec -> t
  
  include Sexpable.S with type t := t
    
  module Table : sig
    val counter : Counter.t
  end

  val equal : t -> t -> bool
  val to_string_hum : t -> string
  val to_pp : ?indent:int -> t -> Pp.t

  (** Convert a skeleton to an {!Expr.t}.
      @param ctx A mapping from static distance variables to expressions. All SD variables will be replaced according to this mapping.
      @param fresh_name A function which generates a fresh name.
      @param of_hole A function which converts a {!Hole.t} into an {!Expr.t}. All holes will be converted according to this function. *)
  val to_expr :
    ?ctx:Expr.t StaticDistance.Map.t
    -> ?fresh_name:(unit -> string)
    -> ?of_hole:(Hole.t -> Expr.t)
    -> t
    -> Expr.t
         
  (** Convert a skeleton to an {!Expr.t}. Throws an exception if a {!Hole.t} is encountered.
      @param ctx A mapping from static distance variables to expressions. All SD variables will be replaced according to this mapping.
      @param fresh_name A function which generates a fresh name. *)
  val to_expr_exn :
    ?ctx:Expr.t StaticDistance.Map.t
    -> ?fresh_name:(unit -> string)
    -> t
    -> Expr.t
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
  val cost_of_skeleton : t -> Skeleton.t -> int
end

module PerFunctionCostModel : sig
  type t
  val to_cost_model : t -> CostModel.t
  val to_json : t -> Json.json
  val of_json : Json.json -> t
end

module Specification : sig
  type data = Skeleton.spec_data = ..
  type data += private Top | Bottom

  type t = Skeleton.spec = {
    verify : 'a. Library.t -> Skeleton.t -> bool;
    compare : t -> int;
    to_sexp : unit -> Sexp.t;
    to_string : unit -> string;
    data : data;
  }

  include Comparable.S with type t := t
  include Sexpable.S with type t := t
  
  val to_string : t -> string
  val verify : t -> ?library:Library.t -> Skeleton.t -> bool
  val equal : t -> t -> bool
  val data : t -> data
  val top : t
  val bottom : t

  val increment_scope : t -> t
end

module Examples : sig
  type t
  type example = Value.t StaticDistance.Map.t * Value.t [@@deriving sexp]

  type Specification.data += private Examples of t

  include Sexpable.S with type t := t

  val of_list : example list -> t Or_error.t
  val of_list_exn : example list -> t
  val to_list : t -> example list
  val singleton : example -> t

  val context : t -> StaticDistance.t list

  val to_spec : t -> Specification.t
end

module FunctionExamples : sig
  type t
  type example = (Value.t StaticDistance.Map.t * Value.t list) * Value.t [@@deriving sexp]

  type Specification.data += private FunctionExamples of t
  
  include Sexpable.S with type t := t

  val of_list : example list -> t Or_error.t
  val of_list_exn : example list -> t

  val of_input_output_list : (Value.t list * Value.t) list -> t Or_error.t
  val of_input_output_list_exn : (Value.t list * Value.t) list -> t

  val to_list : t -> example list
  val singleton : example -> t

  val to_spec : t -> Specification.t
end

module Inputs : sig
  type t

  type Specification.data += private Inputs of t
  include Sexpable.S with type t := t

  val of_examples : Examples.t -> t
  val signature : Library.t -> Skeleton.t -> t -> Value.t list option
  val to_spec : t -> Specification.t
end

(** Hypotheses are a further refinement of {!Skeleton}s which add
    additional information: cost, abstract/concrete state, and a list of
    holes. *)
module Hypothesis : sig
  type kind =
    | Abstract
    | Concrete

  type t

  include Sexpable.S with type t := t

  val skeleton : t -> Skeleton.t
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
  val verify : ?library:Library.t -> t -> bool

  val of_skeleton : CostModel.t -> Skeleton.t -> t

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
