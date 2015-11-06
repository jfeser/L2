open Core.Std

open Infer

module Specification : sig
  include Component0.S
      
  type t = specification

  include Sexpable.S with type t := t

  val of_string : string -> t Or_error.t
end

type t = {
  name : string;
  spec : Specification.t;
  type_ : Type.t;
}

include Sexpable.S with type t := t

val create : string -> string -> string -> t Or_error.t
