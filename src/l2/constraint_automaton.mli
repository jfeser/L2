open Core.Std

open Synthesis_common

module State : sig
  type t
  include Comparable.S with type t := t
end

module Rule : sig
  type t = State.t * Component.Specification.t * (State.t list)
end

type t = {
  states : State.Set.t;
  initial_states : State.Set.t;
  components : Component.t list;
  rules : Rule.t list;
}

val create :
  String.Set.t ->
  String.Set.t ->
  Component.t list ->
  (string * Component.Specification.t * string list) ->
  t

val reduce : t -> t
val is_empty : t -> bool
val difference : t -> t -> t
val complement : t -> t

val to_generalizer : t -> Generalizer.t
