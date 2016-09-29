open Core.Std

(** Implementations of combinatorics routines. *)

(** Compute the partitions of an integer {i n} into {i m} parts. See
    (Knuth 3b, pg. 2). *)
val m_partition : int -> int -> Array.Int.t Sequence.t

(** Compute the unique permutations of an array. See (Knuth 2b, pg. 1). *)
val permutations : Array.Int.t -> Array.Int.t Sequence.t

val permutations_poly : 'a Array.t -> 'a Array.t Sequence.t
  
val combinations_with_replacement : int -> 'a list -> 'a list list
