open Core
open Poly

let rec all_equal (l : 'a list) ~eq =
  match l with
  | x :: xs -> List.for_all xs ~f:(eq x) && all_equal ~eq xs
  | [] -> true

let rec unzip3 = function
  | (x, y, z) :: l ->
      let xs, ys, zs = unzip3 l in
      (x :: xs, y :: ys, z :: zs)
  | [] -> ([], [], [])

let superset l1 l2 =
  List.length l1 >= List.length l2 && List.for_all l2 ~f:(List.mem ~equal:( = ) l1)

let strict_superset l1 l2 =
  List.length l1 > List.length l2 && List.for_all l2 ~f:(List.mem ~equal:( = ) l1)

let log verbosity level str =
  if verbosity >= level then (
    print_endline str;
    Out_channel.flush stdout )
  else ()

let with_runtime (thunk : unit -> 'a) : 'a * Time.Span.t =
  let start_t = Time.now () in
  let x = thunk () in
  let end_t = Time.now () in
  (x, Time.diff end_t start_t)

let add_time (t1 : Time.Span.t ref) (t2 : Time.Span.t) : unit =
  t1 := Time.Span.( + ) !t1 t2
