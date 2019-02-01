open Core

(** Module for creating fresh names and numbers. *)
module Fresh = struct
  let count = ref (-1)

  let int () = incr count ; !count

  let name prefix = Printf.sprintf "%s%d" prefix (int ())

  let names prefix num = List.range 0 num |> List.map ~f:(fun _ -> name prefix)

  (** Create a function for returning fresh integers. *)
  let mk_fresh_int_fun () =
    let count = ref (-1) in
    fun () ->
      incr count ;
      let n = !count in
      if n < 0 then failwith "Out of fresh integers." else n

  (** Create a function for returning fresh names. These names will be
      of the form [a-z][0-9]*. *)
  let mk_fresh_name_fun () =
    let fresh_int = mk_fresh_int_fun () in
    fun () ->
      let n = fresh_int () in
      let prefix = Char.of_int_exn ((n mod 26) + 97) in
      let suffix = if n >= 26 then Int.to_string ((n - 26) mod 26) else "" in
      Printf.sprintf "%c%s" prefix suffix
end

module IntListSet = Set.Make (struct
  type t = int list

  let compare = List.compare Int.compare

  let sexp_of_t = List.sexp_of_t Int.sexp_of_t

  let t_of_sexp = List.t_of_sexp Int.t_of_sexp
end)

let partition n : int list list =
  let map_range a b f = List.map (List.range a b) ~f in
  let add_to_partition x p = List.sort ~compare:Int.compare (p @ [x]) in
  let rec part n : IntListSet.t =
    match n with
    | 0 -> IntListSet.empty
    (* n is always a partition of itself. For each number x in [0, n)
     generate each partition of n - x and add x to each partition. *)
    | n ->
        IntListSet.union_list
          ( [IntListSet.singleton [n]]
          @ map_range 1 n (fun x ->
                IntListSet.map (part (n - x)) ~f:(add_to_partition x) ) )
  in
  IntListSet.to_list (part n)

let m_partition n m = List.filter (partition n) ~f:(fun p -> m = List.length p)

(* insert x at all positions into l and return the list of results *)
let rec insert x l =
  match l with
  | [] -> [[x]]
  | a :: m -> (x :: l) :: List.map (insert x m) ~f:(fun y -> a :: y)

(* list of all permutations of l *)
let rec permutations = function
  | [] -> []
  | [x] -> [[x]]
  | x :: xs -> List.concat_map (permutations xs) ~f:(insert x)

let combinations l k =
  let rec aux k acc emit = function
    | [] -> acc
    | h :: t ->
        if k = 1 then aux k (emit [h] acc) emit t
        else
          let new_emit x = emit (h :: x) in
          aux k (aux (k - 1) acc new_emit t) emit t
  in
  let emit x acc = x :: acc in
  aux k [] emit l

let permutations_k l k = List.concat_map ~f:permutations (combinations l k)

let uniq (l : 'a list) : 'a list =
  List.fold_left l
    ~f:(fun (acc : 'a list) (e : 'a) ->
      if List.mem ~equal:( = ) acc e then acc else e :: acc )
    ~init:[]

let rec all_equal (l : 'a list) ~eq =
  match l with
  | x :: xs -> List.for_all xs ~f:(eq x) && all_equal ~eq xs
  | [] -> true

let rec unzip3 l =
  match l with
  | (a1, b1, c1) :: xs ->
      let a, b, c = unzip3 xs in
      (a1 :: a, b1 :: b, c1 :: c)
  | [] -> ([], [], [])

let rec zip3_exn (l1 : 'a list) (l2 : 'b list) (l3 : 'c list) : ('a * 'b * 'c) list
    =
  match (l1, l2, l3) with
  | x :: xs, y :: ys, z :: zs -> (x, y, z) :: zip3_exn xs ys zs
  | [], [], [] -> []
  | _ -> failwith "Lists have different lengths."

let superset l1 l2 =
  List.length l1 >= List.length l2 && List.for_all l2 ~f:(List.mem ~equal:( = ) l1)

let strict_superset l1 l2 =
  List.length l1 > List.length l2 && List.for_all l2 ~f:(List.mem ~equal:( = ) l1)

let lsplit2_on_str s ~on =
  match String.substr_index s ~pattern:on with
  | Some split_index ->
      Some
        ( String.slice s 0 split_index
        , String.slice s (split_index + String.length on) (String.length s) )
  | None -> None

let max = List.fold_left ~f:(fun a e -> if e > a then e else a) ~init:Int.min_value

let log verbosity level str =
  if verbosity >= level then ( print_endline str ; Out_channel.flush stdout )
  else ()

let with_runtime (thunk : unit -> 'a) : 'a * Time.Span.t =
  let start_t = Time.now () in
  let x = thunk () in
  let end_t = Time.now () in
  (x, Time.diff end_t start_t)

let add_time (t1 : Time.Span.t ref) (t2 : Time.Span.t) : unit =
  t1 := Time.Span.( + ) !t1 t2

let print_sexp x s = print_endline (Sexp.to_string_hum (s x))
