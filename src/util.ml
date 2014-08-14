open Core.Std

module IntListSet = Set.Make(struct
                              type t = int list
                              let compare = List.compare ~cmp:Int.compare
                              let sexp_of_t = List.sexp_of_t Int.sexp_of_t
                              let t_of_sexp = List.t_of_sexp Int.t_of_sexp
                            end)

let partition n : int list list =
  let map_range a b f = List.map (List.range a b) ~f:f in
  let add_to_partition x p = List.sort ~cmp:Int.compare (p @ [x]) in
  let rec part n : IntListSet.t =
    (match n with
     | 0 -> IntListSet.empty
     (* n is always a partition of itself. For each number x in [0, n)
     generate each partition of n - x and add x to each partition. *)
     | n -> IntListSet.union_list
              ([IntListSet.singleton [n]] @
                 map_range 1 n (fun x -> IntListSet.map
                                           (part (n - x))
                                           ~f:(add_to_partition x)))) in
  IntListSet.to_list (part n)
;;

let m_partition n m =
  List.filter (partition n) ~f:(fun p -> m = List.length p) ;;

(* insert x at all positions into l and return the list of results *)
let rec insert x l = match l with
  | [] -> [[x]]
  | a::m -> (x::l) :: (List.map (insert x m) ~f:(fun y -> a::y)) ;;

(* list of all permutations of l *)
let rec permutations = function
  | [] -> []
  | [x] -> [[x]]
  | x::xs -> List.concat_map (permutations xs) ~f:(insert x) ;;

let combinations l k =
    let rec aux k acc emit = function
      | [] -> acc
      | h :: t ->
        if k = 1 then aux k (emit [h] acc) emit t else
          let new_emit x = emit (h :: x) in
          aux k (aux (k-1) acc new_emit t) emit t
    in
    let emit x acc = x :: acc in
    aux k [] emit l;;

let permutations_k l k = List.concat_map ~f:permutations (combinations l k)

let uniq (l:'a list) : 'a list =
  List.fold_left l ~f:(fun (acc:'a list) (e:'a) ->
                       if List.mem acc e then acc else e::acc)
                 ~init:[]

let rec all_equal (l: 'a list) ~eq:eq = match l with
  | x::xs -> (List.for_all xs ~f:(eq x)) && (all_equal ~eq:eq xs)
  | []    -> true

let rec unzip3 l =
  match l with
  | (a1, b1, c1)::xs ->
     let a, b, c = unzip3 xs in
     (a1::a), (b1::b), (c1::c)
  | [] -> [], [], []

let superset l1 l2 =
  (List.length l1) >= (List.length l2)
  && List.for_all l2 ~f:(List.mem l1)

let strict_superset l1 l2 =
  (List.length l1) > (List.length l2)
  && List.for_all l2 ~f:(List.mem l1)

let parse parse_f str =
  let lexbuf = Lexing.from_string str in
  try parse_f Lexer.token lexbuf with
  | Parser.Error -> raise Parser.Error
  | Lexer.SyntaxError _ -> raise Parser.Error
  | Parsing.Parse_error -> raise Parser.Error

let parse_prog str = parse Parser.prog str
let parse_expr str = parse Parser.expr str
let parse_example str = parse Parser.example str
let parse_constr str = parse Parser.constr str
