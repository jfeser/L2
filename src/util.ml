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

let rec all_equal (l: 'a list) ~equal:eq = match l with
  | x::xs -> (List.for_all xs ~f:(eq x)) && (all_equal ~equal:eq xs)
  | []    -> true

let parse str =
  let lexbuf = Lexing.from_string str in
  try Parser.prog Lexer.token lexbuf with
  | Parser.Error -> raise Parser.Error
  | Lexer.SyntaxError _ -> raise Parser.Error
  | Parsing.Parse_error -> raise Parser.Error
;;
