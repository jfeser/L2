open Core.Std

(** Module for creating fresh names and numbers. *)
module Fresh = struct
  let count = ref (-1)
  let int () = incr count; !count
  let name prefix = Printf.sprintf "%s%d" prefix (int ())
  let names prefix num = List.range 0 num |> List.map ~f:(fun _ -> name prefix)
end

module IntListSet = Set.Make(struct
                              type t = int list
                              let compare = List.compare ~cmp:Int.compare
                              let sexp_of_t = List.sexp_of_t Int.sexp_of_t
                              let t_of_sexp = List.t_of_sexp Int.t_of_sexp
                            end)

module SMap = Map.Make(String)
module Ctx = struct
  type 'a t = 'a SMap.t ref
  exception UnboundError of string

  (** Return an empty context. *)
  let empty () : 'a t = ref SMap.empty

  (** Look up an id in a context. *)
  let lookup ctx id = SMap.find !ctx id
  let lookup_exn ctx id = match lookup ctx id with
    | Some v -> v
    | None -> raise (UnboundError id)

  (** Bind a type or value to an id, returning a new context. *)
  let bind ctx id data = ref (SMap.add !ctx ~key:id ~data:data)
  let bind_alist ctx alist =
    List.fold alist ~init:ctx ~f:(fun ctx' (id, data) -> bind ctx' id data)

  (** Remove a binding from a context, returning a new context. *)
  let unbind ctx id = ref (SMap.remove !ctx id)

  (** Bind a type or value to an id, updating the context in place. *)
  let update ctx id data = ctx := SMap.add !ctx ~key:id ~data:data

  (** Remove a binding from a context, updating the context in place. *)
  let remove ctx id = ctx := SMap.remove !ctx id

  let merge c1 c2 ~f:f = ref (SMap.merge !c1 !c2 ~f:f)
  let merge_right (c1: 'a t) (c2: 'a t) : 'a t =
    merge ~f:(fun ~key v -> match v with
        | `Both (_, v) | `Left v | `Right v -> Some v)
      c1 c2
  let map ctx ~f:f = ref (SMap.map !ctx ~f:f)
  let mapi ctx ~f:f = ref (SMap.mapi !ctx ~f:f)
  let filter ctx ~f:f = ref (SMap.filter !ctx ~f:f)
  let filter_mapi ctx ~f:f = ref (SMap.filter_mapi !ctx ~f:f)

  let equal cmp c1 c2 = SMap.equal cmp !c1 !c2

  let keys ctx = SMap.keys !ctx
  let data ctx = SMap.data !ctx

  let of_alist alist = ref (SMap.of_alist alist)
  let of_alist_exn alist = ref (SMap.of_alist_exn alist)
  let of_alist_mult alist = ref (SMap.of_alist_multi alist)

  let to_alist ctx = SMap.to_alist !ctx
  let to_string (ctx: 'a t) (str: 'a -> string) : string =
    to_alist ctx
    |> List.map ~f:(fun (key, value) -> key ^ ": " ^ (str value))
    |> String.concat ~sep:", "
    |> fun s -> "{ " ^ s ^ " }"
end

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

let rec zip3_exn (l1: 'a list) (l2: 'b list) (l3: 'c list) : ('a * 'b * 'c) list =
  match l1, l2, l3 with
  | x::xs, y::ys, z::zs -> (x, y, z)::(zip3_exn xs ys zs)
  | [], [], [] -> []
  | _ -> failwith "Lists have different lengths."

let superset l1 l2 =
  (List.length l1) >= (List.length l2)
  && List.for_all l2 ~f:(List.mem l1)

let strict_superset l1 l2 =
  (List.length l1) > (List.length l2)
  && List.for_all l2 ~f:(List.mem l1)

let lsplit2_on_str s ~on =
  match String.substr_index s ~pattern:on with
  | Some split_index ->
    Some (String.slice s 0 split_index,
          String.slice s (split_index + (String.length on)) (String.length s))
  | None -> None

let max = List.fold_left ~f:(fun a e -> if e > a then e else a) ~init:Int.min_value

let log verbosity level str =
  if verbosity >= level then begin
    print_endline str;
    flush stdout;
  end else ()

exception ParseError of string

let parse parse_f str =
  let lexbuf = Lexing.from_string str in
  try parse_f Lexer.token lexbuf with
  | Parser.Error -> raise (ParseError str)
  | Lexer.SyntaxError _ -> raise (ParseError str)
  | Parsing.Parse_error -> raise (ParseError str)

let parse_expr str = parse Parser.expr_eof str
let parse_typ str = parse Parser.typ_eof str
let parse_example str = parse Parser.example_eof str
let parse_constr str = parse Parser.constr_eof str
