open! Core
open Collections

type 'a t = Empty | Node of 'a * 'a t list [@@deriving compare, hash, sexp]

let rec hash : ?hash_elem:('a -> int) -> 'a t -> int =
 fun ?(hash_elem = Hashtbl.hash) -> function
  | Empty -> Hashtbl.hash Empty
  | Node (x, xs) ->
      let xs_hash = List.map xs ~f:hash |> Hash.combine_many in
      Hash.combine (hash_elem x) xs_hash

let rec to_string t ~str =
  match t with
  | Empty -> "{}"
  | Node (x, []) -> sprintf "{%s}" (str x)
  | Node (x, y) ->
      sprintf "{%s %s}" (str x)
        (String.concat ~sep:" " (List.map y ~f:(to_string ~str)))

let rec size = function
  | Empty -> 1
  | Node (_, c) -> List.fold ~init:1 (List.map c ~f:size) ~f:( + )

let rec map (t : 'a t) ~f : 'b t =
  match t with
  | Empty -> Empty
  | Node (x, children) -> Node (f x, List.map children ~f:(map ~f))

let rec iter : 'a t -> f:('a -> unit) -> unit =
 fun t ~f ->
  match t with
  | Empty -> ()
  | Node (x, children) ->
      f x;
      List.iter children ~f:(iter ~f)

let rec fold t ~f ~init =
  match t with
  | Empty -> init
  | Node (x, children) -> f x (List.map ~f:(fold ~f ~init) children)

let max t ~cmp =
  fold t ~init:None ~f:(fun elem children ->
      let max_children = List.filter_opt children |> List.max_elt ~compare:cmp in
      match max_children with
      | Some elem' -> if cmp elem elem' > 0 then Some elem else Some elem'
      | None -> Some elem)

let rec equal ~equal:e t1 t2 =
  match (t1, t2) with
  | Empty, Empty -> true
  | Node (x1, c1), Node (x2, c2) -> e x1 x2 && List.equal (equal ~equal:e) c1 c2
  | _ -> false

let rec flatten (t : 'a t) : 'a list =
  match t with Empty -> [] | Node (x, y) -> [ x ] @ List.concat_map y ~f:flatten

let rec for_all t ~f =
  match t with
  | Empty -> true
  | Node (x, children) -> f x && List.for_all children ~f:(for_all ~f)

let exists : 'a t -> f:('a -> bool) -> bool =
 fun t ~f -> not (for_all t ~f:(fun x -> not (f x)))

let rec zip (t1 : 'a t) (t2 : 'b t) : ('a * 'b) t Option.t =
  match (t1, t2) with
  | Empty, Empty -> Some Empty
  | Node _, Empty | Empty, Node _ -> None
  | Node (x1, c1), Node (x2, c2) -> (
      match List.zip c1 c2 with
      | Ok c ->
          List.map c ~f:(fun (t1, t2) -> zip t1 t2)
          |> Option.all
          |> Option.map ~f:(fun c -> Node ((x1, x2), c))
      | Unequal_lengths -> None )

let rec all (t : 'a Option.t t) : 'a t Option.t =
  match t with
  | Empty -> Some Empty
  | Node (x, c) ->
      Option.bind x ~f:(fun x ->
          Option.map (List.map c ~f:all |> Option.all) ~f:(fun c -> Node (x, c)))
