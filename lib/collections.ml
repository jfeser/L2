open Core

(** Custom collections. *)

module Json = struct
  include Yojson.Safe

  let sexp_of_json j = to_string j |> [%sexp_of: string]
end

module Hash = struct
  let combine : int -> int -> int = fun h1 h2 -> (h1 lsl 1) lxor h2

  let combine3 : int -> int -> int -> int =
   fun h1 h2 h3 -> combine (combine h1 h2) h3

  let combine_many : int list -> int =
    let rec combine_many' h = function
      | [] -> h
      | x :: xs ->
          let h' = combine h x in
          combine_many' h' xs
    in
    function
    | [] -> failwith "List must be non-empty." | h :: hs -> combine_many' h hs

  let hash_empty = Hashtbl.hash []
end

module ListExt = struct
  include List

  let rec fold_left1 (l : 'a list) ~(f : 'a -> 'a -> 'a) : 'a =
    match l with
    | [] -> failwith "List must be non-empty."
    | [ x ] -> x
    | x :: y :: xs -> fold_left1 (f x y :: xs) ~f

  let rec insert (l : 'a list) (x : 'a) ~(cmp : 'a -> 'a -> int) : 'a list =
    match l with
    | [] -> [ x ]
    | y :: ys -> if cmp x y <= 0 then x :: l else y :: insert ys x ~cmp

  let max = List.fold_left ~f:(fun a e -> if e > a then e else a) ~init:Int.min_value

  let int_sum : int list -> int = List.fold_left ~f:(fun x y -> x + y) ~init:0

  let rec all_equal ?(eq = ( = )) (l : 'a list) =
    match l with
    | [] | [ _ ] -> true
    | x :: y :: xs -> eq x y && all_equal (y :: xs) ~eq

  let rec unzip3 l =
    match l with
    | (a1, b1, c1) :: xs ->
        let a, b, c = unzip3 xs in
        (a1 :: a, b1 :: b, c1 :: c)
    | [] -> ([], [], [])

  let rec repeat n x = if n = 0 then [] else x :: repeat (n - 1) x

  (* diag [1,2,3] 0 = [[0,2,3], [1,0,3], [1,2,0]] *)
  let diag l x =
    List.init (List.length l) ~f:(fun i ->
        List.take l i @ [ x ] @ List.drop l (i + 1))

  let random : ?state:Random.State.t -> 'a list -> 'a option =
   fun ?(state = Random.State.default) l ->
    let len = List.length l in
    if len = 0 then None else Some (List.nth_exn l (Random.State.int state len))

  let hash : ?hash_elem:('a -> int) -> 'a list -> int =
   fun ?(hash_elem = Hashtbl.hash) ->
    fold_left ~init:Hash.hash_empty ~f:(fun h e -> Hash.combine h (hash_elem e))
end

module List = ListExt

module ArrayExt = struct
  include Array

  let to_string : 'a Array.t -> ('a -> string) -> string =
   fun a ts ->
    let elems = to_list a |> List.map ~f:ts in
    let elems_str = String.concat elems ~sep:", " in
    "[" ^ elems_str ^ "]"
end

module Array = ArrayExt

module StreamExt = struct
  include Stream

  (* Create an infinite stream of 'value'. *)
  let repeat (value : 'a) : 'a t = from (fun _ -> Some value)

  (* Create a finite stream of 'value' of length 'n'. *)
  let repeat_n (n : int) (value : 'a) : 'a t =
    List.range 0 n |> List.map ~f:(fun _ -> value) |> of_list

  (* Concatenate two streams together. The second stream will not be
     inspected until the first stream is exhausted. *)
  let concat s1 s2 =
    from (fun _ ->
        match peek s1 with
        | Some _ -> Some (next s1)
        | None -> ( match peek s2 with Some _ -> Some (next s2) | None -> None ))

  (* Map a function over a stream. *)
  let map s ~f = from (fun _ -> try Some (f (next s)) with Failure -> None)

  let group s ~break =
    from (fun _ ->
        let rec collect () =
          match npeek 2 s with
          | [] -> None
          | [ _ ] -> Some [ next s ]
          | [ x; y ] -> if break x y then Some [ next s ] else collect ()
          | _ -> failwith "Stream.npeek returned a larger list than expected."
        in
        collect ())
end

module Stream = StreamExt

module Matrix = struct
  type 'a t = 'a list Stream.t

  (* Map a function over a matrix. *)
  let map s ~f = Stream.map s ~f:(List.map ~f)

  let trans : 'a Stream.t list -> 'a t = function
    | [] -> Stream.repeat []
    | ss -> Stream.from (fun _ -> Some (List.map ss ~f:Stream.next))

  let diag (s : 'a Stream.t Stream.t) : 'a t =
    Stream.from (fun i -> Some (List.map (Stream.npeek (i + 1) s) ~f:Stream.next))

  let join (x : 'a t t) : 'a t =
    Stream.map x ~f:trans |> diag
    |> Stream.map ~f:(fun y -> y |> List.concat |> List.concat)

  let compose (f : 'a -> 'b t) (g : 'b -> 'c t) (x : 'a) : 'c t =
    x |> f |> Stream.map ~f:(List.map ~f:g) |> join
end

module StreamMemoizer
    (Key : Map.Key) (Value : sig
      type t
    end) =
struct
  module KMap = Map.Make (Key)

  type memo_stream = {
    index : int ref;
    head : Value.t list Int.Table.t;
    stream : Value.t Matrix.t;
  }

  type t = memo_stream KMap.t ref

  let empty () = ref KMap.empty

  (* Get access to a stream of results for 'typ'. *)
  let get memo typ stream : Value.t Matrix.t =
    let mstream =
      match KMap.find !memo typ with
      | Some s -> s
      | None ->
          let s =
            { index = ref 0; head = Int.Table.create (); stream = stream () }
          in
          memo := KMap.set !memo ~key:typ ~data:s;
          s
    in
    Stream.from (fun i ->
        let sc = i + 1 in
        if sc <= !(mstream.index) then Some (Int.Table.find_exn mstream.head sc)
        else (
          List.range ~stop:`inclusive (!(mstream.index) + 1) sc
          |> List.iter ~f:(fun j ->
                 try
                   Int.Table.add_exn mstream.head ~key:j
                     ~data:(Stream.next mstream.stream);
                   incr mstream.index
                 with Stream.Failure -> ());
          if sc = !(mstream.index) then Some (Int.Table.find_exn mstream.head sc)
          else None ))
end

module Timer = struct
  type timing_info = { time : Time.Span.t; desc : string }

  type t = timing_info Ctx.t

  let empty = Ctx.empty

  let add_zero t name desc =
    Ctx.update t (Name.of_string name) { time = Time.Span.zero; desc }

  let add t name time =
    let time' = Ctx.lookup_exn t name in
    Ctx.update t name { time' with time = Time.Span.( + ) time time'.time }

  let find_exn t name = (Ctx.lookup_exn t (Name.of_string name)).time

  let run_with_time t name (thunk : unit -> 'a) : 'a =
    let start_t = Time.now () in
    let x = thunk () in
    let end_t = Time.now () in
    add t (Name.of_string name) (Time.diff end_t start_t);
    x

  let to_strings (t : t) : string list =
    List.map (Ctx.data t) ~f:(fun { desc = d; time = t } ->
        sprintf "%s: %s" d (Time.Span.to_short_string t))

  (** Serialize a timer to JSON. This creates an object of the form \{
      name: time, ...\}. Times are stored in seconds. *)
  let to_json (t : t) =
    `Assoc
      ( Ctx.to_alist t
      |> List.map ~f:(fun (k, v) ->
             ( Name.to_string k,
               `Assoc
                 [
                   ("time", `Float (Time.Span.to_sec v.time));
                   ("description", `String v.desc);
                 ] )) )
end

module Counter = struct
  let debug = true

  type count = Simple of int ref | Func of (unit -> int)

  type counter_info = { count : count; desc : string }

  type t = counter_info String.Table.t

  let empty () = String.Table.create ()

  let add_zero t name desc =
    if debug then Hashtbl.set t ~key:name ~data:{ count = Simple (ref 0); desc }
    else ()

  let add_func t name desc f =
    if debug then Hashtbl.set t ~key:name ~data:{ count = Func f; desc } else ()

  let get_count x =
    if debug then match x with Simple c -> !c | Func f -> f () else -1

  let get t name = if debug then get_count (Hashtbl.find_exn t name).count else -1

  let set t name v =
    if debug then
      match (Hashtbl.find_exn t name).count with
      | Simple c -> c := v
      | Func _ -> failwith "Cannot set a function counter."
    else ()

  let incr t name =
    if debug then
      match (Hashtbl.find_exn t name).count with
      | Simple c -> incr c
      | Func _ -> failwith "Cannot incr a function counter."
    else ()

  let to_strings : t -> string list =
   fun t ->
    Hashtbl.data t
    |> List.map ~f:(fun { desc = d; count = c } -> sprintf "%s: %d" d (get_count c))

  (** Serialize a counter to JSON. This creates an object of the form
      \{ name: count, ... \}. *)
  let to_json t =
    `Assoc
      ( Hashtbl.to_alist t
      |> List.map ~f:(fun (k, v) ->
             ( k,
               `Assoc
                 [
                   ("count", `Int (get_count v.count));
                   ("description", `String v.desc);
                 ] )) )
end

module SexpLog = struct
  type v = { value : Sexp.t option; desc : string }

  type t = v String.Table.t

  let empty : unit -> t = String.Table.create

  let add : t -> string -> string -> unit =
   fun t name desc -> String.Table.add_exn t ~key:name ~data:{ value = None; desc }

  let set : t -> string -> Sexp.t -> unit =
   fun t name value ->
    String.Table.update t name ~f:(function
      | Some v -> { v with value = Some value }
      | None -> failwith "Key not found.")

  let rec sexp_to_json = function
    | Sexp.Atom str -> `String str
    | Sexp.List lst -> `List (List.map lst ~f:sexp_to_json)

  let to_json t =
    `Assoc
      ( String.Table.to_alist t
      |> List.map ~f:(fun (k, v) ->
             ( k,
               `Assoc
                 [
                   ( "value",
                     match v.value with
                     | Some vv -> `String (Sexp.to_string_hum vv)
                     | None -> `Null );
                   ("description", `String v.desc);
                 ] )) )
end

module SortedList = struct
  type ('a, 'cmp) t = 'a list

  module SortedList0 = struct
    let of_list : comparator:('a, 'cmp) Comparator.t -> 'a list -> ('a, 'cmp) t =
     fun ~comparator -> List.sort ~compare:comparator.Comparator.compare

    let to_list : ('a, 'cmp) t -> 'a list = fun l -> l

    let length : ('a, 'cmp) t -> int = List.length

    let append :
        comparator:('a, 'cmp) Comparator.t ->
        ('a, 'cmp) t ->
        ('a, 'cmp) t ->
        ('a, 'cmp) t =
     fun ~comparator -> List.merge ~compare:comparator.Comparator.compare

    let map :
        comparator:('a, 'cmp) Comparator.t ->
        f:('a -> 'a) ->
        ('a, 'cmp) t ->
        ('a, 'cmp) t =
     fun ~comparator ~f l ->
      List.map ~f l |> List.sort ~compare:comparator.Comparator.compare

    let filter : f:('a -> bool) -> ('a, 'cmp) t -> ('a, 'cmp) t =
     fun ~f l -> List.filter ~f l
  end

  module Make_using_comparator (Cmp : Comparator.S) = struct
    type ('a, 'b) lst = ('a, 'b) t

    type t = (Cmp.t, Cmp.comparator_witness) lst

    let of_list : Cmp.t list -> t =
     fun l -> SortedList0.of_list ~comparator:Cmp.comparator l

    let to_list : t -> Cmp.t list = fun l -> SortedList0.to_list l

    let append : t -> t -> t =
     fun l1 l2 -> SortedList0.append ~comparator:Cmp.comparator l1 l2

    let map : f:(Cmp.t -> Cmp.t) -> t -> t =
     fun ~f l -> SortedList0.map ~comparator:Cmp.comparator ~f l

    let filter : f:(Cmp.t -> bool) -> t -> t = SortedList0.filter

    let length = SortedList0.length
  end
end

module KTree = struct
  type 'a t = Leaf of 'a | Node of 'a * 'a t list [@@deriving sexp, compare]

  let value = function Leaf x | Node (x, _) -> x

  let rec fold ~f = function
    | Leaf x -> f x []
    | Node (x, xs) -> f x (List.map xs ~f:(fold ~f))

  let rec map ~f = function
    | Leaf x -> Leaf (f x)
    | Node (x, xs) -> Node (f x, List.map xs ~f:(map ~f))

  let rec flatten = function
    | Leaf x -> [ x ]
    | Node (x, xs) -> x :: (List.map xs ~f:flatten |> List.concat)
end

module SequenceExt = struct
  include Sequence

  let inspect : 'a t -> f:('a -> unit) -> 'a t =
   fun s ~f ->
    map s ~f:(fun x ->
        f x;
        x)

  let rec product : 'a t list -> 'a list t = function
    | [] -> empty
    | [ s ] -> map ~f:(fun x -> [ x ]) s
    | s :: ss -> product ss |> concat_map ~f:(fun xs -> map s ~f:(fun x -> x :: xs))
end

module Sequence = SequenceExt
module Seq = Sequence
