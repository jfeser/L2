open Core.Std

module ListExt = struct
  include List

  let rec fold_left1 (l: 'a list) ~(f: 'a -> 'a -> 'a) : 'a = match l with
    | [] -> failwith "List must be non-empty."
    | [x] -> x
    | x::y::xs -> fold_left1 ((f x y)::xs) ~f:f

  let rec insert (l: 'a list) (x: 'a) ~(cmp: 'a -> 'a -> int) : 'a list =
    match l with
    | [] -> [x]
    | y::ys -> if cmp x y <= 0 then x::l else y::(insert ys x ~cmp:cmp)
end
module List = ListExt

module StreamExt = struct
  include Stream

  (* Create an infinite stream of 'value'. *)
  let repeat (value: 'a) : 'a t = from (fun _ -> Some value)

  (* Create a finite stream of 'value' of length 'n'. *)
  let repeat_n (n: int) (value: 'a) : 'a t =
    List.range 0 n |> List.map ~f:(fun _ -> value) |> of_list

  (* Concatenate two streams together. The second stream will not be
     inspected until the first stream is exhausted. *)
  let concat s1 s2 =
    from (fun _ ->
        match peek s1 with
        | Some _ -> Some (next s1)
        | None -> (match peek s2 with
            | Some _ -> Some (next s2)
            | None -> None))

  (* Map a function over a stream. *)
  let map s ~f = from (fun _ -> try Some (f (next s)) with Failure -> None)

  let group s ~break =
    from (fun _ ->
        let rec collect () =
          match npeek 2 s with
          | [] -> None
          | [_] -> Some [next s]
          | [x; y] -> if break x y then Some [next s] else collect ()
          | _ -> failwith "Stream.npeek returned a larger list than expected."
        in collect ())
end

module Stream = StreamExt

module Matrix = struct
  type 'a t = ('a list) Stream.t

  (* Map a function over a matrix. *)
  let map s ~f = Stream.map s ~f:(List.map ~f:f)

  let trans : (('a Stream.t) list -> 'a t) = function
    | [] -> Stream.repeat []
    | ss -> Stream.from (fun _ -> Some (List.map ss ~f:Stream.next))

  let diag (s: ('a Stream.t) Stream.t) : 'a t =
    Stream.from (fun i ->
        Some (List.map (Stream.npeek (i + 1) s) ~f:Stream.next))

  let join (x: ('a t) t) : 'a t =
    Stream.map x ~f:trans
    |> diag
    |> Stream.map ~f:(fun y -> y |> List.concat |> List.concat)

  let compose (f: 'a -> 'b t) (g: 'b -> 'c t) (x: 'a) : 'c t =
    x |> f |> (Stream.map ~f:(List.map ~f:g)) |> join
end

module Memoizer (Key: Map.Key) (Value: sig type t end) = struct
  module KMap = Map.Make(Key)

  type memo_stream = {
    index: int ref;
    head: Value.t list Int.Table.t;
    stream: Value.t Matrix.t;
  }
  type t = memo_stream KMap.t ref

  let empty () = ref KMap.empty

  (* Get access to a stream of results for 'typ'. *)
  let get memo typ stream : Value.t Matrix.t =
    let mstream = match KMap.find !memo typ with
      | Some s -> s
      | None ->
        let s = { index = ref 0; head = Int.Table.create (); stream = stream (); } in
        memo := KMap.add !memo ~key:typ ~data:s; s
    in
    Stream.from (fun i ->
        let sc = i + 1 in
        if sc <= !(mstream.index) then Some (Int.Table.find_exn mstream.head sc)
        else begin
          List.range ~stop:`inclusive (!(mstream.index) + 1) sc
          |> List.iter ~f:(fun j ->
              try
                Int.Table.add_exn
                  mstream.head ~key:j ~data:(Stream.next mstream.stream);
                incr mstream.index;
              with Stream.Failure -> ());
          if sc = !(mstream.index)
          then Some (Int.Table.find_exn mstream.head sc)
          else None
        end)
end

(** An inverted index maps sets to values so that queries can be
    performed that select all super- or sub-sets of the query set. *)
module InvertedIndex
    (KeyElem: sig
       type t
       val t_of_sexp : Sexplib.Sexp.t -> t
       val sexp_of_t : t -> Sexplib.Sexp.t
       val compare : t -> t -> int
     end)
    (Value: sig type t end) =
struct
  module KMap = Map.Make(KeyElem)
  module KSet = Set.Make(KeyElem)

  module KVPair = struct
    type t = KSet.t * Value.t

    let compare (x: t) (y: t) =
      let (x', _), (y', _) = x, y in
      KSet.compare x' y'
  end

  type t =
    ((int * int) list KMap.t ref) * (KVPair.t Int.Table.t) * (unit -> int)

  let create () : t =
    (ref KMap.empty, Int.Table.create (), Util.Fresh.mk_fresh_int_fun ())

  let compare_key_pair x1 x2 =
    let (x, _), (y, _) = x1, x2 in Int.compare x y

  let add (i: t) (k: KSet.t) (v: Value.t) : unit =
    let (index_ref, store, fresh_int) = i in
    let kv_key = fresh_int () in
    let kv_key_pair = (kv_key, Set.length k) in

    (* Generate a new index where the list mapped to each element in k
       contains the reference to the (k, v) pair *)
    let index' =
      List.fold_left (Set.to_list k) ~init:!index_ref ~f:(fun i e ->
          match KMap.find i e with
          | Some l ->
            KMap.add i ~key:e
              ~data:(List.insert l kv_key_pair ~cmp:compare_key_pair)
          | None -> KMap.add i ~key:e ~data:[kv_key_pair])
    in

    printf "Added %s to inverted index as id %d.\n"
      (Sexp.to_string_hum (KSet.sexp_of_t k))
      kv_key;

    (* Update the index. *)
    index_ref := index';

    (* Update the key-value store. *)
    Hashtbl.add_exn store ~key:kv_key ~data:(k, v)

  (* Merge a list of result lists. *)
  let merge_results rs =
    List.fold_left rs ~init:[] ~f:(List.merge ~cmp:compare_key_pair)
    |> List.remove_consecutive_duplicates
      ~equal:(fun (x, _) (y, _) -> x = y)

  (** Return the values that are mapped to the query set. *)
  let find_equal (i: t) (s: KSet.t) : Value.t list =
    let (index_ref, store, _) = i in
    let index = !index_ref in
    let len = Set.length s in

    try
      (* For each value in the query set select the list of set
         references that contain that value. If any of the values has
         no matching list, then there is no set which matches the
         query set. *)
      let result_ref_lists =
        List.map (Set.to_list s) ~f:(KMap.find_exn index)
      in

      (* Merge the result lists. *)
      let result_refs = merge_results result_ref_lists in

      (* Filter the result refs by cardinality. *)
      List.filter result_refs ~f:(fun (_, len') -> len = len')

      (* Dereference the result refs. *)
      |> List.map ~f:(fun (r, _) -> try Hashtbl.find_exn store r with
          | Not_found ->
            failwith "Index contains reference to nonexistent item.")

      (* Filter out the sets that are not equal to the query set. *)
      |> List.filter ~f:(fun (s', _) -> Set.equal s s')

      (* Return the values associated with the selected sets. *)
      |> List.map ~f:(fun (_, v) -> v)
    with Not_found -> []

  (** Return the values that are mapped to subsets of the query set. *)
  let find_subsets (i: t) (s: KSet.t) : Value.t list =
    let (index_ref, store, _) = i in
    let index = !index_ref in
    let len = Set.length s in

    (* For each value in the query set, use the index to get
       references to the sets that contain that value. *)
    let result_ref_lists =
      List.filter_map (Set.to_list s) ~f:(KMap.find index)
    in

    (* Merge the result lists. *)
    let result_refs = merge_results result_ref_lists in

    (* Filter the result refs by cardinality. *)
    List.filter result_refs ~f:(fun (_, len') -> len >= len')

    (* Dereference the result refs. *)
    |> List.map ~f:(fun (r, _) -> try Hashtbl.find_exn store r with
        | Not_found ->
          failwith "Index contains reference to nonexistent item.")

    (* Filter out the sets that are not subsets of the query set. *)
    |> List.filter ~f:(fun (s', _) -> Set.subset s' s)

    (* Return the values associated with the selected sets. *)
    |> List.map ~f:(fun (_, v) -> v)

  (** Return the values that are mapped supersets of the query set. *)
  let find_supersets (i: t) (s: KSet.t) : Value.t list =
    let (index_ref, store, _) = i in
    let index = !index_ref in
    let len = Set.length s in

    try
      (* For each value in the query set select the list of set
         references that contain that value. If any of the values has
         no matching list, then there is no set which matches the
         query set. *)
      let result_ref_lists =
        List.map (Set.to_list s) ~f:(KMap.find_exn index)
      in

      (* Merge the result lists. *)
      let result_refs = merge_results result_ref_lists in

      (* Filter the result refs by cardinality. *)
      List.filter result_refs ~f:(fun (_, len') -> len <= len')

      (* Dereference the result refs. *)
      |> List.map ~f:(fun (r, _) -> try Hashtbl.find_exn store r with
          | Not_found ->
            failwith "Index contains reference to nonexistent item.")

      (* Filter out the sets that are not equal to the query set. *)
      |> List.filter ~f:(fun (s', _) -> Set.subset s s')

      (* Return the values associated with the selected sets. *)
      |> List.map ~f:(fun (_, v) -> v)
    with Not_found -> []
end
