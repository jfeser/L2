open Core
include Stream

type 'a matrix = 'a list t

(* Concatenate two streams together. The second stream will not be
  inspected until the first stream is exhausted. *)
let concat s1 s2 =
  from (fun _ ->
      match peek s1 with
      | Some _ -> Some (next s1)
      | None -> ( match peek s2 with Some _ -> Some (next s2) | None -> None ) )

(* Map a function over a stream. *)
let map s ~f = from (fun _ -> try Some (f (next s)) with Failure -> None)

(* Map a function over a matrix. *)
let map_matrix s ~f = map s ~f:(List.map ~f)

(* Create an infinite stream of 'value'. *)
let repeat (value : 'a) : 'a t = from (fun _ -> Some value)

(* Create a finite stream of 'value' of length 'n'. *)
let repeat_n (n : int) (value : 'a) : 'a t =
  List.range 0 n |> List.map ~f:(fun _ -> value) |> of_list

let trans : 'a t list -> 'a list t = function
  | [] -> repeat []
  | ss -> from (fun _ -> Some (List.map ss ~f:next))

let diag (s : 'a t t) : 'a list t =
  from (fun i -> Some (List.map (npeek (i + 1) s) ~f:next))

let join (x : 'a matrix matrix) : 'a matrix =
  x |> map ~f:trans |> diag |> map ~f:(fun y -> y |> List.concat |> List.concat)

let compose (f : 'a -> 'b matrix) (g : 'b -> 'c matrix) (x : 'a) : 'c matrix =
  x |> f |> map ~f:(List.map ~f:g) |> join

let group s ~break =
  from (fun _ ->
      let rec collect () =
        match npeek 2 s with
        | [] -> None
        | [_] -> Some [next s]
        | [x; y] -> if break x y then Some [next s] else collect ()
        | _ -> failwith "Stream.npeek returned a larger list than expected."
      in
      collect () )

let merge (ss : 'a matrix list) : 'a matrix =
  from (fun _ ->
      Some
        ( ss
        |> List.filter_map ~f:(fun s -> try Some (next s) with Failure -> None)
        |> List.concat ) )

let rec drop_while s ~f =
  match peek s with
  | Some x -> if f x then ( junk s ; drop_while s ~f ) else ()
  | None -> ()

let flatten (m : 'a matrix) : 'a t =
  let current = ref [] in
  from (fun _ ->
      match !current with
      | x :: xs ->
          current := xs ;
          Some x
      | [] -> (
          drop_while m ~f:(( = ) []) ;
          try
            match next m with
            | [] -> failwith "Failed to drop empty rows."
            | x :: xs ->
                current := xs ;
                Some x
          with Failure -> None ) )

module Memoizer
    (Key : Map.Key) (Value : sig
        type t
    end) =
struct
  module KMap = Map.Make (Key)

  type memo_stream =
    {index: int ref; head: Value.t list Int.Table.t; stream: Value.t matrix}

  type t = memo_stream KMap.t ref

  let empty () = ref KMap.empty

  (* Get access to a stream of results for 'typ'. *)
  let get memo typ stream : Value.t matrix =
    let mstream =
      match KMap.find !memo typ with
      | Some s -> s
      | None ->
          let s = {index= ref 0; head= Int.Table.create (); stream= stream ()} in
          memo := KMap.set !memo ~key:typ ~data:s ;
          s
    in
    from (fun i ->
        let sc = i + 1 in
        if sc <= !(mstream.index) then Some (Int.Table.find_exn mstream.head sc)
        else (
          List.range ~stop:`inclusive (!(mstream.index) + 1) sc
          |> List.iter ~f:(fun j ->
                 try
                   Int.Table.add_exn mstream.head ~key:j ~data:(next mstream.stream) ;
                   incr mstream.index
                 with Failure -> () ) ;
          if sc = !(mstream.index) then Some (Int.Table.find_exn mstream.head sc)
          else None ) )
end
