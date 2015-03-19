open Core.Std

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
    from (fun i -> Some (List.map (Stream.npeek (i + 1) s) ~f:Stream.next))

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
    stream: Value.t matrix;
  }
  type t = memo_stream KMap.t ref

  let empty () = ref KMap.empty

  (* Get access to a stream of results for 'typ'. *)
  let get memo typ stream : Value.t matrix =
    let mstream = match KMap.find !memo typ with
      | Some s -> s
      | None ->
        let s = { index = ref 0; head = Int.Table.create (); stream = stream (); } in
        memo := KMap.add !memo ~key:typ ~data:s; s
    in
    from (fun i ->
        let sc = i + 1 in
        if sc <= !(mstream.index) then Some (Int.Table.find_exn mstream.head sc)
        else begin
          List.range ~stop:`inclusive (!(mstream.index) + 1) sc
          |> List.iter
            ~f:(fun j ->
                try Int.Table.add_exn mstream.head ~key:j ~data:(next mstream.stream);
                  incr mstream.index;
                with Failure -> ());
          if sc = !(mstream.index)
          then Some (Int.Table.find_exn mstream.head sc)
          else None
        end)
end
