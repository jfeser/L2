open Core
module Seq = Sequence

let m_partition : int -> int -> Array.Int.t Seq.t =
 fun n m ->
  (* if m <= 0 then failwiths "'m' must be greater than or equal to 1." m [%sexp_of:int]; *)
  if n < m then Seq.empty
  else if m <= 0 then Seq.empty
  else if m = 1 then Seq.singleton (Array.create ~len:1 n)
  else
    let a_init = Array.create ~len:m 1 in
    a_init.(0) <- n - m + 1 ;
    let init_seq = Seq.singleton a_init in
    let rest_seq =
      Seq.unfold ~init:a_init ~f:(fun a ->
          let a = Array.copy a in
          if a.(1) >= a.(0) - 1 then (
            let j = ref 2 in
            let s = ref (a.(0) + a.(1) - 1) in
            while !j < m && a.(!j) >= a.(0) - 1 do
              s := !s + a.(!j) ;
              incr j
            done ;
            if !j >= m then None
            else
              let x = a.(!j) + 1 in
              a.(!j) <- x ;
              decr j ;
              while !j > 0 do
                a.(!j) <- x ;
                s := !s - x ;
                decr j
              done ;
              a.(0) <- !s ;
              Some (Array.copy a, a) )
          else (
            a.(0) <- a.(0) - 1 ;
            a.(1) <- a.(1) + 1 ;
            Some (Array.copy a, a) ) )
    in
    Seq.append init_seq rest_seq

let m_partition_with_zeros : int -> int -> Array.Int.t Seq.t =
 fun n m ->
  if n = 0 then Array.create ~len:m 0 |> Seq.singleton
  else
    Seq.init (m + 1) ~f:(fun m' ->
        m_partition n m'
        |> Seq.map ~f:(fun p ->
               let p' = Array.create ~len:m 0 in
               Array.blito ~src:p ~dst:p' () ;
               p' ) )
    |> Seq.concat

let permutations : Array.Int.t -> Array.Int.t Seq.t =
 fun a_init ->
  let a_init = Array.copy a_init in
  Array.sort ~compare:Int.compare a_init ;
  let init_seq = Seq.singleton a_init in
  let rest_seq =
    Seq.unfold ~init:a_init ~f:(fun a ->
        let a = Array.copy a in
        let n = Array.length a in
        let j = ref (n - 2) in
        while !j >= 0 && a.(!j) >= a.(!j + 1) do
          decr j
        done ;
        if !j < 0 then None
        else
          let l = ref (n - 1) in
          while a.(!j) >= a.(!l) do
            decr l
          done ;
          Array.swap a !j !l ;
          let k = ref (!j + 1) in
          let l = ref (n - 1) in
          while !k < !l do
            Array.swap a !k !l ; incr k ; decr l
          done ;
          Some (a, a) )
  in
  Seq.append init_seq rest_seq

let permutations_poly : 'a Array.t -> 'a Array.t Seq.t =
 fun elems ->
  permutations (Array.init (Array.length elems) ~f:(fun x -> x))
  |> Seq.map ~f:(fun indices -> Array.map indices ~f:(fun i -> elems.(i)))

(* See https://rosettacode.org/wiki/Combinations_with_repetitions#OCaml *)
let rec combinations_with_replacement : int -> 'a list -> 'a list list =
 fun k l ->
  match (k, l) with
  | 0, _ -> [[]]
  | _, [] -> []
  | k, x :: xs ->
      List.map ~f:(fun xs' -> x :: xs') (combinations_with_replacement (k - 1) l)
      @ combinations_with_replacement k xs
