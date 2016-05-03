open Core.Std

let array_to_string a ts =
  let elems = Array.to_list a |> List.map ~f:ts in
  let elems_str = String.concat elems ~sep:", " in
  "[" ^ elems_str ^ "]"

let m_partition : int -> int -> Array.Int.t Sequence.t = fun n m ->
  (* if m <= 0 then failwiths "'m' must be greater than or equal to 1." m [%sexp_of:int]; *)
  if n < m then Sequence.empty else
  if m = 1 then Sequence.singleton (Array.create ~len:1 n) else
    let a_init = Array.create ~len:m 1 in
    a_init.(0) <- n - m + 1;
    let init_seq = Sequence.singleton a_init in
    let rest_seq = 
      Sequence.unfold ~init:a_init ~f:(fun a ->
          let a = Array.copy a in
          if a.(1) >= a.(0) - 1 then
            let j = ref 2 in
            let s = ref (a.(0) + a.(1) - 1) in
            while !j < m && a.(!j) >= a.(0) - 1 do
              s := !s + a.(!j);
              incr j
            done;
            if !j >= m then None else
              let x = a.(!j) + 1 in
              a.(!j) <- x;
              decr j;
              while !j > 0 do
                a.(!j) <- x;
                s := !s - x;
                decr j;
              done;
              a.(0) <- !s;
              Some (Array.copy a, a)
          else begin
            a.(0) <- a.(0) - 1;
            a.(1) <- a.(1) + 1;
            (Some (Array.copy a, a))
          end)
    in
    Sequence.append init_seq rest_seq

let permutations : Array.Int.t -> Array.Int.t Sequence.t = fun a_init ->
  let a_init = Array.copy a_init in
  Array.sort ~cmp:Int.compare a_init;
  let init_seq = Sequence.singleton a_init in
  let rest_seq = Sequence.unfold ~init:a_init ~f:(fun a ->
      let a = Array.copy a in
      let n = Array.length a in
      let j = ref (n - 2) in
      while !j >= 0 && a.(!j) >= a.(!j + 1) do
        decr j;
      done;
      if !j < 0 then None else
        let l = ref (n - 1) in
        while a.(!j) >= a.(!l) do
          decr l;
        done;
        Array.swap a !j !l;
        let k = ref (!j + 1) in
        let l = ref (n - 1) in
        while !k < !l do
          Array.swap a !k !l;
          incr k;
          decr l;
        done;
        Some (a, a))
  in
  Sequence.append init_seq rest_seq
