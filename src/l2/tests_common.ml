open Core.Std
open OUnit2

let mk_equality_tests ?printer ?cmp name f cases =
  name >::: List.map cases ~f:(fun (input, output) ->
      test_case (fun ctxt -> assert_equal ?printer ?cmp ~ctxt output (f input)))

let assert_equivalent ~sexp expected real =
  let to_count_map l =
    List.fold l ~init:(Map.empty ~comparator:Sexp.comparator) ~f:(fun m x ->
        Map.change m (sexp x) (function
            | Some c -> Some (c + 1)
            | None -> Some 1))
  in
  let expected_m = to_count_map expected in
  let real_m = to_count_map real in
  Map.iter expected_m ~f:(fun ~key:k ~data:v ->
      let v' = match Map.find real_m k with
        | Some v' -> v'
        | None -> 0
      in
      if v <> v' then
        assert_failure (sprintf "Expected %d instances of %s but got %d."
                          v (Sexp.to_string_hum k) v'));
  Map.iter real_m ~f:(fun ~key:k ~data:v ->
      let v' = match Map.find expected_m k with
        | Some v' -> v'
        | None -> 0
      in
      if v <> v' then
        assert_failure (sprintf "Expected %d instances of %s but got %d."
                          v' (Sexp.to_string_hum k) v));
