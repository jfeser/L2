open Core
open OUnit2

let make_tests ?(cmp = ( = )) ~in_f ~out_f ~in_str ~out_str ~res_str name cases =
  name
  >::: List.map
         ~f:(fun (input, output) ->
           let case_name =
             Printf.sprintf "%s => %s" (in_str input) (out_str output)
           in
           case_name
           >:: fun _ ->
           assert_equal ~printer:res_str ~cmp (out_f output) (in_f input) )
         cases

let mk_equality_tests ?printer ?cmp name f cases =
  name
  >::: List.map cases ~f:(fun (input, output) ->
           test_case (fun ctxt -> assert_equal ?printer ?cmp ~ctxt output (f input))
       )

let assert_equivalent ~sexp expected real =
  let to_count_map l =
    List.fold l
      ~init:(Map.empty (module Sexp))
      ~f:(fun m x ->
        Map.change m (sexp x) ~f:(function Some c -> Some (c + 1) | None -> Some 1)
        )
  in
  let expected_m = to_count_map expected in
  let real_m = to_count_map real in
  Map.iteri expected_m ~f:(fun ~key:k ~data:v ->
      let v' = match Map.find real_m k with Some v' -> v' | None -> 0 in
      if v <> v' then
        assert_failure
          (sprintf "Expected %d instances of %s but got %d." v
             (Sexp.to_string_hum k) v') ) ;
  Map.iteri real_m ~f:(fun ~key:k ~data:v ->
      let v' = match Map.find expected_m k with Some v' -> v' | None -> 0 in
      if v <> v' then
        assert_failure
          (sprintf "Expected %d instances of %s but got %d." v'
             (Sexp.to_string_hum k) v) )
