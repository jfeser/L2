open OUnit2
open L2
open Collections

(** Test a function in the standard evaluation context. *)
let test_l2_function_single fun_name input_strs result_str =
  let inputs = List.map ~f:Expr.of_string_exn input_strs in
  let result = Expr.of_string_exn result_str in
  let ctx = Eval.stdlib_vctx in
  assert_equal ~printer:Eval.value_to_string (Eval.eval ctx result)
    (Eval.eval ctx (`Apply (`Id fun_name, inputs)))

let test_l2_function fun_name cases =
  fun_name ^ "-tests"
  >::: List.map
         ~f:(fun (input_strs, result_str) ->
           test_case (fun _ ->
               test_l2_function_single fun_name input_strs result_str ) )
         cases

let merge_tests =
  test_l2_function "merge"
    [ (["[]"; "[3 4 5]"], "[3 4 5]")
    ; (["[1 2 3]"; "[]"], "[1 2 3]")
    ; (["[1 2 3]"; "[3 4 5]"], "[1 2 3 3 4 5]") ]

let intersperse_tests =
  test_l2_function "intersperse"
    [ (["[]"; "1"], "[]")
    ; (["[2]"; "1"], "[2]")
    ; (["[2 3]"; "1"], "[2 1 3]")
    ; (["[2 3 4]"; "1"], "[2 1 3 1 4]") ]

let append_tests =
  test_l2_function "append"
    [ (["[]"; "[]"], "[]")
    ; (["[1]"; "[]"], "[1]")
    ; (["[]"; "[1]"], "[1]")
    ; (["[2]"; "[1]"], "[2 1]") ]

let reverse_tests =
  test_l2_function "reverse"
    [(["[]"], "[]"); (["[1]"], "[1]"); (["[1 2 3]"], "[3 2 1]")]

let concat_tests =
  test_l2_function "concat"
    [ (["[]"], "[]")
    ; (["[[] [] []]"], "[]")
    ; (["[[1 2 3] [4 5] [7]]"], "[1 2 3 4 5 7]") ]

let drop_tests =
  test_l2_function "drop"
    [ (["[]"; "0"], "[]")
    ; (["[1 2]"; "0"], "[1 2]")
    ; (["[1 2 3]"; "1"], "[2 3]")
    ; (["[1 2 3]"; "2"], "[3]")
    ; (["[1 2 3]"; "3"], "[]") ]

let take_tests =
  test_l2_function "take"
    [ (["[]"; "0"], "[]")
    ; (["[1 2]"; "0"], "[]")
    ; (["[1 2 3]"; "1"], "[1]")
    ; (["[1 2 3]"; "2"], "[1 2]")
    ; (["[1 2 3]"; "3"], "[1 2 3]") ]

let sort_tests =
  test_l2_function "sort"
    [ (["[]"], "[]")
    ; (["[1]"], "[1]")
    ; (["[1 2 3]"], "[1 2 3]")
    ; (["[3 2 1]"], "[1 2 3]") ]

let dedup_tests =
  test_l2_function "dedup"
    [ (["[]"], "[]")
    ; (["[1]"], "[1]")
    ; (["[1 2 3]"], "[1 2 3]")
    ; (["[3 2 1]"], "[1 2 3]")
    ; (["[1 1]"], "[1]")
    ; (["[1 2 1]"], "[1 2]") ]

let tests =
  "eval-tests"
  >::: [ merge_tests
       ; intersperse_tests
       ; append_tests
       ; reverse_tests
       ; concat_tests
       ; drop_tests
       ; take_tests
       ; sort_tests
       ; dedup_tests ]
