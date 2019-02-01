open OUnit2
open L2
open Unify

let test_unify_apply =
  "test-unify-apply"
  >:: fun _ ->
  let ev = `Apply (`Id "sum", [`Id "x"]) in
  let st2 = K "1" in
  match sterm_of_expr_value ev with
  | Some st1 ->
      let t1, t2 = (translate st1, translate st2) in
      assert_equal ~printer:sub_to_string
        [("(sum x)", Term ("1", []))]
        (unify_one t1 t2)
  | None -> assert_failure "Creating term failed."

let tests = "unify-tests" >::: [test_unify_apply]
