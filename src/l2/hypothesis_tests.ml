open Core.Std
open OUnit2

open Tests_common
open Hypothesis

let static_distance_tests = "static-distance" >::: [
    "create" >::: [
      test_case (fun ctxt ->
          let sd = StaticDistance.create 1 2 in
          assert_equal ~ctxt ~printer:Int.to_string (StaticDistance.distance sd) 1;
          assert_equal ~ctxt ~printer:Int.to_string (StaticDistance.index sd) 2);

      test_case (fun _ ->
          assert_raises ~msg:"Bad arguments should raise Invalid_argument."
            (Invalid_argument "Argument out of range.") (fun () ->
                StaticDistance.create (-1) 1);
          assert_raises ~msg:"Bad arguments should raise Invalid_argument."
            (Invalid_argument "Argument out of range.") (fun () ->
                StaticDistance.create 1 (-1)));
    ];

    mk_equality_tests "args" StaticDistance.args
      ~printer:(fun a -> Sexp.to_string (List.sexp_of_t StaticDistance.sexp_of_t a))
      [
        0, [];
        1, [StaticDistance.create 1 1];
        2, [StaticDistance.create 1 1; StaticDistance.create 1 2];
      ];

    "increment_scope" >::: [
      test_case (fun ctxt ->
          let sd = StaticDistance.create 1 2 |> StaticDistance.increment_scope in
          assert_equal ~ctxt ~printer:Int.to_string (StaticDistance.distance sd) 2;
          assert_equal ~ctxt ~printer:Int.to_string (StaticDistance.index sd) 2);
    ]
  ]

let tests = "hypothesis" >::: [
    static_distance_tests;
  ]
