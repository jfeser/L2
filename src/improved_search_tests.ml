open Core.Std
open OUnit2

open Tests_common
open Ast 
open Infer
open Improved_search

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

module Symbols = struct
  let lambda = Symbol.create "Lambda"
  let combinator = Symbol.create "Combinator"
  let expression = Symbol.create "Expression"
  let constant = Symbol.create "Constant"
  let identifier = Symbol.create "Identifier"
end

module Gen = L2_Generalizer.Make(Symbols)

let memoizer_tests = "memoizer" >::: [
    "get" >::: [
      test_case (fun _ ->
          let m = Memoizer.create Gen.generalize in
          let hole = Hole.create StaticDistance.Map.empty Type.num Symbols.constant in
          assert_raises ~msg:"Out of bounds cost should raise Invalid_argument."
            (Invalid_argument "Argument out of range.") (fun () ->
                Memoizer.get m hole Specification.Top (-1))
        );

      test_case (fun _ ->
          let m = Memoizer.create Gen.generalize in
          let hole = Hole.create StaticDistance.Map.empty Type.num Symbols.constant in
          assert_equal [] (Memoizer.get m hole Specification.Top 0)
        );

      test_case (fun _ ->
          let m = Memoizer.create Gen.generalize in
          let hole = Hole.create StaticDistance.Map.empty Type.num Symbols.constant in
          let spec = Specification.Top in
          assert_equivalent ~sexp:(Tuple.T2.sexp_of_t Hypothesis.sexp_of_t Unifier.sexp_of_t)
            (Gen.generate_constants hole spec)
            (Memoizer.get m hole spec 1)
        );

      test_case (fun ctxt ->
          let m = Memoizer.create Gen.generalize in
          let hole = Hole.create StaticDistance.Map.empty Type.num Symbols.expression in
          let spec = Specification.Top in
          assert_equal ~ctxt ~cmp:Int.equal ~printer:Int.to_string
             48 (List.length (Memoizer.get m hole spec 3))
        );

      test_case (fun ctxt ->
          let m = Memoizer.create Gen.generalize in
          let hole = Hole.create StaticDistance.Map.empty (Type.list (Type.free 0 0)) Symbols.expression in
          let spec = Specification.Top in
          assert_equal ~ctxt ~cmp:Int.equal ~printer:Int.to_string
             22 (List.length (Memoizer.get m hole spec 3))
        );
    ]
  ]

let tests = "search" >::: [
    "symbol" >::: [
      "create" >::: [
        test_case (fun _ ->
            let s1 = Symbol.create "test1" in
            let s2 = Symbol.create "test2" in
            assert_bool "A symbol is only equal to itself." (not (Symbol.equal s1 s2)));
        test_case (fun _ ->
            let s1 = Symbol.create "test" in
            let s2 = Symbol.create "test" in
            assert_bool "A symbol is only equal to itself." (not (Symbol.equal s1 s2)));
        test_case (fun _ ->
            let s = Symbol.create "test" in
            assert_bool "A symbol is only equal to itself." (Symbol.equal s s));
      ]
    ];

    static_distance_tests;
    memoizer_tests;
  ]
