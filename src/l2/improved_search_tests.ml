open Core.Std
open OUnit2

open Tests_common
open Ast 
open Infer
open Hypothesis
open Improved_search

module Symbols = struct
  let lambda = Symbol.create "Lambda"
  let combinator = Symbol.create "Combinator"
  let expression = Symbol.create "Expression"
  let constant = Symbol.create "Constant"
  let identifier = Symbol.create "Identifier"
  let base_case = Symbol.create "BaseCase"
end

module Gen = L2_Generalizer.Make (Symbols)
module Mem = Memoizer.Make (Gen) (L2_Deduction)

let memoizer_tests = "memoizer" >::: [
    "get" >::: [
      test_case (fun _ ->
          let m = Mem.create () in
          let hole = Hole.create StaticDistance.Map.empty Type.num Symbols.constant in
          assert_raises ~msg:"Out of bounds cost should raise Invalid_argument."
            (Invalid_argument "Argument out of range.") (fun () ->
                Mem.get m hole Specification.Top (-1))
        );

      test_case (fun _ ->
          let m = Mem.create () in
          let hole = Hole.create StaticDistance.Map.empty Type.num Symbols.constant in
          assert_equal [] (Mem.get m hole Specification.Top 0)
        );

      test_case (fun _ ->
          let m = Mem.create () in
          let hole = Hole.create StaticDistance.Map.empty Type.num Symbols.constant in
          let spec = Specification.Top in
          assert_equivalent ~sexp:(Tuple.T2.sexp_of_t Hypothesis.sexp_of_t Unifier.sexp_of_t)
            (Gen.generate_constants hole spec)
            (Mem.get m hole spec 1)
        );

      test_case (fun ctxt ->
          let m = Mem.create () in
          let hole = Hole.create StaticDistance.Map.empty Type.num Symbols.expression in
          let spec = Specification.Top in
          assert_equal ~ctxt ~cmp:Int.equal ~printer:Int.to_string
             48 (List.length (Mem.get m hole spec 3))
        );

      test_case (fun ctxt ->
          let m = Mem.create () in
          let hole = Hole.create StaticDistance.Map.empty (Type.list (Type.free 0 0)) Symbols.expression in
          let spec = Specification.Top in
          assert_equal ~ctxt ~cmp:Int.equal ~printer:Int.to_string
             22 (List.length (Mem.get m hole spec 3))
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

    memoizer_tests;
  ]
