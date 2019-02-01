open Core
open OUnit2
open L2
open Synthesis_common
open Hypothesis
open V2_engine
module Sym = L2_Generalizer.Symbols
module Gen = L2_Generalizer.With_components
module Mem = Memoizer

let cost_model = default_cost_model

let top = Specification.top

let cost_model_tests =
  "cost-model"
  >::: [ test_case (fun ctxt ->
             let h =
               let cm = cost_model in
               let one = Hypothesis.num cm 1 top in
               Hypothesis.apply cm
                 (Hypothesis.id_name cm "append" top)
                 [one; one] top
             in
             assert_equal ~ctxt ~printer:Int.to_string 3 (Hypothesis.cost h) ) ]

(* let memoizer_tests = "memoizer" >::: [ *)
(*     "get" >::: [ *)
(*       test_case (fun _ -> *)
(*           let m = create_memoizer () in *)
(*           let hole = Hole.create Type.num Sym.constant in *)
(*           assert_raises ~msg:"Out of bounds cost should raise Invalid_argument." *)
(*             (Invalid_argument "Argument out of range.") (fun () -> *)
(*                 Mem.get m hole Specification.Top (-1)) *)
(*         ); *)

(*       test_case (fun _ -> *)
(*           let m = create_memoizer () in *)
(*           let hole = Hole.create Type.num Sym.constant in *)
(*           assert_equal [] (Mem.get m hole Specification.Top 0) *)
(*         ); *)

(*       test_case (fun _ -> *)
(*           let m = create_memoizer () in *)
(*           let hole = Hole.create Type.num Sym.constant in *)
(*           let spec = Specification.Top in *)
(*           assert_equivalent ~sexp:(Tuple.T2.sexp_of_t Hypothesis.sexp_of_t Unifier.sexp_of_t) *)
(*             (Gen.generate_constants hole spec) *)
(*             (Mem.get m hole spec 1) *)
(*         ); *)

(*       test_case (fun ctxt -> *)
(*           let m = create_memoizer () in *)
(*           let hole = Hole.create Type.num Sym.expression in *)
(*           let spec = Specification.Top in *)
(*           assert_equal ~ctxt ~cmp:Int.equal ~printer:Int.to_string *)
(*              52 (List.length (Mem.get m hole spec 3)) *)
(*         ); *)

(*       test_case (fun ctxt -> *)
(*           let m = create_memoizer () in *)
(*           let hole = Hole.create (Type.list (Type.free 0 0)) Sym.expression in *)
(*           let spec = Specification.Top in *)
(*           assert_equal ~ctxt ~cmp:Int.equal ~printer:Int.to_string *)
(*              63 (List.length (Mem.get m hole spec 3)) *)
(*         ); *)
(*     ] *)
(*   ] *)

let tests =
  "v2-engine"
  >::: [ cost_model_tests
       ; "symbol"
         >::: [ "create"
                >::: [ test_case (fun _ ->
                           let s1 = Symbol.create "test1" in
                           let s2 = Symbol.create "test2" in
                           assert_bool "A symbol is only equal to itself."
                             (not (Symbol.equal s1 s2)) )
                     ; test_case (fun _ ->
                           let s1 = Symbol.create "test" in
                           let s2 = Symbol.create "test" in
                           assert_bool "A symbol is only equal to itself."
                             (not (Symbol.equal s1 s2)) )
                     ; test_case (fun _ ->
                           let s = Symbol.create "test" in
                           assert_bool "A symbol is only equal to itself."
                             (Symbol.equal s s) ) ] ]
       (* memoizer_tests; *)
        ]
