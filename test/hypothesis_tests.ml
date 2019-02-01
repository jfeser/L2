open Core
open OUnit2
open L2
open Tests_common
open Hypothesis

let static_distance_tests =
  "static-distance"
  >::: [ "create"
         >::: [ test_case (fun ctxt ->
                    let sd = StaticDistance.create ~distance:1 ~index:2 in
                    assert_equal ~ctxt ~printer:Int.to_string
                      (StaticDistance.distance sd) 1 ;
                    assert_equal ~ctxt ~printer:Int.to_string
                      (StaticDistance.index sd) 2 )
              ; test_case (fun _ ->
                    assert_raises
                      ~msg:"Bad arguments should raise Invalid_argument."
                      (Invalid_argument "Argument out of range.") (fun () ->
                        StaticDistance.create ~distance:(-1) ~index:1 ) ;
                    assert_raises
                      ~msg:"Bad arguments should raise Invalid_argument."
                      (Invalid_argument "Argument out of range.") (fun () ->
                        StaticDistance.create ~distance:1 ~index:(-1) ) ) ]
       ; mk_equality_tests "args" StaticDistance.args
           ~printer:(fun a ->
             Sexp.to_string (List.sexp_of_t StaticDistance.sexp_of_t a) )
           [ (0, [])
           ; (1, [StaticDistance.create ~distance:1 ~index:1])
           ; ( 2
             , [ StaticDistance.create ~distance:1 ~index:1
               ; StaticDistance.create ~distance:1 ~index:2 ] ) ]
       ; "increment_scope"
         >::: [ test_case (fun ctxt ->
                    let sd =
                      StaticDistance.create ~distance:1 ~index:2
                      |> StaticDistance.increment_scope
                    in
                    assert_equal ~ctxt ~printer:Int.to_string
                      (StaticDistance.distance sd) 2 ;
                    assert_equal ~ctxt ~printer:Int.to_string
                      (StaticDistance.index sd) 2 ) ] ]

let top = Specification.top

let constant_cm = CostModel.constant 1

let cost_model_tests =
  "cost-model"
  >::: [ test_case (fun ctxt ->
             let h = Hypothesis.num constant_cm 1 top in
             assert_equal ~ctxt ~printer:Int.to_string 1 (Hypothesis.cost h) )
       ; test_case (fun ctxt ->
             let one = Hypothesis.num constant_cm 1 top in
             let h =
               Hypothesis.apply constant_cm
                 (Hypothesis.id_name constant_cm "+" top)
                 [one; one] top
             in
             assert_equal ~ctxt ~printer:Int.to_string 4 (Hypothesis.cost h) ) ]

let spec_tests =
  let module Sp = Specification in
  "specifications"
  >::: [ test_case (fun _ ->
             let module FE = FunctionExamples in
             let s1 =
               FE.of_input_output_list_exn [([`Num 0], `Num 1)] |> FE.to_spec
             in
             let s2 =
               FE.of_input_output_list_exn [([`Num 0], `Num 2)] |> FE.to_spec
             in
             assert_bool "specs are not equal" (Sp.compare s1 s2 <> 0) )
       ; test_case (fun _ ->
             let module FE = FunctionExamples in
             let s1 =
               FE.of_input_output_list_exn [([`Num 0], `Num 1)] |> FE.to_spec
             in
             let s2 =
               FE.of_input_output_list_exn [([`Num 0], `Num 1)] |> FE.to_spec
             in
             assert_bool "specs are equal" (Sp.compare s1 s2 = 0) ) ]

let tests = "hypothesis" >::: [static_distance_tests; cost_model_tests; spec_tests]
