open Core.Std
open OUnit2
open Tests_common

open Component
open Infer

let specification_of_string_tests =
  let module Sp = Specification in
  let module T = Term in
  let module V = Variable in
  let module C = Constant in
  
  let cases = [
  ] in

  "of_string" >::: List.map cases ~f:(fun (input, output) ->
      test_case (fun ctxt ->
          let output = Ok (Sp.t_of_sexp (Sexp.of_string output)) in
          assert_equal
            ~printer:(function
                | Ok spec -> Sexp.to_string_hum (Sp.sexp_of_t spec)
                | Error err -> Error.to_string_hum err)
            ~cmp:(fun m_s1 m_s2 ->
                let s1 = ok_exn m_s1 in
                let s2 = ok_exn m_s2 in
                Sp.equal s1 s2)
            ~ctxt output (Sp.of_string input)))

let tests = "component" >::: [
    "specification" >::: [
      specification_of_string_tests;
    ]
  ]
