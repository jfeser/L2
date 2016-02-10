open Core.Std
open OUnit2
open Tests_common

open Component
open Infer
    
module Sp = Specification

let specification_of_string_tests =
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

let to_z3 =
  let cases = [
    "And(Eq(Add(Len(i2), 1), Len(r))) where i2: list, r: list";
  ] in

  "to_z3" >::: List.map cases ~f:(fun input ->
      test_case (fun ctxt ->
          let zctx = Z3.mk_context [] in
          let spec = Sp.of_string input |> Or_error.ok_exn in
          match Sp.to_z3 zctx spec with
          | Ok _ -> ()
          | Error err ->
            let err_str =
              sprintf "Converting %s to Z3 failed:\n%s" input (Error.to_string_hum err)
            in
            assert_failure err_str))

let entails =
  let cases = [
    "And(Eq(Add(Len(i2), 1), Len(r))) where i2: list, r: list", "#t", true;
    "#t", "And(Eq(Add(Len(i2), 1), Len(r))) where i2: list, r: list", false;
  ] in

  "entails" >::: List.map cases ~f:(fun (in1, in2, out) ->
      test_case (fun ctxt ->
          let zctx = Z3.mk_context [] in
          let spec1 = Sp.of_string in1 |> Or_error.ok_exn in
          let spec2 = Sp.of_string in2 |> Or_error.ok_exn in
          assert_equal ~ctxt
            ~cmp:(fun x1 x2 -> Int.equal (Or_error.compare Bool.compare x1 x2) 0)
            ~printer:(fun oe -> Sexp.to_string_hum ([%sexp_of:Bool.t Or_error.t] oe))
            (Ok out) (Sp.entails zctx spec1 spec2)))

let tests = "component" >::: [
    "specification" >::: [
      specification_of_string_tests;
      to_z3;
      entails;
    ]
  ]
