open Core.Std
open OUnit2
open Tests_common

open Component

let specification_of_string_tests =
  let cases = [
    "() ^ Len(i1) > 0 ^ Sub(Len(i1), 1) = Len(r) ^ Set(i1) ⊃ Set(r)",
    Ok { Specification.phi = []; Specification.constraints = [
        Binary (Gt, Apply ("Len", [Variable (Input 1)]), Constant (Int 0));
        Binary (Eq, Apply ("Sub", [Apply ("Len", [Variable (Input 1)]); Constant (Int 1)]), Apply ("Len", [Variable Output]));
        Binary (Superset, Apply ("Set", [Variable (Input 1)]), Apply ("Set", [Variable Output]));
      ]; };
  ] in
  mk_equality_tests
    ~printer:(function
        | Ok spec -> Sexp.to_string_hum (Specification.sexp_of_t spec)
        | Error err -> Error.to_string_hum err)
    ~cmp:(=)
    "of_string"
    Specification.of_string
    cases

let tests = "component" >::: [
    "specification" >::: [
      specification_of_string_tests;
    ]
  ]
