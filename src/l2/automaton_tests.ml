open Core.Std
open OUnit2

module C = Component
module CA = Automaton.Constrained

let components = [
  C.create ~name:"cons" ~type_:"(a, list[a]) -> list[a]"
    ~spec:"And(Eq(Plus(Len(i2), 1), r)) where i2: list, r: list";
  C.create ~name:"nil" ~spec:"Eq(Len(r), 0) where r: list" ~type_:"list[a]";
  C.create ~name:"elem" ~spec:"#t" ~type_:"num";
] |> Or_error.all |> Or_error.ok_exn

let create states initial_states components rules =
  CA.create
    (String.Set.of_list states)
    (String.Set.of_list initial_states)
    (C.Set.of_list components)
    (List.map rules ~f:(fun (q, spec, qq) -> (q, C.Specification.of_string spec |> Or_error.ok_exn, qq)))

let zctx = Z3.mk_context []

let reduce_tests = "reduce" >::: [
    test_case (fun ctxt ->
        let a_expected = create ["q0"; "q1"] ["q0"] components [
            ("q0", "#t", ["q1"; "q0"]);
            ("q1", "#t", []);
            ("q0", "#t", [])
          ] in
        let a' = CA.reduce zctx a_expected |> Or_error.ok_exn in
        assert_equal ~cmp:CA.equal ~ctxt ~printer:CA.to_string a_expected a');

    test_case (fun ctxt ->
        let a_expected = create ["q0"; "q1"] ["q0"] components [
            ("q0", "Gt(Len(r), Len(i2)) where r: list, i2: list", ["q1"; "q0"]);
            ("q1", "#t", []);
            ("q0", "Eq(Len(r), 0) where r: list", [])
          ] in
        let a' = CA.reduce zctx a_expected |> Or_error.ok_exn in
        assert_equal ~cmp:CA.equal ~ctxt ~printer:CA.to_string a_expected a');

    test_case (fun ctxt ->
        let a = create ["q0"; "q1"; "q2"] ["q0"] components [
            ("q0", "#t", ["q1"; "q0"]);
            ("q1", "#t", []);
          ] in
        let a' = CA.reduce zctx a |> Or_error.ok_exn in
        assert_equal ~ctxt 0 (Hypothesis.Symbol.Set.length a'.CA.initial_states));
  ]

let generalize_tests = "generalize" >::: [
  ]

let tests = "constraint-automaton" >::: [
    reduce_tests;
  ]
