open Core.Std
open OUnit2

open Synthesis_common
open Hypothesis

module H = Hypothesis
module C = Component
module CA = Automaton.Constrained
module CSpec = C.Specification

let components = [
  C.create ~name:"cons" ~type_:"(a, list[a]) -> list[a]"
    ~spec:"And(Eq(Add(Len(i2), 1), Len(r))) where i2: list, r: list";
  C.create ~name:"nil" ~spec:"Eq(Len(r), 0) where r: list" ~type_:"list[a]";
  C.create ~name:"elem" ~spec:"#t" ~type_:"num";
] |> Or_error.all |> Or_error.ok_exn

let create states initial_states components rules =
  CA.create
    (String.Set.of_list states)
    (String.Set.of_list initial_states)
    (C.Set.of_list components)
    (List.map rules ~f:(fun (q, spec, qq) -> (q, CSpec.of_string spec |> Or_error.ok_exn, qq)))

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
        assert_equal ~ctxt 0 (Symbol.Set.length a'.CA.initial_states));
  ]

let generalize_tests = "generalize" >::: [
    test_case (fun ctxt ->
        let a = create ["q0"; "q1"] ["q0"] components [
            ("q0", "#t", ["q1"; "q0"]);
            ("q1", "#t", []);
            ("q0", "#t", []);
          ] in
        let cm = CostModel.constant 1 in
        let gen = CA.to_generalizer zctx a cm |> Or_error.ok_exn in
        let memo = Memoizer.create gen cm in
        let hole = Hole.create (Infer.Type.list Infer.Type.num) (Symbol.Set.choose_exn a.CA.initial_states) in
        let hypo = Hypothesis.hole cm hole Specification.Top in
        let out =
          Memoizer.fill_holes_in_hypothesis memo hypo 1
          |> List.map ~f:Tuple.T2.get1
          |> [%sexp_of: Hypothesis.t list]
        in
        assert_equal ~cmp:Sexp.equal ~ctxt ~printer:Sexp.to_string_hum
          (Sexp.of_string
             "(((skeleton (Id_h (Name nil) Top)) (cost 1) (kind Concrete) (holes ())))")
          out);

    test_case (fun ctxt ->
        let a = create ["q0"; "q1"] ["q0"] components [
            ("q0", "#t", ["q1"; "q0"]);
            ("q1", "#t", []);
            ("q0", "#t", []);
          ] in
        let cm = CostModel.constant 1 in
        let gen = CA.to_generalizer zctx a cm |> Or_error.ok_exn in
        let memo = Memoizer.create gen cm in
        let hole = Hole.create (Infer.Type.list Infer.Type.num) (Symbol.Set.choose_exn a.CA.initial_states) in
        let hypo = Hypothesis.hole cm hole Specification.Top in
        let out =
          Memoizer.fill_holes_in_hypothesis memo hypo 4
          |> List.map ~f:Tuple.T2.get1
          |> [%sexp_of: Hypothesis.t list]
        in
        assert_equal ~cmp:Sexp.equal ~ctxt ~printer:Sexp.to_string_hum
          (Sexp.of_string
             "(((skeleton
   (Apply_h
    ((Id_h (Name cons) Top) ((Id_h (Name elem) Top) (Id_h (Name nil) Top)))
    Top))
  (cost 4) (kind Concrete) (holes ())))")
          out);
  ]

let conflict_tests = "conflict" >::: [
    "of_skeleton" >::: [
      test_case (fun ctxt ->
          let zctx = Z3.mk_context [] in
          let spec = CSpec.of_string "Eq(3, Len(r)) where r: list" |> Or_error.ok_exn in
          let cm = CostModel.constant 1 in
          let top = Specification.Top in
          let skel = H.apply cm (H.id_name cm "cons" top) [
              H.id_name cm "elem" top; H.id_name cm "nil" top;
            ] top
                     |> H.skeleton
          in
          let component_set = Component.Set.of_list components in
          let conflict =
            Automaton.Conflict.of_skeleton zctx component_set skel spec |> Or_error.ok_exn
          in
          let expected_rules =
            "((q1
       ((_constraint
         (Apply And
          ((Apply Eq
            ((Apply Add
              ((Apply Len ((Variable (Input 2)))) (Constant (Int 1))))
             (Apply Len ((Variable Output))))))))
        (sorts (((Input 2) List) (Output List))))
       (* q0))
      (q0
       ((_constraint
         (Apply And
          ((Apply Eq ((Apply Len ((Variable Output))) (Constant (Int 0)))))))
        (sorts ((Output List))))
       ()))"
            |> Sexp.of_string
          in
          let actual_rules =
            [%sexp_of:Automaton.Rule.t List.t]
              (Option.value_exn conflict).Automaton.Conflict.automaton.CA.rules
          in

          assert_equal ~ctxt ~cmp:Sexp.equal ~printer:Sexp.to_string_hum expected_rules actual_rules);
    ]
  ]

let synthesizer_tests = "synthesizer" >::: [
  ]

let tests = "constraint-automaton" >::: [
    reduce_tests;
    generalize_tests;
    conflict_tests;
  ]
