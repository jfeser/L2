open Core.Std
open OUnit2

open Infer

module H = Hypothesis.Hypothesis
module SD = Hypothesis.StaticDistance
module Sp = Hypothesis.Specification
open Or_error.Monad_infix

let cm = Hypothesis.CostModel.zero

let of_string str = Sexp.of_string str |> Conflict.t_of_sexp

let of_hypothesis_unpruned_tests =
  let cases = [
    (let x = SD.create ~distance:1 ~index:1 in
     let spec = Sp.Examples.of_list_exn [
         (SD.Map.of_alist_exn [x, `List [`Num 1]]), `List [`Num 2];
         (SD.Map.of_alist_exn [x, `List [`Num 1; `Num 2]]), `List [`Num 2; `Num 3];
       ]
     in
     H.apply cm (H.id_name cm "drop" Sp.Top) [
       H.apply cm (H.id_name cm "cdr" Sp.Top) [H.id_sd cm x Sp.Top] Sp.Top;
       H.hole cm (Hypothesis.Hole.create
                    (SD.Map.of_alist_exn [x, "list[num]" |> Type.of_string])
                    ("num" |> Type.of_string)
                    (Hypothesis.Symbol.create "test")) Sp.Top
     ] (Sp.Examples spec)),

    "((input_spec
  ((Binary Eq (Variable Output) (Variable (Free f3)))
   (Binary Eq (Apply Len ((Variable (Input 1))))
    (Apply Len ((Variable Output))))
   (Binary Ge (Apply Len ((Variable (Input 1))))
    (Apply Len ((Variable Output))))
   (Binary Le (Apply Len ((Variable (Input 1))))
    (Apply Len ((Variable Output))))
   (Binary NotSubset (Variable (Input 1)) (Variable Output))
   (Binary NotSuperset (Variable (Input 1)) (Variable Output))))
 (body_spec
  (Node
   ((Binary Ge (Variable (Free f2)) (Constant (Int 0)))
    (Binary Ge (Apply Len ((Variable (Free f1)))) (Variable (Free f2)))
    (Binary Eq
     (Apply Sub ((Apply Len ((Variable (Free f1)))) (Variable (Free f2))))
     (Apply Len ((Variable (Free f3)))))
    (Binary Superset (Variable (Free f1)) (Variable (Free f3))))
   ((Node
     ((Binary Gt (Apply Len ((Variable (Input 1)))) (Constant (Int 0)))
      (Binary Eq
       (Apply Sub ((Apply Len ((Variable (Input 1)))) (Constant (Int 1))))
       (Apply Len ((Variable (Free f1)))))
      (Binary Superset (Variable (Input 1)) (Variable (Free f1))))
     ((Leaf ())))
    (Leaf ()))))
 (sorts (((Free f1) List) ((Free f2) Int) ((Free f3) List) ((Input 1) List) (Output List))))";

    "((skeleton
  (Op_h
   (RCons
    ((List_h () Top)
     (Hole_h
      ((id 20) (ctx (((1 1) (App_t list ((Const_t Num_t))))))
       (type_ (Const_t Num_t)) (symbol Expression))
      Top)))
   (Examples
    (((((1 1) (List ()))) (List ()))
     ((((1 1) (List ((Num 0) (Num 1) (Num 0)))))
      (List ((Num 0) (Num 0) (Num 0))))
     ((((1 1) (List ((Num 1) (Num 0))))) (List ((Num 1) (Num 1))))
     ((((1 1) (List ((Num 2) (Num 0) (Num 2) (Num 3)))))
      (List ((Num 2) (Num 2) (Num 2) (Num 2))))))))
 (cost 2) (kind Abstract)
 (holes
  ((((id 20) (ctx (((1 1) (App_t list ((Const_t Num_t))))))
     (type_ (Const_t Num_t)) (symbol Expression))
    Top))))" |> (fun s -> Hypothesis.Hypothesis.t_of_sexp (Sexp.of_string s)),

    "((input_spec
  ((Binary Eq (Variable Output) (Variable (Free f2)))
   (Binary Eq (Apply Len ((Variable (Input 1)))) (Apply Len ((Variable Output))))
   (Binary Ge (Apply Len ((Variable (Input 1)))) (Apply Len ((Variable Output))))
   (Binary Le (Apply Len ((Variable (Input 1)))) (Apply Len ((Variable Output))))))
 (body_spec
  (Node
   ((Binary Eq
     (Apply Plus ((Apply Len ((Variable (Free f0)))) (Constant (Int 1))))
     (Apply Len ((Variable (Free f2)))))
    (Binary Subset (Variable (Free f0)) (Variable (Free f2))))
   ((Leaf ((Binary Eq (Apply Len ((Variable (Free f0)))) (Constant (Int 0)))))
    (Leaf ()))))
 (sorts
  (((Free f0) List) ((Free f1) Int) ((Free f2) List) ((Input 1) List)
   (Output List))))";
  ] in
  "of_hypothesis_unpruned" >::: List.map cases ~f:(fun (input, output) ->
      test_case (fun ctxt ->
          let output = Ok (Sexp.of_string output |> Conflict.t_of_sexp) in
          assert_equal
            ~printer:(function
                | Ok c -> Sexp.to_string_hum (Conflict.sexp_of_t c)
                | Error err -> Error.to_string_hum err)
            ~cmp:(fun m_s1 m_s2 ->
                let s1 = ok_exn m_s1 in
                let s2 = ok_exn m_s2 in
                Conflict.equal s1 s2)
            ~ctxt output (Conflict.of_hypothesis_unpruned Component.stdlib input)))

let of_hypothesis_tests =
  let cases = [
    "((skeleton
  (Op_h
   (RCons
    ((List_h () Top)
     (Hole_h
      ((id 20) (ctx (((1 1) (App_t list ((Const_t Num_t))))))
       (type_ (Const_t Num_t)) (symbol Expression))
      Top)))
   (Examples
    (((((1 1) (List ()))) (List ()))
     ((((1 1) (List ((Num 0) (Num 1) (Num 0))))) (List ((Num 0) (Num 0) (Num 0))))
     ((((1 1) (List ((Num 1) (Num 0))))) (List ((Num 1) (Num 1))))
     ((((1 1) (List ((Num 2) (Num 0) (Num 2) (Num 3)))))
      (List ((Num 2) (Num 2) (Num 2) (Num 2))))))))
 (cost 2) (kind Abstract)
 (holes
  ((((id 20) (ctx (((1 1) (App_t list ((Const_t Num_t))))))
     (type_ (Const_t Num_t)) (symbol Expression))
    Top))))",

    "((input_spec
  ((Binary Eq (Variable Output) (Variable (Free f2)))
   (Binary Eq (Apply Len ((Variable (Input 1)))) (Apply Len ((Variable Output))))
   (Binary Ge (Apply Len ((Variable (Input 1)))) (Apply Len ((Variable Output))))
   (Binary Le (Apply Len ((Variable (Input 1)))) (Apply Len ((Variable Output))))))
 (body_spec
  (Node
   ((Binary Eq
     (Apply Plus ((Apply Len ((Variable (Free f0)))) (Constant (Int 1))))
     (Apply Len ((Variable (Free f2)))))
    (Binary Subset (Variable (Free f0)) (Variable (Free f2))))
   ((Leaf ((Binary Eq (Apply Len ((Variable (Free f0)))) (Constant (Int 0)))))
    (Leaf ()))))
 (sorts
  (((Free f0) List) ((Free f1) Int) ((Free f2) List) ((Input 1) List)
   (Output List))))";
  ] in
  "of_hypothesis_unpruned" >::: List.map cases ~f:(fun (input, output) ->
      test_case (fun ctxt ->
          let input = Hypothesis.Hypothesis.t_of_sexp (Sexp.of_string input) in
          let output = Sexp.of_string output |> Conflict.t_of_sexp in
          match Conflict.of_hypothesis input with
          | Ok (`Conflict c) ->
              assert_equal
              ~printer:(fun c ->  Sexp.to_string_hum (Conflict.sexp_of_t c))
              ~cmp:Conflict.equal
              ~ctxt output c
          | Ok `NoConflict -> assert_failure "No conflict found."
          | Error err -> assert_failure (Error.to_string_hum err)))

let tests = "conflict" >::: [
    of_hypothesis_unpruned_tests;
    of_hypothesis_tests;
  ]
