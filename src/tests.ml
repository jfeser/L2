open Core.Std
open OUnit2
open Ast

let identity (x: 'a) : 'a = x

let cmp_partition a b = 
  let sort_partition p = List.sort ~cmp:Int.compare p in
  let sort_partition_list l = List.map ~f:sort_partition l
                              |> List.sort ~cmp:(List.compare ~cmp:Int.compare) in
  (sort_partition_list a) = (sort_partition_list b)

let m_expr_to_string = function Some e -> expr_to_string e | None -> "None"

let assert_solve result examples init = 
  let res_expr = Util.parse_expr result in
  assert_equal ~printer:expr_to_string res_expr ((Search.solve examples ~init:init) :> expr)

let assert_solve_cata (result: string) (examples: example list) (init: expr list) = 
  let res_prog = Util.parse_prog result in
  let solve_prog = ((Search.solve_catamorphic examples ~init:init) :> expr list) in
  assert_equal ~printer:prog_to_string res_prog solve_prog

let eval expr = Eval.eval (Eval.empty_eval_ctx ()) expr

let make_tests ?cmp:(cmp = (=)) ~in_f ~out_f ~in_str ~out_str ~res_str name cases = 
  name >:::
    (List.map ~f:(fun (input, output) -> 
                  let case_name = Printf.sprintf "%s => %s" (in_str input) (out_str output) in
                  case_name >:: (fun _ -> assert_equal ~printer:res_str ~cmp:cmp 
                                                       (out_f output) (in_f input)))
              cases)

let test_parse_expr =
  make_tests ~in_f:Util.parse_expr ~out_f:identity
              ~in_str:identity ~out_str:expr_to_string ~res_str:expr_to_string
              "parse_expr"
              [ "1", `Num 1;
                "#t", `Bool true;
                "#f", `Bool false;
                "nil", `Nil;
                "[]", `List [];
                "[1]", `List [`Num 1;];
                "[1 2]", `List [`Num 1; `Num 2;];
                "[[]]", `List [`List []];
                "[[1]]", `List [`List [`Num 1;]];
                "a", `Id "a";
                "test", `Id "test";
                "(+ (+ 1 2) 3)", `Op (Plus, [`Op (Plus, [`Num 1; `Num 2]); `Num 3;]);
                "(let f (lambda (x:num) (if (= x 0) 0 (+ (f (- x 1)) 1))) (f 0))", 
                `Let ("f", `Lambda ([("x", Num_t)], 
                                    `Op (If, [`Op (Eq, [`Id "x"; `Num 0]);
                                              `Num 0;
                                              `Op (Plus, [`Apply (`Id "f",
                                                                  [`Op (Minus, [`Id "x"; 
                                                                                `Num 1])]);
                                                          `Num 1])])),
                      `Apply (`Id "f", [`Num 0]));
                "(+ 1 2)", `Op (Plus, [`Num 1; `Num 2]);
                "(cons 1 [])", `Op (Cons, [`Num 1; `List []]);
                "(cons 1 [2])", `Op (Cons, [`Num 1; `List [`Num 2]]);
                "(cdr [])", `Op (Cdr, [`List []]);
                "(cdr [1 2])", `Op (Cdr, [`List [`Num 1; `Num 2;]]);
              ]

let test_parse_example = 
  make_tests ~in_f:Util.parse_example ~out_f:identity
              ~in_str:identity ~out_str:example_to_string ~res_str:example_to_string
              "parse_example"
              [ "(f 1) -> 1", ((`Apply (`Id "f", [`Num 1])), `Num 1); 
                "(f (f 1)) -> 1", ((`Apply (`Id "f", [`Apply (`Id "f", [`Num 1])])), `Num 1);
              ]

let test_parse_prog = 
  make_tests ~in_f:Util.parse_prog ~out_f:identity
              ~in_str:identity ~out_str:prog_to_string ~res_str:prog_to_string
              "parse_prog"
              [ "1 2 3", [`Num 1; `Num 2; `Num 3];
              ]

(* let test_parse_failure = *)
(*   make_tests ~in_f:identity ~out_f:(fun str -> (fun () -> parse str)) *)
(*              ~in_str:(fun _ -> "Parser.Error") ~out_str:identity *)
(*              ~ass:assert_raises *)
(*     [ Parser.Error, "["; *)
(*       Parser.Error, "[(])"; *)
(*       Parser.Error, "(+ 1)"; *)
(*     ] *)

let test_eval = 
  make_tests ~in_f:(fun str -> str |> Util.parse_expr |> eval) ~out_f:identity 
              ~in_str:identity ~out_str:value_to_string ~res_str:value_to_string
              "eval"
              [ "1", `Num 1;
                "#t", `Bool true;
                "#f", `Bool false;
                "[]", `Nil;
                "[1]", `List [`Num 1];
                "nil", `Nil;
                "(+ 1 2)", `Num 3;
                "(- 1 2)", `Num (-1);
                "(* 1 2)", `Num 2;
                "(/ 4 2)", `Num 2;
                "(% 4 2)", `Num 0;
                "(= 4 2)", `Bool false;
                "(= 4 4)", `Bool true;
                "(> 4 2)", `Bool true;
                "(> 4 4)", `Bool false;
                "(>= 4 2)", `Bool true;
                "(>= 4 4)", `Bool true;
                "(>= 4 5)", `Bool false;
                "(cons 4 [])", `List [`Num 4];
                "(cons 4 [1])", `List [`Num 4; `Num 1];
                "(car [1])", `Num 1;
                "(cdr [1 2])", `List [`Num 2];
                "(if #t 1 2)", `Num 1;
                "(if #f 1 2)", `Num 2;
                "(let a 1 (+ 1 a))", `Num 2;
                "(let a 5 (let b 2 (* a b)))", `Num 10;
                "(let a 5 (let a 2 (+ a 1)))", `Num 3;
                "(let a (* 3 4) (+ a 1))", `Num 13;
                "(let f (lambda (x:num) (+ 1 x)) (f 1))", `Num 2;
                "(let f (lambda (x:num y:num) (+ y x)) (f 1 2))", `Num 3;
                "(let f (lambda (x:num) (lambda (y:num) (+ x y))) ((f 1) 2))", `Num 3;
                "(let f (lambda (x:num) (+ x 1)) (let g (lambda (x:num) (+ 1 x)) (f (g 1))))", `Num 3;
                "(let f (lambda (x:num) (if (= x 0) 0 (f (- x 1)))) (f 0))", `Num 0;
                "(let f (lambda (x:num) (if (= x 0) 0 (f (- x 1)))) (f 5))", `Num 0;
                "(fold [1 2 3] (lambda (a:num e:num) (+ a e)) 0)", `Num 6; (* Sum *)
                "(fold [[1] [2 1] [3 2 1]] (lambda (a:[num] e:num) (cons (car e) a)) [])", 
                `List [`Num 1; `Num 2; `Num 3]; (* Firsts *)
                "(foldl [1 2 3] (lambda (a:num e:num) (+ a e)) 0)", `Num 6; (* Sum *)
                "(foldl [[1] [2 1] [3 2 1]] (lambda (a:[num] e:num) (cons (car e) a)) [])", 
                `List [`Num 3; `Num 2; `Num 1]; (* Rev-firsts *)
                "(filter [1 2 3 4] (lambda (e:num) (> 3 e)))", `List [`Num 1; `Num 2];
                "(filter [1 2 3 4] (lambda (e:num) (= 0 (% e 2))))", `List [`Num 2; `Num 4];
              ]

let test_eval_prog = 
  make_tests ~in_f:(fun str -> str |> Util.parse_prog |> Eval.prog_eval) ~out_f:identity
              ~in_str:identity ~out_str:value_to_string ~res_str:value_to_string
              "eval_prog"
              [ "(define a 1) (+ a 1)", `Num 2;
                "(define a 1) (define b (+ a 1)) (+ b 1)", `Num 3;
                "(define plus (lambda (a:num b:num) (+ a b))) (plus 1 2)", `Num 3;
                "(define a 1)", `Nil;
                "1 2 3", `Num 3;
                "(define last (lambda (l:[num]) (if (= nil (cdr l)) (car l) (last (cdr l))))) (last [1 2 3])", `Num 3;
              ]

let test_fold_constants = 
  make_tests ~in_f:(fun str -> str |> Util.parse_expr |> Rewrite.fold_constants) 
              ~out_f:(fun str -> Some (Util.parse_expr str))
              ~in_str:identity ~out_str:identity 
              ~res_str:m_expr_to_string
              "fold_constants"
              [ "1", "1";
                "#f", "#f";
                "nil", "nil";
                "[1 2]", "[1 2]";
                "(+ 1 2)", "3";
                "(+ (* 0 5) (/ 4 2))", "2";
                "(+ a (- 4 3))", "(+ a 1)";
                "(lambda (x:num) (+ x (* 1 5)))", "(lambda (x:num) (+ x 5))";
                "(lambda (x:num) (+ 1 (* 1 5)))", "6";
              ]

let test_rewrite = 
  make_tests ~in_f:(fun str -> str |> Util.parse_expr |> Rewrite.rewrite)
              ~out_f:(fun str -> Some (Util.parse_expr str))
              ~in_str:identity ~out_str:identity 
              ~res_str:m_expr_to_string             
              "rewrite"
              [ "1", "1";
                "#f", "#f";
                "nil", "nil";
                "[1 2]", "[1 2]";
                "(+ x 0)", "x";
                "(+ 0 x)", "x";
                "(+ 1 x)", "(+ 1 x)";
                "(- x 0)", "x";
                "(* x 0)", "0";
                "(* 0 x)", "0";
                "(* x 1)", "x";
                "(* 1 x)", "x";
                "(/ x 1)", "x";
                "(/ 0 x)", "0";
                "(/ x x)", "1";
                "(% 0 x)", "0";
                "(% x 1)", "0";
                "(% x x)", "0";
                "(!= x y)", "(!= x y)";
                "(!= x x)", "#f";
                "(+ (- y x) x)", "y";
                "(- (+ y x) x)", "y";
                "(- (+ y x) y)", "x";
                "(= (= x y) #f)", "(!= x y)";
              ]

let test_normalize = 
  make_tests ~in_f:(fun str -> str |> Util.parse_expr |> Rewrite.normalize) ~out_f:Util.parse_expr
              ~in_str:identity ~out_str:identity ~res_str:expr_to_string
    "normalize"
    [ "(+ 1 (+ 2 3))", "(+ 1 2 3)";
      "(+ (+ 1 2) (+ 3 4))", "(+ 1 2 3 4)";
      "(+ (* (* 0 1) 2) (+ 3 4))", "(+ (* 0 1 2) 3 4)";
      "(+ 1 (- 2 3))", "(+ (- 2 3) 1)";
      "(- 1 (- 2 3))", "(- 1 (- 2 3))";
    ]

let test_denormalize = 
  make_tests ~in_f:(fun str -> str |> Util.parse_expr |> Rewrite.denormalize) ~out_f:Util.parse_expr
              ~in_str:identity ~out_str:identity ~res_str:expr_to_string
    "normalize"
    [ "(+ 1 2 3)", "(+ 1 (+ 2 3))";
      "(+ 1 2 3 4)", "(+ 1 (+ 2 (+ 3 4)))";
      "(+ (* 0 1 2) 3 4)", "(+ (* 0 (* 1 2)) (+ 3 4))";
    ]

let test_straight_solve =
  make_tests ~in_f:(fun (_, example_strs, init_strs) -> 
                    let solution = Search.solve ~init:(List.map init_strs ~f:Util.parse_expr) 
                                                (List.map example_strs ~f:Util.parse_example) in
                    (solution :> expr))
             ~out_f:Util.parse_expr
             ~in_str:(fun (name, _, _) -> name) ~out_str:identity ~res_str:expr_to_string
             "straight_solve"
             [
               ("plus", ["(f 1 1) -> 2"; 
                         "(f 2 1) -> 3"], []), 
               "(define f (lambda (x0:num x1:num) (+ x0 x1)))";

               ("max", ["(f 3 5) -> 5";
                        "(f 5 3) -> 5"], []),
               "(define f (lambda (x0:num x1:num) (if (< x0 x1) x1 x0)))";

               ("second", ["(f [1 2]) -> 2";
                           "(f [1 3]) -> 3"], []),
               "(define f (lambda (x0:[num]) (car (cdr x0))))";

               ("even", ["(f 1) -> #f";
                         "(f 2) -> #t";
                         "(f 3) -> #f";
                         "(f 4) -> #t";
                        ], ["0"; "2"]),
               "(define f (lambda (x0:num) (= (% x0 2) 0)))";
             ]

let test_catamorphic_solve =
  make_tests ~in_f:(fun (_, example_strs, init_strs) ->
                    let solution = Search.solve_catamorphic 
                                     ~init:(List.map init_strs ~f:Util.parse_expr)
                                     (List.map example_strs ~f:Util.parse_example) in
                    (solution :> expr list))
             ~out_f:Util.parse_prog
             ~in_str:(fun (name, _, _) -> name) ~out_str:identity ~res_str:prog_to_string
             "catamorphic_solve"
             [
               ("sum", ["(f []) -> 0";
                        "(f [1]) -> 1";
                        "(f [1 2]) -> 3";
                       ], []),
               "";

               ("rev-concat", ["(f []) -> []";
                               "(f [[1]]) -> [1]";
                               "(f [[1] [2]]) -> [1 2]";
                              ], []),
               "";

               ("length", ["(f []) -> 0";
                           "(f [0]) -> 1";
                           "(f [0 0]) -> 2";
                          ], ["1"]),
               "";
             ]
(* let test_catamorphic_solve =  *)
(*   "catamorphic_solve" >::: *)
(*     (List.map ~f:(fun (str, examples, init) ->  *)
(*                   let title = str in *)
(*                   title >:: (fun _ -> assert_solve_cata str examples init)) *)
(*               [ "(define f (lambda (x0:[num]) (foldl x0 (lambda (a:num e:num) (+ a e)) 0)))",  *)
(*                 [ ([`Nil], `Num 0); *)
(*                   ([`List [`Num 1]], `Num 1); *)
(*                   ([`List [`Num 1; `Num 2]], `Num 3); *)
(*                 ], []; *)

(*                 "(define f (lambda (x0:[[num]]) (foldl x0 (lambda (a:[num] e:num) (cons (car e) a)) [])))", *)
(*                 [ ([`Nil], `Nil); *)
(*                   ([`List [`List [`Num 1]]], `List [`Num 1]); *)
(*                   ([`List [`List [`Num 1]; `List [`Num 2]]], `List [`Num 2; `Num 1]); *)
(*                 ], []; *)

(*                 "nil", (\*length*\) *)
(*                 [ ([`Nil], `Num 0); *)
(*                   ([`List [`Num 0]], `Num 1); *)
(*                   ([`List [`Num 0; `Num 0]], `Num 2);], [`Num 1]; *)

(*                 "nil", (\* incr *\) *)
(*                 [ ([`Nil], `Nil); *)
(*                   ([`List [`Num 0]], `List [`Num 1]); *)
(*                   ([`List [`Num 0; `Num 1]], `List [`Num 2; `Num 1]);], [`Num 1]; *)

(*                 "allodd", (\* allodd *\) *)
(*                 [ [`Nil], `Bool true; *)
(*                   [`List [`Num 1]], `Bool true; *)
(*                   [`List [`Num 4]], `Bool false; *)
(*                   [`List [`Num 1; `Num 3]], `Bool true; *)
(*                   [`List [`Num 4; `Num 1]], `Bool false; *)
(*                   [`List [`Num 2; `Num 1; `Num 2; `Num 3]], `Bool false; *)
(*                 ], [`Num 0; `Num 2; `Bool true; `Bool false]; *)

(*                 "and", (\* and *\) *)
(*                 [ [`Nil], `Bool true; *)
(*                   [`List [`Bool true]], `Bool true; *)
(*                   [`List [`Bool false]], `Bool false; *)
(*                   [`List [`Bool true; `Bool true]], `Bool true; *)
(*                   [`List [`Bool false; `Bool true]], `Bool false; *)
(*                 ], [`Bool true; `Bool false]; *)

(*                 (\* "zeroes", (\\* zeroes *\\) *\) *)
(*                 (\* [ [`Nil], `Nil; *\) *)
(*                 (\*   [`List [`Num 0]], `Nil; *\) *)
(*                 (\*   [`List [`Num 1; `Num 0]], `List [`Num 1]; *\) *)
(*                 (\*   [`List [`Num 1; `Num 2; `Num 0]], `List [`Num 1; `Num 2]; *\) *)
(*                 (\* ], [`Num 0]; *\) *)
(*     ]) *)

let partition_to_string = List.to_string ~f:(List.to_string ~f:Int.to_string)
let test_partition =
  make_tests ~in_f:Util.partition ~out_f:identity 
              ~in_str:Int.to_string ~out_str:partition_to_string ~res_str:partition_to_string
              ~cmp:cmp_partition
              "test_partition"
              [ 0, [];
                1, [[1]];
                2, [[2]; [1; 1]];
                3, [[3]; [1; 2]; [1; 1; 1]];
              ]

let test_m_partition =
  "test_m_partition" >:::
    (List.map ~f:(fun (n, m, p) ->
                  let title = Printf.sprintf "%s -> %s" 
                                             (Int.to_string n)
                                             (partition_to_string p) in
                  title >:: (fun _ -> assert_equal ~cmp:cmp_partition (Util.m_partition n m) p))
              [ 3, 1, [[3]];
                3, 2, [[1; 2]];
                3, 3, [[1; 1; 1]];
    ])

let test_specialize = 
  "test_specialize" >:::
    (List.map ~f:(fun (t1, t2, t3) ->
                  let title = Printf.sprintf "%s %s -> %s"
                                             (typ_to_string t1)
                                             (typ_to_string t2)
                                             (typ_to_string t3) in
                  title >:: (fun _ -> assert_equal (Eval.specialize t1 t2) t3))
              [ Nil_t, Nil_t, Nil_t;
                List_t Num_t, Nil_t, List_t Num_t;
                Nil_t, List_t Num_t, List_t Num_t;
                List_t Num_t, List_t Num_t, List_t Num_t;
                List_t (List_t Num_t), List_t Nil_t, List_t (List_t Num_t);
                Num_t, Num_t, Num_t;
    ])

let test_typeof_value = 
  make_tests ~in_f:Eval.typeof_value ~out_f:identity
              ~in_str:value_to_string ~out_str:typ_to_string ~res_str:typ_to_string
              "typeof_value"
              [ `Num 1, Num_t;
                `Bool true, Bool_t;
                `List [`Num 1; `Num 2], List_t Num_t;
                `List [`Nil; `Nil], List_t Nil_t;
                `List [`List [`Num 1; `Num 2]], List_t (List_t Num_t);
              ]

let test_typeof_example = 
  make_tests ~in_f:(fun ex -> ex |> Util.parse_example 
                              |> (Search.typeof_example (Eval.empty_type_ctx ())))
             ~out_f:identity
             ~in_str:identity ~out_str:typ_to_string ~res_str:typ_to_string
             "typeof_example"
             [ "(f 1) -> 1", Arrow_t ([Num_t], Num_t);
               "(f 1) -> []", Arrow_t ([Num_t], Nil_t);
               "(f 1) -> [1]", Arrow_t ([Num_t], (List_t Num_t));
               "(f 1 #f) -> #f", Arrow_t ([Num_t; Bool_t], Bool_t);
             ]

let test_signature = 
  make_tests ~in_f:(fun exs -> exs |> List.map ~f:Util.parse_example |> Search.signature)
             ~out_f:identity
             ~in_str:(fun exs -> "[" ^ (String.concat ~sep:"; " exs) ^ "]") 
             ~out_str:typ_to_string ~res_str:typ_to_string
             "signature"
             [ ["(f 1) -> 1"; "(f 2) -> 2"], Arrow_t ([Num_t], Num_t);
               ["(f #f 0) -> 1"; "(f #t 5) -> 2"], Arrow_t ([Bool_t; Num_t], Num_t);
               ["(f 1) -> 1"; "(f (f 2)) -> 2"], Arrow_t ([Num_t], Num_t);
               ["(f 1 []) -> [1]"; "(f 1 (f 2 [])) -> [2 1]"], Arrow_t ([Num_t; List_t Num_t], (List_t Num_t));
             ]

let () = run_test_tt_main 
           ("test-suite" >::: 
              [                 
                test_parse_expr;
                test_parse_example;
                test_parse_prog;
                (* test_parse_failure; *)

                test_eval; 
                test_eval_prog;

                (* "typeof_examples" >:: test_search_typeof_examples; *)
                test_typeof_value;
                test_typeof_example;
                test_specialize;
                test_signature;

                test_partition;
                test_m_partition;

                test_fold_constants;
                test_rewrite;
                test_normalize;
                test_denormalize;

                test_straight_solve;
                test_catamorphic_solve;
           ]);
;;
