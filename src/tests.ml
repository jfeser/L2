open Core.Std
open OUnit2
open Ast

let assert_partition_equal (a:int list list) (b:int list list) =
  let sort_partition p = List.sort ~cmp:Int.compare p in
  let sort_partition_list l = 
    List.map ~f:sort_partition l
    |> List.sort ~cmp:(List.compare ~cmp:Int.compare) in
  assert_equal (sort_partition_list a) (sort_partition_list b)

let assert_parse_equal str exprs = assert_equal (Util.parse str) exprs
let assert_parse_raises str exn = assert_raises exn (fun () -> (Util.parse str))

let assert_eval_equal expr value =
  match Util.parse expr with
  | [e] -> assert_equal ~printer:value_to_string value (Eval.eval Eval.empty_eval_ctx e)
  | _ -> assert_failure "Too many expressions to eval."

let assert_prog_equal prog value = 
  assert_equal value (Eval.prog_eval (Util.parse prog))

let assert_solve result examples init = 
  let res_expr = List.hd_exn @@ Util.parse result in
  assert_equal ~printer:expr_to_string res_expr 
               (Search.solve examples ~init:init)

let assert_solve_cata (result: string) (examples: Search.example list) (init: expr list) = 
  let res_expr = List.hd_exn @@ Util.parse result in
  assert_equal ~printer:expr_to_string res_expr 
               (Search.solve_catamorphic examples ~init:init)

let make_tests tests_name res_to_string assert_f cases = 
  tests_name >::: 
    (List.map ~f:(fun (str, res) -> 
                  let title = Printf.sprintf "%s -> %s" str (res_to_string res) in
                  title >:: (fun _ -> assert_f str res))
              cases)

let test_parse_success = 
  let parse_to_string ps = ps |> List.map ~f:expr_to_string |> String.concat ~sep:" " in
  make_tests
    "parse_success" parse_to_string assert_parse_equal
    [ "1", [`Num 1];
      "1 2 3", [`Num 1; `Num 2; `Num 3];
      "#t", [`Bool true];
      "#f", [`Bool false];
      "nil", [`Nil];
      "[]", [`List []];
      "[1]", [`List [`Num 1;]];
      "[1 2]", [`List [`Num 1; `Num 2;]];
      "[[]]", [`List [`List []]];
      "[[1]]", [`List [`List [`Num 1;]]];
      "a", [`Id "a"];
      "test", [`Id "test"];
      "(+ (+ 1 2) 3)", [`Op (Plus, [`Op (Plus, [`Num 1; `Num 2]); `Num 3;])];
      "(let f (lambda (x:num) (if (= x 0) 0 (+ (f (- x 1)) 1))) (f 0))", 
      [`Let ("f", `Lambda ([("x", Num_t)], 
                           `Op (If, [`Op (Eq, [`Id "x"; `Num 0]);
                                     `Num 0;
                                     `Op (Plus, [`Apply (`Id "f",
                                                         [`Op (Minus, [`Id "x"; 
                                                                       `Num 1])]);
                                                 `Num 1])])),
             `Apply (`Id "f", [`Num 0]))];
      "(+ 1 2)", [`Op (Plus, [`Num 1; `Num 2])];
      "(cons 1 [])", [`Op (Cons, [`Num 1; `List []])];
      "(cons 1 [2])", [`Op (Cons, [`Num 1; `List [`Num 2]])];
      "(cdr [])", [`Op (Cdr, [`List []])];
      "(cdr [1 2])", [`Op (Cdr, [`List [`Num 1; `Num 2;]])];
    ]

let test_parse_failure = 
  make_tests
    "parse_failure" (fun _ -> "Parser.Error") assert_parse_raises
    [ "[", Parser.Error;
      "[(])", Parser.Error;
      "(+ 1)", Parser.Error;
    ]

let test_eval = 
  make_tests 
    "eval" value_to_string assert_eval_equal
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
      "(foldl [1 2 3] (lambda (a:num e:num) (+ a e)) 0)", `Num 6; (* Sum *)
      "(foldl [[1] [2 1] [3 2 1]] (lambda (a:[num] e:num) (cons (car e) a)) [])", 
      `List [`Num 3; `Num 2; `Num 1]; (* Rev-firsts *)
    ]

let test_eval_prog = 
  make_tests 
    "eval_prog" value_to_string assert_prog_equal
    [ "(define a 1) (+ a 1)", (`Num 2);
      "(define a 1) (define b (+ a 1)) (+ b 1)", (`Num 3);
      "(define plus (lambda (a:num b:num) (+ a b))) (plus 1 2)", (`Num 3);
      "(define a 1)", `Nil;
      "1 2 3", (`Num 3);
    ]

let test_straight_solve = 
  "straight_solve" >::: 
    (List.map ~f:(fun (str, examples, init) -> 
                  let title = str in
                  title >:: (fun _ -> assert_solve str examples init))
              [ "(define f (lambda (x0:num x1:num) (+ x0 x1)))", 
                [([`Num 1; `Num 1], `Num 2);
                 ([`Num 2; `Num 1], `Num 3)],  
                [];

                "(define f (lambda (x0:num x1:num) (if (< x0 x1) x1 x0)))",
                [([`Num 3; `Num 5], `Num 5);
                 ([`Num 5; `Num 3], `Num 5);
                 ([`Num (-1); `Num 1], `Num 1)], 
                [];

                "(define f (lambda (x0:[num]) (car (cdr x0))))",
                [([`List [`Num 1; `Num 2]], `Num 2);
                 ([`List [`Num 1; `Num 3]], `Num 3)], 
                [];
    ])

let test_catamorphic_solve = 
  "catamorphic_solve" >:::
    (List.map ~f:(fun (str, examples, init) -> 
                  let title = str in
                  title >:: (fun _ -> assert_solve_cata str examples init))
              [ "(define f (lambda (x0:[num]) (foldl x0 (lambda (a:num e:num) (+ a e)) 0)))", 
                [ ([`Nil], `Num 0);
                  ([`List [`Num 1]], `Num 1);
                  ([`List [`Num 1; `Num 2]], `Num 3);
                ], [];
                "(define f (lambda (x0:[[num]]) (foldl x0 (lambda (a:[num] e:num) (cons (car e) a)) [])))",
                [ ([`Nil], `Nil);
                  ([`List [`List [`Num 1]]], `List [`Num 1]);
                  ([`List [`List [`Num 1]; `List [`Num 2]]], `List [`Num 2; `Num 1]);
                ], [];

                "nil", (*length*)
                [ ([`Nil], `Num 0);
                  ([`List [`Num 0]], `Num 1);
                  ([`List [`Num 0; `Num 0]], `Num 2);], [`Num 1];
    (* "(define f (lambda (x0:[num]) (car (cdr x0))))", *)
    (* [([`List [`Num 1; `Num 2]], `Num 2); *)
    (*  ([`List [`Num 1; `Num 3]], `Num 3)],  *)
    (* []; *)
    ])

let partition_to_string = List.to_string ~f:(List.to_string ~f:Int.to_string)
let test_partition =
  "test_partition" >:::
    (List.map ~f:(fun (n, p) ->
                  let title = Printf.sprintf "%s -> %s" 
                                             (Int.to_string n)
                                             (partition_to_string p) in
                  title >:: (fun _ -> assert_partition_equal (Util.partition n) p))
              [ 0, [];
                1, [[1]];
                2, [[2]; [1; 1]];
                3, [[3]; [1; 2]; [1; 1; 1]];
    ])

let test_m_partition =
  "test_m_partition" >:::
    (List.map ~f:(fun (n, m, p) ->
                  let title = Printf.sprintf "%s -> %s" 
                                             (Int.to_string n)
                                             (partition_to_string p) in
                  title >:: (fun _ -> assert_partition_equal (Util.m_partition n m) p))
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


(*Helper methods for sat solver and symb solver test suites*)
let exact_parse_from_string exp = 
  (match (Util.parse exp) with
  | hd::_ -> hd
  | [] -> assert false)
  

let vals_to_string (res:(value list * value) list) =
  let rec list_to_string (in_list:value list)= (match in_list with
  | `Num(hd)::tl -> String.concat ~sep:"" [string_of_int hd; " "; list_to_string tl]
  | _ -> "") in 
  let rec vals_to_string_helper (res:(value list * value) list) = (match res with
    | (hd1,`Num(hd2))::tl -> String.concat ~sep:"" ["(";String.strip (list_to_string hd1) ;") = "; string_of_int hd2;") "; vals_to_string_helper tl]
    | _ -> "") in
  String.concat ~sep:"" ["[";String.strip (vals_to_string_helper res);"]"]

let test_sat_solver = 
  "test_sat_solver" >:::
      (List.map ~f:(fun (n, (m:(value list * value) list), p) ->
                  let title = Printf.sprintf "%s %s -> %s" 
                                             n
                                             (vals_to_string m)
                                             p
                                             in
                  title >:: (fun _ -> (assert_equal ~printer:(fun x -> x) p (expr_to_string (SymbSolver.sat_solve (exact_parse_from_string n) m)))))
              [ "(lambda (x:num y:num) (+ (+ x y) z))" , [([`Num 1;`Num 2],`Num 3)], "(+ (+ x y) 0)";
                "(lambda (x:num y:num) (+ (+ x y) z))" , [([`Num 6;`Num 7],`Num 8)], "(+ (+ x y) -5)";
                "(lambda (x:num y:num) (+ (+ (+ x y) z1) z2))" , [([`Num 1;`Num 2],`Num 3)], "(+ (+ (+ x y) 0) 0)"
                  
            ])

let test_symb_solver = 
  "test_symb_solver" >:::
      (List.map ~f:(fun (n, c, (m:(value list * value) list), p) ->
                  let title = Printf.sprintf "%s %s %s -> %s" 
                                             n
                                             (String.concat ~sep:"\n" c)
                                             (vals_to_string m)
                                             p
                                             in
                  title >:: (fun _ -> assert_equal ~printer:(fun x -> x) p (expr_to_string (SymbSolver.symb_solve (exact_parse_from_string n) (List.map ~f:(exact_parse_from_string) c) m))))
              [
              "(lambda (x:num y:num) (+ (+ x y) z))" , [], [([`Num 1;`Num 2],`Num 3)], "(+ (+ x y) 0)"; 
              "(lambda (x:num y:num) (+ (+ x y) z))" , ["(< z 1)"], [([`Num 1;`Num 2],`Num 3)], "(+ (+ x y) 0)";
              "(lambda (x:num y:num) (+ (+ x y) z))" , ["(< z 1)"], [([`Num 6;`Num 7],`Num 8)], "(+ (+ x y) -5)";
              "(lambda (x:num y:num) (+ (+ x y) z))" , ["(< z 1)";"(> z (- 0 1))"], [([`Num 1;`Num 2],`Num 3)], "(+ (+ x y) 0)";
              "(lambda (x:num y:num) (+ (+ (+ x y) z1) z2))" ,["(< z1 2)"; "(<z2 2)"], [([`Num 1;`Num 2],`Num 3)], "(+ (+ (+ x y) 0) 0)";
              "(lambda (x:num y:num) (+ (+ (+ x y) z1) z2))" ,["(< z1 (- 0 2))"; "(> z2 2)"], [([`Num 1;`Num 2],`Num 3)], "(+ (+ (+ x y) -3) 3)";
              "(lambda (x:num y:num) (+ (+ x y) z))" , ["(< (f 1 2) 4)"], [([`Num 1;`Num 2],`Num 3)], "(+ (+ x y) 0)";
              "(lambda (x:num y:num) (+ (+ (* x z1) z2) y))" , ["(< (f 2 3) 4)"; "(< 0 z2)"], [([`Num 1;`Num 2],`Num 0)], "(+ (+ (* x -3) 1) y)";

            ])

let test_eval_typeof_value _ = 
  assert_equal Num_t (Eval.typeof_value (`Num 1));
  assert_equal Bool_t (Eval.typeof_value (`Bool true));
  assert_equal (List_t Num_t) (Eval.typeof_value (`List [`Num 1; `Num 2]));
  assert_equal (List_t Nil_t) (Eval.typeof_value (`List [`Nil; `Nil]));
  assert_equal (List_t (List_t Num_t))
               (Eval.typeof_value (`List [(`List [`Num 1]); `Nil]));
(* assert_raises Eval.SolveError *)
(*               (fun _ -> Eval.typeof_value (`List [`Num 1; `Bool true])); *)
(* assert_raises Eval.SolveError  *)
(*               (fun _ -> Eval.typeof_value (`List [`Nil; `Bool true])); *)
(* assert_raises Eval.SolveError *)
(*               (fun _ -> Eval.typeof_value (`List [(`List [`Num 1]); *)
(*                                                    (`List [`Bool true])])); *)
;;

let test_search_typeof_examples _ =
  assert_equal (Arrow_t ([Num_t], Num_t))
               (Search.signature (Eval.empty_type_ctx) [([`Num 1], `Num 2); 
                                                        ([`Num 2], `Num 3)]);
  assert_equal (Arrow_t ([(List_t Num_t)], Num_t))
               (Search.signature (Eval.empty_type_ctx) [([`List [`Num 1; `Num 2]], `Num 2)]);
;;

let () = run_test_tt_main 
           ("test-suite" >::: 
              [ test_eval; 
                test_partition;
                test_m_partition;
                "typeof_examples" >:: test_search_typeof_examples;
                "typeof_value" >:: test_eval_typeof_value;
                test_eval_prog;
                test_parse_success;
                test_parse_failure;
                test_specialize;
                test_straight_solve;
                test_catamorphic_solve;
                test_sat_solver;
                test_symb_solver
           ]);
;;
