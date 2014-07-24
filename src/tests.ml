open Core.Std
open OUnit2
open Ast

(* Configuration options. *)
let test_solve = Conf.make_bool "solve" false "By default, do not test solve functions."

let identity (x: 'a) : 'a = x

let cmp_partition a b = 
  let sort_partition p = List.sort ~cmp:Int.compare p in
  let sort_partition_list l = List.map ~f:sort_partition l
                              |> List.sort ~cmp:(List.compare ~cmp:Int.compare) in
  (sort_partition_list a) = (sort_partition_list b)

let m_expr_to_string = function Some e -> expr_to_string e | None -> "None"

let vals_to_string (res:(value list * value) list) =
  let val_to_string (v: value list * value) = 
    let (inputs, result) = v in
    let inputs_strs = List.map inputs ~f:value_to_string in
    (Ast.sexp "(" inputs_strs ")") ^ " = " ^ (value_to_string result) in
  let vals_strs = List.map res ~f:val_to_string in
  Ast.sexp "[" vals_strs "]"

let eval expr = Eval.eval (Util.empty_ctx ()) expr

let make_tests ?cmp:(cmp = (=)) ~in_f ~out_f ~in_str ~out_str ~res_str name cases = 
  name >:::
    (List.map ~f:(fun (input, output) -> 
                  let case_name = Printf.sprintf "%s => %s" (in_str input) (out_str output) in
                  case_name >:: (fun _ -> assert_equal ~printer:res_str ~cmp:cmp 
                                                       (out_f output) (in_f input)))
              cases)

let make_solve_tests ?cmp:(cmp = (=)) ~in_f ~out_f ~in_str ~out_str ~res_str name cases = 
  name >:::
    (List.map ~f:(fun (input, output) -> 
                  let case_name = Printf.sprintf "%s => %s" (in_str input) (out_str output) in
                  case_name >:: (fun ctx -> 
                                 skip_if (not (test_solve ctx)) "Skipping solve tests.";
                                 assert_equal ~printer:res_str ~cmp:cmp (out_f output) (in_f input)))
              cases)

let test_parse_expr =
  make_tests ~in_f:Util.parse_expr ~out_f:identity
              ~in_str:identity ~out_str:expr_to_string ~res_str:expr_to_string
              "parse_expr"
              [ "1", `Num 1;
                "#t", `Bool true;
                "#f", `Bool false;
                "[]:bool", `List ([], Bool_t);
                "[1]", `List ([`Num 1;], Num_t);
                "[1 2]", `List ([`Num 1; `Num 2;], Num_t);
                "[[]:num]", `List ([`List ([], Num_t)], List_t Num_t);
                "[[1]]", `List ([`List ([`Num 1], Num_t)], List_t Num_t);
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
                "(cons 1 []:num)", `Op (Cons, [`Num 1; `List ([], Num_t)]);
                "(cons 1 [2])", `Op (Cons, [`Num 1; `List ([`Num 2], Num_t)]);
                "(cdr []:num)", `Op (Cdr, [`List ([], Num_t)]);
                "(cdr [1 2])", `Op (Cdr, [`List ([`Num 1; `Num 2;], Num_t)]);
                "(f 1 2)", `Apply (`Id "f", [`Num 1; `Num 2]);
                "(> (f 1 2) 3)", `Op (Gt, [`Apply (`Id "f", [`Num 1; `Num 2]); `Num 3]);
                "(map x7 f6)", `Op (Map, [`Id "x7"; `Id "f6"]);
              ]

let test_parse_example = 
  make_tests ~in_f:Util.parse_example ~out_f:identity
              ~in_str:identity ~out_str:example_to_string ~res_str:example_to_string
              "parse_example"
              [ "(f 1) -> 1", ((`Apply (`Id "f", [`Num 1])), `Num 1); 
                "(f (f 1)) -> 1", ((`Apply (`Id "f", [`Apply (`Id "f", [`Num 1])])), `Num 1);
                "(f []:[num]) -> []:[num]", ((`Apply (`Id "f", [`List ([], List_t Num_t)])), (`List ([], List_t Num_t)));
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
                "[1]", `List ([`Num 1], Num_t);
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
                "(cons 4 []:num)", `List ([`Num 4], Num_t);
                "(cons 4 [1])", `List ([`Num 4; `Num 1], Num_t);
                "(car [1])", `Num 1;
                "(cdr [1 2])", `List ([`Num 2], Num_t);
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
                "(fold [[1] [2 1] [3 2 1]] (lambda (a:[num] e:num) (cons (car e) a)) []:num)",
                `List ([`Num 1; `Num 2; `Num 3], Num_t); (* Firsts *)
                "(foldl [1 2 3] (lambda (a:num e:num) (+ a e)) 0)", `Num 6; (* Sum *)
                "(foldl [[1] [2 1] [3 2 1]] (lambda (a:[num] e:num) (cons (car e) a)) []:num)",
                `List ([`Num 3; `Num 2; `Num 1], Num_t); (* Rev-firsts *)
                "(filter []:num (lambda (e:num) (> 3 e)))", `List ([], Num_t);
                "(filter [1 2 3 4] (lambda (e:num) (> 3 e)))", `List ([`Num 1; `Num 2], Num_t);
                "(filter [1 2 3 4] (lambda (e:num) (= 0 (% e 2))))", `List ([`Num 2; `Num 4], Num_t);
                "(map []:num (lambda (e:num) (+ e 1)))", `List ([], Num_t);
                "(map [1] (lambda (e:num) (+ e 1)))", `List ([`Num 2], Num_t);
                "(map [1 2] (lambda (e:num) (+ e 1)))", `List ([`Num 2; `Num 3], Num_t);
              ]

let test_eval_prog = 
  make_tests ~in_f:(fun str -> str |> Util.parse_prog |> Eval.prog_eval) ~out_f:identity
              ~in_str:identity ~out_str:value_to_string ~res_str:value_to_string
              "eval_prog"
              [ "(define a 1) (+ a 1)", `Num 2;
                "(define a 1) (define b (+ a 1)) (+ b 1)", `Num 3;
                "(define plus (lambda (a:num b:num) (+ a b))) (plus 1 2)", `Num 3;
                "(define a 1)", `Unit;
                "1 2 3", `Num 3;
                "(define last (lambda (l:[num]) (if (= []:num (cdr l)) (car l) (last (cdr l))))) (last [1 2 3])", 
                `Num 3;
                "(define f6 (lambda (e8:num) (+ 1 e8))) (define f (lambda (x7:[num]) (map x7 f6))) (f [1 2 3])", 
                `List ([`Num 2; `Num 3; `Num 4], Num_t);
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
  make_solve_tests
    ~in_f:(fun (_, example_strs, init_strs) -> 
           let solution = Search.solve ~init:(List.map init_strs ~f:Util.parse_expr) 
                                       (List.map example_strs ~f:Util.parse_example) [] in
           (solution :> expr option))
    ~out_f:(fun res_str -> Some (Util.parse_expr res_str))
    ~in_str:(fun (name, _, _) -> name) ~out_str:identity 
    ~res_str:(fun res -> match res with
                         | Some expr -> expr_to_string expr
                         | None -> "")
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
  make_solve_tests 
    ~in_f:(fun (_, example_strs, init_strs) ->
           let solution = Search.solve_catamorphic 
                            ~init:(List.map init_strs ~f:Util.parse_expr)
                            (List.map example_strs ~f:Util.parse_example) in
           (solution :> expr list))
    ~out_f:Util.parse_prog
    ~in_str:(fun (name, _, _) -> name) ~out_str:identity ~res_str:prog_to_string
    "catamorphic_solve"
    [
      ("sum", ["(f []:num) -> 0";
               "(f [1]) -> 1";
               "(f [1 2]) -> 3";
              ], []),
      "";

      ("sums", ["(f []:[num]) -> []:num";
                "(f [[]:num]) -> [0]";
                "(f [[1] []:num]) -> [1 0]";
                "(f [[1 2] [3 4]]) -> [3 7]";
               ], []),
      "";

      ("concat", ["(f []:[num]) -> []:num";
                  "(f [[1]]) -> [1]";
                  "(f [[1] [2]]) -> [1 2]";
                  "(f [[1] [3]]) -> [1 3]";
                 ], []),
      "";

      ("length", ["(f []:num) -> 0";
                  "(f [0]) -> 1";
                  "(f [0 0]) -> 2";
                 ], ["1"]),
      "";

      ("lengths", ["(f []:[num]) -> []:num";
                   "(f [[]:num]) -> [0]";
                   "(f [[1] [1 1] [1 1 1]]) -> [1 2 3]";
                  ], ["1"]),
      "";

      ("evens", ["(f []:num) -> []:num";
                 "(f [1]) -> []:num";
                 "(f [1 2]) -> [2]";
                 "(f [1 2 3 4]) -> [2 4]";
                ], ["0"; "2"]),
      "";

      ("odds", ["(f []:num) -> []:num";
                "(f [1]) -> [1]";
                "(f [1 2]) -> [1]";
                "(f [1 2 3 4]) -> [1 3]";
               ], ["0"; "2"]),
      "";

      ("zeroes", ["(f []:num) -> []:num";
                  "(f [0]) -> []:num";
                  "(f [1 0]) -> [1]";
                  "(f [1 0 2]) -> [1 2]";
                 ], ["0"]),
      "";

      ("incr", ["(f []:num) -> []:num";
                "(f [1]) -> [2]";
                "(f [1 2]) -> [2 3]";
                "(f [1 2 3 4]) -> [2 3 4 5]";
               ], ["1"]),
      "";

      ("allodd", ["(f []:num) -> #t";
                  "(f [1]) -> #t";
                  "(f [4]) -> #f";
                  "(f [1 3]) -> #t";
                  "(f [4 1]) -> #f";
                  "(f [2 1 2 3]) -> #f";
                 ], ["0"; "2"; "#t"; "#f"]),
      "";
    ]

let test_catamorphic_looped_solve =
  make_solve_tests 
    ~in_f:(fun (_, example_strs, init_strs) ->
           let solution = Search.solve_catamorphic_looped
                            ~init:(List.map init_strs ~f:Util.parse_expr)
                            (List.map example_strs ~f:Util.parse_example) in
           (solution :> program))
    ~out_f:Util.parse_prog
    ~in_str:(fun (name, _, _) -> name) ~out_str:identity ~res_str:prog_to_string
    "catamorphic_solve"
    [
      ("incr", ["(f []:num) -> []:num";
                "(f [1]) -> [2]";
                "(f [1 2]) -> [2 3]";
                "(f [1 2 3 4]) -> [2 3 4 5]";
               ], ["1"]),
      "";

      ("add", ["(f []:num 1) -> []:num";
                "(f [1] 1) -> [2]";
                "(f [1 2] 1) -> [2 3]";
                "(f [1 2] 2) -> [3 4]";
                "(f [1 2 3 4] 5) -> [6 7 8 9]";
               ], []),
      "";

      ("evens", ["(f []:num) -> []:num";
                 "(f [1]) -> []:num";
                 "(f [1 2]) -> [2]";
                 "(f [1 2 3 4]) -> [2 4]";
                ], ["0"; "2"]),
      "";

      ("odds", ["(f []:num) -> []:num";
                "(f [1]) -> [1]";
                "(f [1 2]) -> [1]";
                "(f [1 2 3 4]) -> [1 3]";
               ], ["0"; "2"]),
      "";

      ("zeroes", ["(f []:num) -> []:num";
                  "(f [0]) -> []:num";
                  "(f [1 0]) -> [1]";
                  "(f [1 0 2]) -> [1 2]";
                 ], ["0"]),
      "";

      ("concat", ["(f []:num []:num) -> []:num";
                  "(f [0] []:num) -> [0]";
                  "(f [1 0] [0]) -> [1 0 0]";
                  "(f [1 0 2] [3 4]) -> [1 0 2 3 4]";
                 ], []),
      "";

      ("reverse", ["(f []:num) -> []:num";
                   "(f [0] []:num) -> [0]";
                   "(f [1 0] [0]) -> [1 0 0]";
                   "(f [1 0 2] [3 4]) -> [1 0 2 3 4]";
                  ], []),
      "";
    ]

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

let test_typeof_value = 
  make_tests ~in_f:Eval.typeof_value ~out_f:identity
              ~in_str:value_to_string ~out_str:typ_to_string ~res_str:typ_to_string
              "typeof_value"
              [ `Num 1, Num_t;
                `Bool true, Bool_t;
                `List ([`Num 1; `Num 2], Num_t), List_t Num_t;
                `List ([`List ([`Num 1; `Num 2], Num_t)], List_t Num_t), List_t (List_t Num_t);
              ]

let test_typeof_example = 
  make_tests ~in_f:(fun ex -> ex |> Util.parse_example 
                              |> (Search.typeof_example (Util.empty_ctx ())))
             ~out_f:identity
             ~in_str:identity ~out_str:typ_to_string ~res_str:typ_to_string
             "typeof_example"
             [ "(f 1) -> 1", Arrow_t ([Num_t], Num_t);
               "(f 1) -> []:num", Arrow_t ([Num_t], List_t Num_t);
               "(f 1) -> [1]", Arrow_t ([Num_t], List_t Num_t);
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
               ["(f 1 []:num) -> [1]"; "(f 1 (f 2 []:num)) -> [2 1]"], 
               Arrow_t ([Num_t; List_t Num_t], (List_t Num_t));
             ]

let test_expand = 
  make_tests ~in_f:(fun e -> e |> Util.parse_expr |> Verify.expand (Util.empty_ctx ())) 
             ~out_f:Util.parse_expr
             ~in_str:identity ~out_str:identity ~res_str:expr_to_string
             "expand"
             [ 
               "(let x 2 (+ x 1))", "(+ 2 1)";
               "(let x 3 (lambda (a:num) (+ a x)))", "(lambda (a:num) (+ a 3))";
               "(let x 3 (lambda (x:num) (+ 5 x)))", "(lambda (x:num) (+ 5 x))";
               "(define y (let a (+ 1 2) (* a 3)))", "(define y (* (+ 1 2) 3))";
               "(let x 2 (let x 3 (let x 4 x)))", "4";
               "(let x 2 (let x 3 (let x 4 x)))", "4";
             ]

let test_expr_to_z3 =
  let zctx = Z3.mk_context [] in
  
  make_tests ~in_f:(fun e -> e 
                             |> Util.parse_expr 
                             |> Verify.expr_to_z3 zctx (Util.empty_ctx ()))
             ~out_f:identity 
             ~in_str:identity ~out_str:Z3.Expr.to_string ~res_str:Z3.Expr.to_string
             ~cmp:Z3.Expr.equal
             "expr_to_z3"
             [
               "(+ 1 2)", Z3.Arithmetic.mk_add zctx
                                               [ (Z3.Arithmetic.Integer.mk_numeral_i zctx 1);
                                                 (Z3.Arithmetic.Integer.mk_numeral_i zctx 2); ];
             ]

let test_verify = 
  let status_to_str = function
    | Verify.Invalid -> "Invalid"
    | Verify.Valid -> "Valid"
    | Verify.Error -> "Error" in
  make_tests 
    ~in_f:(fun (fdef_str, cs_strs) -> 
           let fdef = match Util.parse_expr fdef_str with 
             | `Define (n, `Lambda (a, b)) -> `Define (n, `Lambda (a, b)) 
             | _ -> assert_failure "Not a function definition." in
           let cs = List.map cs_strs ~f:Util.parse_constr in
           Verify.verify [] cs fdef)
    ~out_f:identity 
    ~in_str:(fun (fdef_str, cs_strs) -> String.concat ~sep:", " (fdef_str::cs_strs))
    ~out_str:status_to_str ~res_str:status_to_str
    "verify"
    [ 
      ("(define f (lambda (x:num) (+ x 1)))", [ "(forall (a:num) (> (f a) a))" ]), Verify.Valid;
      ("(define f (lambda (x:num) (+ x 1)))", [ "(forall (a:num) (= (f a) a))" ]), Verify.Invalid;
      ("(define f (lambda (x0:num x1:num) (if (< x0 x1) x1 x0)))", 
       [ "(forall (a:num b:num) (>= (f a b) a))";
         "(forall (a:num b:num) (>= (f a b) b))" ]), Verify.Valid;
      ("(define f (lambda (x0:num x1:num) (if (< x0 x1) x1 x0)))", 
       [ "(forall (a:num b:num) (>= (f a b) a))";
         "(forall (a:num b:num) (>= (f a b) b))"; 
         "(forall (a:num b:num) (= (f a b) b))"; 
      ]), Verify.Invalid;
      ("(define f (lambda (x:num) (= (% x 2) 0)))", [ "(forall (a:num) (= (f (* 2 a)) #t))" ]), Verify.Valid;
      ("(define f (lambda (x:num y:[num]) (cons x y)))", 
       [ "(forall (a:num b:[num]) (= (car (f a b)) a))" ]), Verify.Valid;
    ]

let test_sat_solver = 
  make_tests
    ~in_f:(fun (f_str, exs) -> SymbSolver.sat_solve (Util.parse_expr f_str) exs)
    ~out_f:Util.parse_expr
    ~in_str:(fun (f_str, exs) -> f_str ^ " " ^ (vals_to_string exs))
    ~out_str:identity
    ~res_str:expr_to_string
    "sat_solver"
    [ 
      ("(lambda (x:num y:num) (+ (+ x y) z))", [[`Num 1; `Num 2], `Num 3]), "(+ (+ x y) 0)";
      ("(lambda (x:num y:num) (+ (+ x y) z))", [[`Num 6; `Num 7], `Num 8]), "(+ (+ x y) -5)";
      ("(lambda (x:num y:num) (+ (+ (+ x y) z1) z2))", [[`Num 1;`Num 2],`Num 3]), "(+ (+ (+ x y) 0) 0)";
    ]

let test_symb_solver = 
  make_tests
    ~in_f:(fun (f_str, constr_strs, exs) -> 
           let f = Util.parse_expr f_str in
           let constrs = List.map constr_strs ~f:Util.parse_expr in
           SymbSolver.symb_solve f constrs exs)
    ~out_f:Util.parse_expr
    ~in_str:(fun (f_str, constr_strs, exs) -> 
             Printf.sprintf "%s, %s, %s" f_str (String.concat ~sep:" " constr_strs) (vals_to_string exs))
    ~out_str:identity
    ~res_str:expr_to_string
    "symb_solver"
    [
      ("(lambda (x:num y:num) (+ (+ x y) z))", [], [[`Num 1; `Num 2], `Num 3]), 
      "(+ (+ x y) 0)"; 
      ("(lambda (x:num y:num) (+ (+ x y) z))", [ "(< z 1)" ], [[`Num 1; `Num 2], `Num 3]), 
      "(+ (+ x y) 0)";
      ("(lambda (x:num y:num) (+ (+ x y) z))", [ "(< z 1)" ], [[`Num 6; `Num 7], `Num 8]),
      "(+ (+ x y) -5)";
      ("(lambda (x:num y:num) (+ (+ x y) z))", [ "(< z 1)"; "(> z (- 0 1))" ], [[`Num 1; `Num 2], `Num 3]),
      "(+ (+ x y) 0)";
      ("(lambda (x:num y:num) (+ (+ (+ x y) z1) z2))", [ "(< z1 2)"; "(<z2 2)" ], [[`Num 1; `Num 2], `Num 3]),
      "(+ (+ (+ x y) 0) 0)";
      ("(lambda (x:num y:num) (+ (+ (+ x y) z1) z2))", [ "(< z1 (- 0 2))"; "(> z2 2)" ], [[`Num 1; `Num 2], `Num 3]),
      "(+ (+ (+ x y) -3) 3)";
      ("(lambda (x:num y:num) (+ (+ x y) z))", [ "(< (f 1 2) 4)" ], [[`Num 1; `Num 2], `Num 3]), 
      "(+ (+ x y) 0)";
      ("(lambda (x:num y:num) (+ (+ (* x z1) z2) y))", [ "(< (f 2 3) 4)"; "(< 0 z2)"], [[`Num 1; `Num 2], `Num 0]), 
      "(+ (+ (* x -3) 1) y)";
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

                test_typeof_value;
                test_typeof_example;
                test_signature;

                test_expand;
                test_expr_to_z3;
                test_verify;
                
                test_partition;
                test_m_partition;

                test_fold_constants;
                test_rewrite;
                test_normalize;
                test_denormalize;

                test_sat_solver;
                test_symb_solver;

                test_straight_solve;
                test_catamorphic_looped_solve;
           (* test_catamorphic_solve; *)
           ]);
