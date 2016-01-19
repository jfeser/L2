open Core.Std
open OUnit2

open Ast
open Collections
open Infer

let identity (x: 'a) : 'a = x

let cmp_partition a b =
  let sort_partition p = List.sort ~cmp:Int.compare p in
  let sort_partition_list l = List.map ~f:sort_partition l
                              |> List.sort ~cmp:(List.compare Int.compare) in
  (sort_partition_list a) = (sort_partition_list b)

let m_expr_to_string = function Some e -> Expr.to_string e | None -> "None"

(* let vals_to_string (res:(value list * value) list) = *)
(*   let val_to_string (v: value list * value) = *)
(*     let (inputs, result) = v in *)
(*     let inputs_strs = List.map inputs ~f:value_to_string in *)
(*     (Ast.sexp "(" inputs_strs ")") ^ " = " ^ (value_to_string result) in *)
(*   let vals_strs = List.map res ~f:val_to_string in *)
(*   Ast.sexp "[" vals_strs "]" *)

let make_tests ?cmp:(cmp = (=)) ~in_f ~out_f ~in_str ~out_str ~res_str name cases =
  name >:::
  (List.map ~f:(fun (input, output) ->
       let case_name = Printf.sprintf "%s => %s" (in_str input) (out_str output) in
       case_name >:: (fun _ -> assert_equal ~printer:res_str ~cmp:cmp
                         (out_f output) (in_f input)))
      cases)

(* let make_solve_tests ?cmp:(cmp = (=)) ~in_f ~out_f ~in_str ~out_str ~res_str name cases = *)
(*   name >::: *)
(*     (List.map ~f:(fun (input, output) -> *)
(*                   let case_name = Printf.sprintf "%s => %s" (in_str input) (out_str output) in *)
(*                   case_name >:: (fun ctx -> *)
(*                                  skip_if (not (test_solve ctx)) "Skipping solve tests."; *)
(*                                  assert_equal ~printer:res_str ~cmp:cmp (out_f output) (in_f input))) *)
(*               cases) *)

let test_parse_expr =
  let open Collections.Tree in
  make_tests ~in_f:Expr.of_string ~out_f:identity
    ~in_str:identity ~out_str:Expr.to_string ~res_str:Expr.to_string
    "parse_expr"
    [ "1", `Num 1;
      "#t", `Bool true;
      "#f", `Bool false;
      "[]", `List [];
      "[1]", `List [`Num 1];
      "[1 2]", `List [`Num 1; `Num 2];
      "[[]]", `List [`List []];
      "[[1]]", `List [`List [`Num 1]];
      "a", `Id "a";
      "test", `Id "test";
      "(+ (+ 1 2) 3)", `Op (Plus, [`Op (Plus, [`Num 1; `Num 2]); `Num 3;]);
      "(let f (lambda (x) (if (= x 0) 0 (+ (f (- x 1)) 1))) (f 0))",
      `Let ("f", `Lambda (["x"],
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
      "(f 1 2)", `Apply (`Id "f", [`Num 1; `Num 2]);
      "(> (f 1 2) 3)", `Op (Gt, [`Apply (`Id "f", [`Num 1; `Num 2]); `Num 3]);
      "(map x7 f6)", `Apply (`Id "map", [`Id "x7"; `Id "f6"]);
      "{}", `Tree Empty;
      "{1}", `Tree (Node (`Num 1, []));
      "{1 {}}", `Tree (Node (`Num 1, [Empty]));
    ]

let test_parse_typ =
  make_tests ~in_f:Type.of_string ~out_f:identity
    ~in_str:identity ~out_str:Type.to_string ~res_str:Type.to_string
    "parse_typ"
    [ "num", Const_t Num_t;
    ]

let test_parse_example =
  make_tests ~in_f:Example.of_string ~out_f:identity
    ~in_str:identity ~out_str:Example.to_string ~res_str:Example.to_string
    "parse_example"
    [ "(f 1) -> 1", ((`Apply (`Id "f", [`Num 1])), `Num 1);
      "(f (f 1)) -> 1", ((`Apply (`Id "f", [`Apply (`Id "f", [`Num 1])])), `Num 1);
      "(f []) -> []", ((`Apply (`Id "f", [`List []])), (`List []));
    ]

let test_eval =
  let open Eval in
  let open Collections.Tree in
  make_tests ~in_f:(fun str -> str |> Expr.of_string |> (eval (Ctx.empty ())))
    ~out_f:identity
    ~in_str:identity ~out_str:value_to_string ~res_str:value_to_string
    "eval"
    [ "1", `Num 1;
      "#t", `Bool true;
      "#f", `Bool false;
      "[1]", `List [`Num 1];
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
      "(let f (lambda (x) (+ 1 x)) (f 1))", `Num 2;
      "(let f (lambda (x y) (+ y x)) (f 1 2))", `Num 3;
      "(let f (lambda (x) (lambda (y) (+ x y))) ((f 1) 2))", `Num 3;
      "(let f (lambda (x) (+ x 1)) (let g (lambda (x) (+ 1 x)) (f (g 1))))", `Num 3;
      "(let f (lambda (x) (if (= x 0) 0 (f (- x 1)))) (f 0))", `Num 0;
      "(let f (lambda (x) (if (= x 0) 0 (f (- x 1)))) (f 5))", `Num 0;
      "(foldr [1 2 3] (lambda (a e) (+ a e)) 0)", `Num 6; (* Sum *)
      "(foldr [[1] [2 1] [3 2 1]] (lambda (a e) (cons (car e) a)) [])",
      `List [`Num 1; `Num 2; `Num 3]; (* Firsts *)
      "(foldl [1 2 3] (lambda (a e) (+ a e)) 0)", `Num 6; (* Sum *)
      "(foldl [[1] [2 1] [3 2 1]] (lambda (a e) (cons (car e) a)) [])",
      `List [`Num 3; `Num 2; `Num 1]; (* Rev-firsts *)
      "(filter [] (lambda (e) (> 3 e)))", `List [];
      "(filter [1 2 3 4] (lambda (e) (> 3 e)))", `List [`Num 1; `Num 2];
      "(filter [1 2 3 4] (lambda (e) (= 0 (% e 2))))", `List [`Num 2; `Num 4];
      "(map [] (lambda (e) (+ e 1)))", `List [];
      "(map [1] (lambda (e) (+ e 1)))", `List [`Num 2];
      "(map [1 2] (lambda (e) (+ e 1)))", `List [`Num 2; `Num 3];
      "(map [0 1 0] (lambda (e) (= e 0)))", `List [`Bool true; `Bool false; `Bool true];
      "{}", `Tree (Empty);
      "(tree 1 [])", `Tree (Node (`Num 1, []));
      "(tree 1 [(tree 1 [])])", `Tree (Node (`Num 1, [Node (`Num 1, [])]));
      "(value (tree 1 [(tree 1 [])]))", `Num 1;
      "(value (tree 1 []))", `Num 1;
      "(mapt (tree 1 []) (lambda (e) (+ e 1)))", `Tree (Node (`Num 2, []));
      "(mapt (tree 1 [(tree 1 [])]) (lambda (e) (+ e 1)))", `Tree (Node (`Num 2, [Node (`Num 2, [])]));
      "(mapt {1 {1}} (lambda (e) (+ e 1)))", `Tree (Node (`Num 2, [Node (`Num 2, [])]));
      "(let max (lambda (x) (foldl x (lambda (a e) (if (> e a) e a)) 0)) (max [1 2 3]))", `Num 3;
      "(let max (lambda (x) (foldl x (lambda (a e) (if (> e a) e a)) 0)) (max [0 1 5 9]))", `Num 9;
      "(let max (lambda (x) (foldl x (lambda (a e) (if (> e a) e a)) 0)) (let dropmax (lambda (y) (filter y (lambda (z) (< z (max y))))) (dropmax [1 5 0 9])))",
      `List [`Num 1; `Num 5; `Num 0];
      "(let member (lambda (l x) (foldl l (lambda (a e ) (| (= e x) a)) #f)) (member [] 0))", `Bool false;
      "(let member (lambda (l x) (foldl l (lambda (a e ) (| (= e x) a)) #f)) (member [0] 0))", `Bool true;
      "(let member (lambda (l x) (foldl l (lambda (a e ) (| (= e x) a)) #f)) (member [0 1 ] 0))", `Bool true;
      "(let count (lambda (l x) (foldl l (lambda (a e) (if (= e x) (+ a 1) a)) 0)) (count [1 2 3 4 4] 4))", `Num 2;
      "(let last (lambda (a) (foldl a (lambda (c b) b) 0))
                 (let shiftr (lambda (a) (foldr a (lambda (c b) (foldl c (lambda (e d) (cons (last a) (cons b (cdr c)))) [1])) [])) (shiftr [6 5 3 7 8])))", `List [`Num 8; `Num 6; `Num 5; `Num 3; `Num 7];
      "(let last (lambda (a) (foldl a (lambda (c b) b) 0))
                 (let shiftr (lambda (a) (foldr a (lambda (c b) (foldl c (lambda (e d) (cons (last a) (cons b (cdr c)))) [1])) [])) (shiftr [4 0 5])))", `List [`Num 5; `Num 4; `Num 0];
    ]

let test_fold_constants =
  make_tests ~in_f:(fun str -> str |> Expr.of_string |> Rewrite.fold_constants)
    ~out_f:(fun str -> Some (Expr.of_string str))
    ~in_str:identity ~out_str:identity
    ~res_str:m_expr_to_string
    "fold_constants"
    [ "1", "1";
      "#f", "#f";
      "[]", "[]";
      "[1 2]", "[1 2]";
      "(+ 1 2)", "3";
      "(+ (* 0 5) (/ 4 2))", "2";
      "(+ a (- 4 3))", "(+ a 1)";
      "(lambda (x) (+ x (* 1 5)))", "(lambda (x) (+ x 5))";
      "(lambda (x) (+ 1 (* 1 5)))", "6";
    ]

(* let test_rewrite = *)
(*   make_tests ~in_f:(fun str -> str |> Expr.of_string |> Rewrite.rewrite) *)
(*     ~out_f:(fun str -> Some (Expr.of_string str)) *)
(*     ~in_str:identity ~out_str:identity *)
(*     ~res_str:m_expr_to_string *)
(*     "rewrite" *)
(*     [ "1", "1"; *)
(*       "#f", "#f"; *)
(*       "[]", "[]"; *)
(*       "[1 2]", "[1 2]"; *)
(*       "(+ x 0)", "x"; *)
(*       "(+ 0 x)", "x"; *)
(*       "(+ 1 x)", "(+ 1 x)"; *)
(*       "(- x 0)", "x"; *)
(*       "(\* x 0)", "0"; *)
(*       "(\* 0 x)", "0"; *)
(*       "(\* x 1)", "x"; *)
(*       "(\* 1 x)", "x"; *)
(*       "(/ x 1)", "x"; *)
(*       "(/ 0 x)", "0"; *)
(*       "(/ x x)", "1"; *)
(*       "(% 0 x)", "0"; *)
(*       "(% x 1)", "0"; *)
(*       "(% x x)", "0"; *)
(*       "(!= x y)", "(!= x y)"; *)
(*       "(!= x x)", "#f"; *)
(*       "(+ (- y x) x)", "y"; *)
(*       "(- (+ y x) x)", "y"; *)
(*       "(- (+ y x) y)", "x"; *)
(*       "(= (= x y) #f)", "(!= x y)"; *)
(*     ] *)

(* let test_normalize = *)
(*   make_tests ~in_f:(fun str -> str |> Expr.of_string |> Rewrite.normalize) ~out_f:Expr.of_string *)
(*               ~in_str:identity ~out_str:identity ~res_str:Expr.to_string *)
(*     "normalize" *)
(*     [ "(+ 1 (+ 2 3))", "(+ 1 2 3)"; *)
(*       "(+ (+ 1 2) (+ 3 4))", "(+ 1 2 3 4)"; *)
(*       "(+ (\* (\* 0 1) 2) (+ 3 4))", "(+ (\* 0 1 2) 3 4)"; *)
(*       "(+ 1 (- 2 3))", "(+ (- 2 3) 1)"; *)
(*       "(- 1 (- 2 3))", "(- 1 (- 2 3))"; *)
(*     ] *)

(* let test_denormalize = *)
(*   make_tests ~in_f:(fun str -> str |> Expr.of_string |> Rewrite.denormalize) ~out_f:Expr.of_string *)
(*               ~in_str:identity ~out_str:identity ~res_str:Expr.to_string *)
(*     "normalize" *)
(*     [ "(+ 1 2 3)", "(+ 1 (+ 2 3))"; *)
(*       "(+ 1 2 3 4)", "(+ 1 (+ 2 (+ 3 4)))"; *)
(*       "(+ (\* 0 1 2) 3 4)", "(+ (\* 0 (\* 1 2)) (+ 3 4))"; *)
(*     ] *)

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

(* let test_signature = *)
(*   make_tests ~in_f:(fun exs -> exs |> List.map ~f:Example.of_string |> Search.signature |> Infer.normalize) *)
(*              ~out_f:Type.of_string *)
(*              ~in_str:(fun exs -> "[" ^ (String.concat ~sep:"; " exs) ^ "]") *)
(*              ~out_str:identity ~res_str:Type.to_string *)
(*              "signature" *)
(*              [ ["(f 1) -> 1"; "(f 2) -> 2"], "num -> num"; *)
(*                ["(f #f 0) -> 1"; "(f #t 5) -> 2"], "(bool, num) -> num"; *)
(*                ["(f 1) -> 1"; "(f (f 2)) -> 2"], "num -> num"; *)
(*                ["(f 1 []) -> [1]";  *)
(*                 "(f 1 (f 2 [])) -> [2 1]"], "(num, list[num]) -> list[num]"; *)
(*                ["(f2 [0] 0) -> [0]"; *)
(*                 "(f2 (f2 [1 0] 1) 0) -> [1 0 0]"; *)
(*                 "(f2 (f2 (f2 [1 0 2] 1) 2) 0) -> [1 0 2 3 4]"; *)
(*                 "(f2 [0] 0) -> [0]"; *)
(*                 "(f2 (f2 [1 0] 1) 0) -> [1 0 0]"; *)
(*                 "(f2 (f2 (f2 [1 0 2] 1) 0) 2) -> [1 0 2 3 4]";], "(list[num], num) -> list[num]"; *)
(*                ["(f []) -> []"; *)
(*                 "(f [1]) -> [2]"; *)
(*                 "(f [1 2]) -> [2 3]"; *)
(*                 "(f [1 2 3 4]) -> [2 3 4 5]";], "list[num] -> list[num]"; *)
(*                ["(f {}) -> {}"; *)
(*                 "(f {1}) -> {2}"; *)
(*                 "(f {1 {2}}) -> {2 {3}}";], "tree[num] -> tree[num]"; *)
(*              ] *)

(* let test_expand = *)
(*   make_tests ~in_f:(fun e -> e |> Expr.of_string |> Verify.expand (Ctx.empty ())) *)
(*              ~out_f:Expr.of_string *)
(*              ~in_str:identity ~out_str:identity ~res_str:Expr.to_string *)
(*              "expand" *)
(*              [ *)
(*                "(let x 2 (+ x 1))", "(+ 2 1)"; *)
(*                "(let x 3 (lambda (a:num):num (+ a x)))", "(lambda (a:num):num (+ a 3))"; *)
(*                "(let x 3 (lambda (x:num):num (+ 5 x)))", "(lambda (x:num):num (+ 5 x))"; *)
(*                "(define y (let a (+ 1 2) (\* a 3)))", "(define y (\* (+ 1 2) 3))"; *)
(*                "(let x 2 (let x 3 (let x 4 x)))", "4"; *)
(*                "(let x 2 (let x 3 (let x 4 x)))", "4"; *)
(*              ] *)

(* let test_verify = *)
(*   let status_to_str = function *)
(*     | Verify.Invalid -> "Invalid" *)
(*     | Verify.Valid -> "Valid" *)
(*     | Verify.Error -> "Error" in *)
(*   make_tests *)
(*     ~in_f:(fun (lambda_str, cs_strs) -> *)
(*            let lambda = Expr.of_string lambda_str in *)
(*            let target expr = `Let ("f", lambda, expr) in *)
(*            let constraints = List.map cs_strs ~f:Util.parse_constr in *)
(*            Verify.verify [] constraints target) *)
(*     ~out_f:identity *)
(*     ~in_str:(fun (fdef_str, cs_strs) -> String.concat ~sep:", " (fdef_str::cs_strs)) *)
(*     ~out_str:status_to_str ~res_str:status_to_str *)
(*     "verify" *)
(*     [ *)
(*       ("(lambda (x) (+ x 1))", [ "(forall (a) (> (f a) a))" ]), Verify.Valid; *)
(*       ("(lambda (x) (+ x 1))", [ "(forall (a) (= (f a) a))" ]), Verify.Invalid; *)
(*       ("(lambda (x0 x1) (if (< x0 x1) x1 x0))", *)
(*        [ "(forall (a b) (>= (f a b) a))";  *)
(*          "(forall (a b) (>= (f a b) b))" ]), Verify.Valid; *)
(*       ("(lambda (x0 x1) (if (< x0 x1) x1 x0))", *)
(*        [ "(forall (a b) (>= (f a b) a))"; *)
(*          "(forall (a b) (>= (f a b) b))"; *)
(*          "(forall (a b) (= (f a b) b))"; *)
(*       ]), Verify.Invalid; *)
(*       ("(lambda (x) (= (% x 2) 0))", [ "(forall (a) (= (f (\* 2 a)) #t))" ]), Verify.Valid; *)
(*       ("(lambda (x y) (cons x y))", [ "(forall (a b) (= (car (f a b)) a))" ]), Verify.Valid; *)
(*     ] *)

(* let test_sat_solver = *)
(*   make_tests *)
(*     ~in_f:(fun (f_str, exs) -> SymbSolver.sat_solve (Expr.of_string f_str) exs) *)
(*     ~out_f:Expr.of_string *)
(*     ~in_str:(fun (f_str, exs) -> f_str ^ " " ^ (vals_to_string exs)) *)
(*     ~out_str:identity *)
(*     ~res_str:Expr.to_string *)
(*     "sat_solver" *)
(*     [ *)
(*       ("(lambda (x:num y:num):num (+ (+ x y) z))", [[`Num 1; `Num 2], `Num 3]), "(+ (+ x y) 0)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ x y) z))", [[`Num 6; `Num 7], `Num 8]), "(+ (+ x y) -5)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ (+ x y) z1) z2))", [[`Num 1;`Num 2],`Num 3]), "(+ (+ (+ x y) 0) 0)"; *)
(*     ] *)

(* let test_symb_solver = *)
(*   make_tests *)
(*     ~in_f:(fun (f_str, constr_strs, exs) -> *)
(*            let f = Expr.of_string f_str in *)
(*            let constrs = List.map constr_strs ~f:Expr.of_string in *)
(*            SymbSolver.symb_solve f constrs exs) *)
(*     ~out_f:Expr.of_string *)
(*     ~in_str:(fun (f_str, constr_strs, exs) -> *)
(*              Printf.sprintf "%s, %s, %s" f_str (String.concat ~sep:" " constr_strs) (vals_to_string exs)) *)
(*     ~out_str:identity *)
(*     ~res_str:Expr.to_string *)
(*     "symb_solver" *)
(*     [ *)
(*       ("(lambda (x:num y:num):num (+ (+ x y) z))", [], [[`Num 1; `Num 2], `Num 3]), *)
(*       "(+ (+ x y) 0)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ x y) z))", [ "(< z 1)" ], [[`Num 1; `Num 2], `Num 3]), *)
(*       "(+ (+ x y) 0)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ x y) z))", [ "(< z 1)" ], [[`Num 6; `Num 7], `Num 8]), *)
(*       "(+ (+ x y) -5)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ x y) z))", [ "(< z 1)"; "(> z (- 0 1))" ], [[`Num 1; `Num 2], `Num 3]), *)
(*       "(+ (+ x y) 0)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ (+ x y) z1) z2))", [ "(< z1 2)"; "(<z2 2)" ], [[`Num 1; `Num 2], `Num 3]), *)
(*       "(+ (+ (+ x y) 0) 0)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ (+ x y) z1) z2))", [ "(< z1 (- 0 2))"; "(> z2 2)" ], [[`Num 1; `Num 2], `Num 3]), *)
(*       "(+ (+ (+ x y) -3) 3)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ x y) z))", [ "(< (f 1 2) 4)" ], [[`Num 1; `Num 2], `Num 3]), *)
(*       "(+ (+ x y) 0)"; *)
(*       ("(lambda (x:num y:num):num (+ (+ (\* x z1) z2) y))", [ "(< (f 2 3) 4)"; "(< 0 z2)"], [[`Num 1; `Num 2], `Num 0]), *)
(*       "(+ (+ (\* x -3) 1) y)"; *)
(*     ] *)

let () = run_test_tt_main
    ("all-tests" >:::
     [
       Eval_tests.tests;
       Unify_tests.tests;
       Collections_tests.tests;
       Type_tests.tests;
       Improved_search_tests.tests;
       Hypothesis_tests.tests;
       Component_tests.tests;
       Conflict_tests.tests;
       
       test_parse_expr;
       test_parse_typ;
       test_parse_example;

       test_eval;
       (* test_unify; *)
       (* test_signature; *)

       (* test_expand; *)
       (* test_expr_to_z3; *)
       (* test_verify; *)

       test_partition;
       test_m_partition;

       test_fold_constants;
       (* test_rewrite; *)
       (* test_normalize; *)
       (* test_denormalize; *)

       (* test_sat_solver; *)
       (* test_symb_solver; *)
     ]);
