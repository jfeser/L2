open Core
open OUnit2
open L2
open Tests_common
open Collections

let identity (x : 'a) : 'a = x

let cmp_partition a b =
  let sort_partition p = List.sort ~compare:Int.compare p in
  let sort_partition_list l =
    List.map ~f:sort_partition l |> List.sort ~compare:(List.compare Int.compare)
  in
  sort_partition_list a = sort_partition_list b

let m_expr_to_string = function Some e -> Expr.to_string e | None -> "None"

let test_eval =
  let open Eval in
  let open Collections.Tree in
  make_tests
    ~in_f:(fun str -> str |> Expr.of_string_exn |> eval (Ctx.empty ()))
    ~out_f:identity ~in_str:identity ~out_str:Value.to_string
    ~res_str:Value.to_string "eval"
    [ ("1", `Num 1)
    ; ("#t", `Bool true)
    ; ("#f", `Bool false)
    ; ("[1]", `List [`Num 1])
    ; ("(+ 1 2)", `Num 3)
    ; ("(- 1 2)", `Num (-1))
    ; ("(* 1 2)", `Num 2)
    ; ("(/ 4 2)", `Num 2)
    ; ("(% 4 2)", `Num 0)
    ; ("(= 4 2)", `Bool false)
    ; ("(= 4 4)", `Bool true)
    ; ("(> 4 2)", `Bool true)
    ; ("(> 4 4)", `Bool false)
    ; ("(>= 4 2)", `Bool true)
    ; ("(>= 4 4)", `Bool true)
    ; ("(>= 4 5)", `Bool false)
    ; ("(cons 4 [])", `List [`Num 4])
    ; ("(cons 4 [1])", `List [`Num 4; `Num 1])
    ; ("(car [1])", `Num 1)
    ; ("(cdr [1 2])", `List [`Num 2])
    ; ("(if #t 1 2)", `Num 1)
    ; ("(if #f 1 2)", `Num 2)
    ; ("(let a 1 (+ 1 a))", `Num 2)
    ; ("(let a 5 (let b 2 (* a b)))", `Num 10)
    ; ("(let a 5 (let a 2 (+ a 1)))", `Num 3)
    ; ("(let a (* 3 4) (+ a 1))", `Num 13)
    ; ("(let f (lambda (x) (+ 1 x)) (f 1))", `Num 2)
    ; ("(let f (lambda (x y) (+ y x)) (f 1 2))", `Num 3)
    ; ("(let f (lambda (x) (lambda (y) (+ x y))) ((f 1) 2))", `Num 3)
    ; ("(let f (lambda (x) (+ x 1)) (let g (lambda (x) (+ 1 x)) (f (g 1))))", `Num 3)
    ; ("(let f (lambda (x) (if (= x 0) 0 (f (- x 1)))) (f 0))", `Num 0)
    ; ("(let f (lambda (x) (if (= x 0) 0 (f (- x 1)))) (f 5))", `Num 0)
    ; ("(foldr [1 2 3] (lambda (a e) (+ a e)) 0)", `Num 6)
    ; (* Sum *)
      ( "(foldr [[1] [2 1] [3 2 1]] (lambda (a e) (cons (car e) a)) [])"
      , `List [`Num 1; `Num 2; `Num 3] )
    ; (* Firsts *)
      ("(foldl [1 2 3] (lambda (a e) (+ a e)) 0)", `Num 6)
    ; (* Sum *)
      ( "(foldl [[1] [2 1] [3 2 1]] (lambda (a e) (cons (car e) a)) [])"
      , `List [`Num 3; `Num 2; `Num 1] )
    ; (* Rev-firsts *)
      ("(filter [] (lambda (e) (> 3 e)))", `List [])
    ; ("(filter [1 2 3 4] (lambda (e) (> 3 e)))", `List [`Num 1; `Num 2])
    ; ("(filter [1 2 3 4] (lambda (e) (= 0 (% e 2))))", `List [`Num 2; `Num 4])
    ; ("(map [] (lambda (e) (+ e 1)))", `List [])
    ; ("(map [1] (lambda (e) (+ e 1)))", `List [`Num 2])
    ; ("(map [1 2] (lambda (e) (+ e 1)))", `List [`Num 2; `Num 3])
    ; ( "(map [0 1 0] (lambda (e) (= e 0)))"
      , `List [`Bool true; `Bool false; `Bool true] )
    ; ("{}", `Tree Empty)
    ; ("(tree 1 [])", `Tree (Node (`Num 1, [])))
    ; ("(tree 1 [(tree 1 [])])", `Tree (Node (`Num 1, [Node (`Num 1, [])])))
    ; ("(value (tree 1 [(tree 1 [])]))", `Num 1)
    ; ("(value (tree 1 []))", `Num 1)
    ; ("(mapt (tree 1 []) (lambda (e) (+ e 1)))", `Tree (Node (`Num 2, [])))
    ; ( "(mapt (tree 1 [(tree 1 [])]) (lambda (e) (+ e 1)))"
      , `Tree (Node (`Num 2, [Node (`Num 2, [])])) )
    ; ( "(mapt {1 {1}} (lambda (e) (+ e 1)))"
      , `Tree (Node (`Num 2, [Node (`Num 2, [])])) )
    ; ( "(let max (lambda (x) (foldl x (lambda (a e) (if (> e a) e a)) 0)) (max [1 \
         2 3]))"
      , `Num 3 )
    ; ( "(let max (lambda (x) (foldl x (lambda (a e) (if (> e a) e a)) 0)) (max [0 \
         1 5 9]))"
      , `Num 9 )
    ; ( "(let max (lambda (x) (foldl x (lambda (a e) (if (> e a) e a)) 0)) (let \
         dropmax (lambda (y) (filter y (lambda (z) (< z (max y))))) (dropmax [1 5 \
         0 9])))"
      , `List [`Num 1; `Num 5; `Num 0] )
    ; ( "(let member (lambda (l x) (foldl l (lambda (a e ) (| (= e x) a)) #f)) \
         (member [] 0))"
      , `Bool false )
    ; ( "(let member (lambda (l x) (foldl l (lambda (a e ) (| (= e x) a)) #f)) \
         (member [0] 0))"
      , `Bool true )
    ; ( "(let member (lambda (l x) (foldl l (lambda (a e ) (| (= e x) a)) #f)) \
         (member [0 1 ] 0))"
      , `Bool true )
    ; ( "(let count (lambda (l x) (foldl l (lambda (a e) (if (= e x) (+ a 1) a)) \
         0)) (count [1 2 3 4 4] 4))"
      , `Num 2 )
    ; ( "(let last (lambda (a) (foldl a (lambda (c b) b) 0))\n\
        \                 (let shiftr (lambda (a) (foldr a (lambda (c b) (foldl c \
         (lambda (e d) (cons (last a) (cons b (cdr c)))) [1])) [])) (shiftr [6 5 3 \
         7 8])))"
      , `List [`Num 8; `Num 6; `Num 5; `Num 3; `Num 7] )
    ; ( "(let last (lambda (a) (foldl a (lambda (c b) b) 0))\n\
        \                 (let shiftr (lambda (a) (foldr a (lambda (c b) (foldl c \
         (lambda (e d) (cons (last a) (cons b (cdr c)))) [1])) [])) (shiftr [4 0 \
         5])))"
      , `List [`Num 5; `Num 4; `Num 0] ) ]

let test_fold_constants =
  make_tests
    ~in_f:(fun str -> str |> Expr.of_string_exn |> Rewrite.fold_constants)
    ~out_f:(fun str -> Some (Expr.of_string_exn str))
    ~in_str:identity ~out_str:identity ~res_str:m_expr_to_string "fold_constants"
    [ ("1", "1")
    ; ("#f", "#f")
    ; ("[]", "[]")
    ; ("[1 2]", "[1 2]")
    ; ("(+ 1 2)", "3")
    ; ("(+ (* 0 5) (/ 4 2))", "2")
    ; ("(+ a (- 4 3))", "(+ a 1)")
    ; ("(lambda (x) (+ x (* 1 5)))", "(lambda (x) (+ x 5))")
    ; ("(lambda (x) (+ 1 (* 1 5)))", "6") ]

let partition_to_string = List.to_string ~f:(List.to_string ~f:Int.to_string)

let test_partition =
  make_tests ~in_f:Util.partition ~out_f:identity ~in_str:Int.to_string
    ~out_str:partition_to_string ~res_str:partition_to_string ~cmp:cmp_partition
    "test_partition"
    [(0, []); (1, [[1]]); (2, [[2]; [1; 1]]); (3, [[3]; [1; 2]; [1; 1; 1]])]

let test_m_partition =
  "test_m_partition"
  >::: List.map
         ~f:(fun (n, m, p) ->
           let title =
             Printf.sprintf "%s -> %s" (Int.to_string n) (partition_to_string p)
           in
           title
           >:: fun _ -> assert_equal ~cmp:cmp_partition (Util.m_partition n m) p )
         [(3, 1, [[3]]); (3, 2, [[1; 2]]); (3, 3, [[1; 1; 1]])]

let () =
  run_test_tt_main
    ( "all-tests"
    >::: [ (* Eval_tests.tests; *)
           Unify_tests.tests
         ; Collections_tests.tests
         ; Type_tests.tests
         ; V2_engine_tests.tests
         ; Hypothesis_tests.tests
         ; Sexp_parser_tests.tests
         ; (* Component_tests.tests; *)
           (* Automaton_tests.tests; *)
           
           (* test_parse_expr; *)
           (* test_parse_typ; *)
           (* test_parse_example; *)
           
           (* test_eval; *)
           (* test_unify; *)
           (* test_signature; *)
           
           (* test_expand; *)
           (* test_expr_to_z3; *)
           (* test_verify; *)
           test_partition
         ; test_m_partition
         ; test_fold_constants
         (* test_rewrite; *)
         (* test_normalize; *)
         (* test_denormalize; *)
         
         (* test_sat_solver; *)
         (* test_symb_solver; *)
          ] )
