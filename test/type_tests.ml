open Core
open OUnit2
open L2
open Tests_common
open Collections
open Infer

let unifier_of_types_tests =
  let open Type in
  mk_equality_tests
    ~printer:(fun u -> Sexp.to_string_hum (Option.sexp_of_t Unifier.sexp_of_t u))
    ~cmp:(Option.equal Unifier.equal) "unifier-of_types-tests"
    (fun (t1, t2) -> Unifier.of_types t1 t2)
    [ ((num, num), Some Unifier.empty)
    ; ((bool, num), None)
    ; ((list (free 0 0), num), None)
    ; ((list (free 0 0), num), None)
    ; ((list (free 0 0), list num), Some (Unifier.of_alist_exn [(0, num)]))
    ; ((list (quant "a"), list num), None)
    ; ( (arrow1 (free 0 0) (free 1 0), arrow1 num (free 2 0))
      , Some (Unifier.of_alist_exn [(0, num); (2, free 1 0)]) )
    ; ((tree (free 0 0), tree num), Some (Unifier.of_alist_exn [(0, num)]))
    ; ((tree num, tree (free 0 0)), Some (Unifier.of_alist_exn [(0, num)]))
    ; ((list (free 0 0), list num), Some (Unifier.of_alist_exn [(0, num)]))
    ; ((list num, list (free 0 0)), Some (Unifier.of_alist_exn [(0, num)])) ]

let unifier_tests = "unifier-tests" >::: [unifier_of_types_tests]

let infer_typeof_tests =
  let cases =
    [ ("1", "num")
    ; ("#t", "bool")
    ; ("#f", "bool")
    ; ("[]", "list[a]")
    ; ("[1 2 3]", "list[num]")
    ; ("(+ 1 2)", "num")
    ; ("(< 1 2)", "bool")
    ; ("(cons 1 [])", "list[num]")
    ; ("(cons 1 [1 2 3])", "list[num]")
    ; ("(car [1 2 3])", "num")
    ; ("(cdr [1 2 3])", "list[num]")
    ; ("(car (cdr [1 2 3]))", "num")
    ; ("(let f (lambda (x) (+ 1 x)) f)", "num -> num")
    ; ("(let f (lambda (x y) (+ x y)) f)", "(num, num) -> num")
    ; ("(let g (lambda (x y f) (+ x (f y))) g)", "(num, a, (a -> num)) -> num")
    ; ("(lambda (x y f) (+ x (f y)))", "(num, a, (a -> num)) -> num")
    ; ( "(let g (lambda (x y) (lambda (f) (f x y))) g)"
      , "(a, b) -> (((a, b) -> c) -> c)" )
    ; ("(let f (lambda (x) (cons x [])) f)", "t1 -> list[t1]")
    ; ("(map [] (lambda (x) (+ x 1)))", "list[num]")
    ; ("(map [1 2 3] (lambda (x) (+ x 1)))", "list[num]")
    ; ("(let f (lambda (x y) (+ x y)) (f 1 2))", "num")
    ; ("(let f (lambda (x) (+ x 1)) (f 1))", "num")
    ; ("(let f (lambda (x) (+ x 1)) (f 1))", "num")
    ; ("(lambda (x) (let y x y))", "t1 -> t1")
    ; ("(lambda (x) (let y (lambda (z) z) y))", "t0 -> (t1 -> t1)")
    ; ("(let f (lambda (x) x) (let id (lambda (y) y) (= f id)))", "bool")
    ; ("(let apply (lambda (f x) (f x)) apply)", "((a -> b), a) -> b")
    ; ( "(lambda (f) (let x (lambda (g y) (let z (g y) (= f g))) x))"
      , "(a -> b) -> (((a -> b), a) -> bool)" )
    ; ( "(lambda (f) (let x (lambda (g) (let z (g 1) (= f g))) x))"
      , "(num -> b) -> ((num -> b) -> bool)" )
    ; ( "(lambda (f) (lambda (g) (let z (g 1) (= f g))))"
      , "(num -> b) -> ((num -> b) -> bool)" )
    ; ("(lambda (f) (let x (lambda (g) (= f g)) x))", "a -> (a -> bool)")
    ; ("(lambda (f g) (let z (g 1) (= f g)))", "((num -> a), (num -> a)) -> bool")
    ; ("(lambda (l x) (= [x] l))", "(list[a], a) -> bool")
    ; ("(let a 0 (let b 1 (lambda (x) (cons a [b]))))", "a -> list[num]")
    ; ("(lambda (y) (if (= 0 y) 0 1))", "num -> num")
    ; ("(lambda (y) (= y 1))", "num -> bool")
    ; ("{}", "tree[a]")
    ; ("{1}", "tree[num]")
    ; ("{1 {2}}", "tree[num]")
    ; ("(value {1})", "num")
    ; ("(children {1 {2} {3}})", "list[tree[num]]") ]
    |> List.map ~f:(fun (input_s, output_s) ->
           (Expr.of_string_exn input_s, Type.normalize (Type.of_string_exn output_s))
       )
  in
  mk_equality_tests
    ~printer:(fun t -> Sexp.to_string (Type.sexp_of_t t))
    ~cmp:Type.equal "infer-typeof-tests"
    (fun input ->
      let t, _ = Type.of_expr input in
      t )
    cases

let infer_tests = "infer-tests" >::: [ (* infer_typeof_tests; *) ]

let tests = "type-tests" >::: [unifier_tests; infer_tests]
