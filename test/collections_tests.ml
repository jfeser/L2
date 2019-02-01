open Core
open OUnit2
open L2
open Collections

let tree_max_tests =
  let module T = Tree in
  "tree-max-tests"
  >::: List.map
         ~f:(fun (input, output) ->
           test_case (fun _ -> assert_equal (Tree.max ~cmp:Int.compare input) output)
           )
         [ (T.Empty, None)
         ; (T.Node (0, []), Some 0)
         ; (T.Node (0, [T.Node (1, []); T.Node (0, [])]), Some 1)
         ; (T.Node (1, [T.Node (0, []); T.Node (0, [])]), Some 1)
         ; (T.Node (1, [T.Node (0, []); T.Node (2, [])]), Some 2) ]

let tree_size_tests =
  let module T = Tree in
  "tree-size-tests"
  >::: List.map
         ~f:(fun (input, output) ->
           test_case (fun _ -> assert_equal (Tree.size input) output) )
         [ (T.Empty, 1)
         ; (T.Node (0, []), 1)
         ; (T.Node (0, [T.Node (1, []); T.Node (0, [])]), 3) ]

let tree_map_tests =
  let module T = Tree in
  "tree-map-tests"
  >::: List.map
         ~f:(fun (tree, f, output) ->
           test_case (fun _ -> assert_equal (Tree.map tree ~f) output) )
         [ (T.Empty, (fun x -> x), T.Empty)
         ; (T.Node (0, []), (fun x -> x), T.Node (0, []))
         ; (T.Node (0, []), (fun x -> x + 1), T.Node (1, []))
         ; ( T.Node (0, [T.Node (1, []); T.Node (0, [])])
           , (fun x -> x + 1)
           , T.Node (1, [T.Node (2, []); T.Node (1, [])]) ) ]

let tree_tests = "tree-tests" >::: [tree_max_tests; tree_size_tests; tree_map_tests]

let tests = "collections-tests" >::: [tree_tests]
