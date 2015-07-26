open Core.Std
open Printf

open Collections

let testcases =
  [
    "dupli", [],
    [
      "(dupli []) -> []";
      "(dupli [1]) -> [1 1]";
      "(dupli [1 2 3]) -> [1 1 2 2 3 3]";
    ], "Duplicates each element in a list.";

    "add", [],
    [
      "(add [] 1) -> []";
      "(add [1] 1) -> [2]";
      "(add [1 2] 1) -> [2 3]";
      "(add [1 2] 2) -> [3 4]";
      "(add [1 2 3 4] 5) -> [6 7 8 9]";
    ], "Adds a number to each element of a list.";

    "Reverse", [],
    [
      "(Reverse []) -> []";
      "(Reverse [0]) -> [0]";
      "(Reverse [0 1]) -> [1 0]";
      "(Reverse [0 1 2]) -> [2 1 0]"
    ], "Reverses a list.";

    "droplast", [],
    [
      "(droplast [1]) -> []";
      "(droplast [1 2 3]) -> [1 2]";
      "(droplast [1 2]) -> [1]";
      "(droplast [1 5 2 7 8]) -> [1 5 2 7]";
      "(droplast [1 1 1 1 1 1 1]) -> [1 1 1 1 1 1]";
      "(droplast [1 1 1 1 1 1]) -> [1 1 1 1 1]";
    ], "";

    "last", [],
    [
      "(last [1]) -> 1";
      "(last [1 2]) -> 2";
      "(last [1 2 3]) -> 3";
      "(last [1 3 5 8]) -> 8"
    ], "Returns the last element in a list.";

    "length", [],
    [
      "(length []) -> 0";
      "(length [0]) -> 1";
      "(length [0 0]) -> 2";
      "(length [0 0 0]) -> 3";
    ], "Returns the length of a list.";

    "max", [],
    [
      "(max []) -> 0";
      "(max [0]) -> 0";
      "(max [0 2 1]) -> 2";
      "(max [1 6 2 5]) -> 6";
      "(max [1 6 7 5]) -> 7";
      "(max [10 25 7 9 18]) -> 25";
      "(max [100 25 7 9 18]) -> 100";
    ], "Returns the largest number in a list, or zero if the list is empty.";

    "multfirst", [],
    [
      "(multfirst []) -> []";
      "(multfirst [1 0]) -> [1 1]";
      "(multfirst [0 1 0]) -> [0 0 0]";
      "(multfirst [2 0 2 3]) -> [2 2 2 2]";
    ], "Replaces every item in a list with the first item.";

    "multlast", [],
    [
      "(multlast []) -> []";
      "(multlast [1 0]) -> [0 0]";
      "(multlast [0 1 0]) -> [0 0 0]";
      "(multlast [2 0 2 3]) -> [3 3 3 3]";
    ], "Replaces every item in a list with the last item.";

    "append", [],
    [
      "(append [] 1) -> [1]";
      "(append [] 2) -> [2]";
      "(append [1 0] 2) -> [1 0 2]";
    ], "Appends an item to a list.";

    "member", [],
    [
      "(member [] 0) -> #f";
      "(member [0] 0) -> #t";
      "(member [0] 1) -> #f";
      "(member [0 1 0] 0) -> #t";
      "(member [0 1 0] 1) -> #t";
      "(member [1 6 2 5] 2) -> #t";
      "(member [5 6 2] 6) -> #t";
      "(member [2 5 6] 6) -> #t";
      "(member [1 2 5] 3) -> #f";
    ], "Checks whether an item is a member of a list.";

    "concat", [],
    [
      "(concat [] []) -> []";
      "(concat [0] []) -> [0]";
      "(concat [] [0]) -> [0]";
      "(concat [1 0] [0]) -> [1 0 0]";
      "(concat [1 0 2] [3 4]) -> [1 0 2 3 4]";
    ], "Appends a list to the end of another list.";

    "sum", [],
    [
      "(sum []) -> 0";
      "(sum [1]) -> 1";
      "(sum [1 3 5]) -> 9";
      "(sum [1 5]) -> 6";
    ], "Returns the sum of a list.";

    "incrs", [],
    [
      "(incrs []) -> []";
      "(incrs [[1]]) -> [[2]]";
      "(incrs [[1] [2]]) -> [[2] [3]]";
      "(incrs [[1 2] [3 4]]) -> [[2 3] [4 5]]";
    ], "For each list in a list of lists, increments each number in the list by one.";

    "sums", [],
    [
      "(sums []) -> []";
      "(sums [[]]) -> [0]";
      "(sums [[1] []]) -> [1 0]";
      "(sums [[1 2] [3 4]]) -> [3 7]";
    ], "For list in a list of lists, sums the list.";

    "join", [],
    [
      "(join []) -> []";
      "(join [[] [1 0]]) -> [1 0]";
      "(join [[1 0] []]) -> [1 0]";
      "(join [[1 0] [2 3] [6] [4 5]]) -> [1 0 2 3 6 4 5]";
    ], "Concatenates together a list of lists.";

    "incrt", [],
    [
      "(incrt {}) -> {}";
      "(incrt {1}) -> {2}";
      "(incrt {1 {2}}) -> {2 {3}}";
    ], "Increments the value of each node in a tree by one.";

    "sumt", [],
    [
      "(sumt {}) -> 0";
      "(sumt {1}) -> 1";
      "(sumt {1 {2} {3}}) -> 6";
    ], "Sums the nodes of a tree.";

    "leaves", [
      "join", "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))";
    ], [
      "(leaves {}) -> []";
      "(leaves {1}) -> [1]";
      "(leaves {1 {2} {3}}) -> [2 3]";
      "(leaves {1 {2} {3 {4}}}) -> [2 4]";
      "(leaves {1 {2 {1} {5}} {3 {4}}}) -> [1 5 4]";
    ], "Returns a list of the leaves of a tree.";

    "count_leaves", [
      "sum", "(lambda (a) (foldl a (lambda (c b) (+ c b)) 0))";
    ], [
      "(count_leaves {}) -> 0";
      "(count_leaves {5}) -> 1";
      "(count_leaves {3 {2}}) -> 1";
      "(count_leaves {3 {2} {5}}) -> 2";
      "(count_leaves {3 {2 {3}} {5}}) -> 2";
      "(count_leaves {3 {2 {3} {5}} {5 {5}}}) -> 3";
      "(count_leaves {3 {2 {3} {5}} {5 {5} {4}}}) -> 4";
      "(count_leaves {5 {5 {5 {5 {5 {5 {5 {5}}}}}}}}) -> 1";
    ], "Counts the number of leaves in a tree.";

    "membert", [],
    [
      "(membert {} 1) -> #f";
      "(membert {1} 1) -> #t";
      "(membert {0 {5} {6} {6}} 6) -> #t";
      "(membert {0 {5 {7} {1} {1}} {6} {8}} 3) -> #f";
      "(membert {0 {5 {7} {1} {3}} {6} {8}} 9) -> #f";
      "(membert {0 {5 {7} {1} {3}} {6} {8}} 7) -> #t";
      "(membert {0 {5 {7} {1} {3}} {6} {8}} 8) -> #t";
      "(membert {0 {5 {7} {1} {3}} {6} {8}} 0) -> #t";
      "(membert {12 {5 {7} {1} {3}} {6} {8}} 0) -> #f";
      "(membert {1 {3 {5 {7 {9}}}}} 9) -> #t";
      "(membert {1 {3 {5 {7 {9 {1} {2} {4} {6} {8}}}}}} 8) -> #t";
      "(membert {1 {3 {5 {7 {9 {1} {2} {4} {6} {8}}}}}} 12) -> #f";
    ], "Checks whether an element is contained in a tree.";

    "maxt", [],
    [
      "(maxt {}) -> 0";
      "(maxt {1}) -> 1";
      "(maxt {5 {2} {3}}) -> 5";
      "(maxt {5 {2} {6}}) -> 6";
      "(maxt {5 {2 {0} {7} {4}} {6}}) -> 7";
      "(maxt {5 {2 {0} {7} {4}} {8}}) -> 8";
    ], "Returns the maximum element in a tree.";

    "flatten", [
      "join", "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))";
    ], [
      "(flatten {}) -> []";
      "(flatten {1}) -> [1]";
      "(flatten {1 {2} {3}}) -> [1 2 3]";
    ], "Flattens a tree into a list. Requires the specification of $join$.";

    "height", [
      "max", "(lambda (a) (foldl a (lambda (c b) (if (< c b) b c)) 0))";
    ], [
      "(height {}) -> 0";
      "(height {1}) -> 1";
      "(height {100 {100} {100}}) -> 2";
      "(height {100 {100} {100 {100 {100}}}}) -> 4";
      "(height {100 {100 {100 {100 {100}}}} {100}}) -> 5";
      "(height {90 {6 {5} {6} {8}} {7} {9} {5}}) -> 3";
    ], "Returns the height of a tree. Requires the specification of $max$.";

    "prependt", [],
    [
      "(prependt {[]} 1) -> {[1]}";
      "(prependt {[]} 2) -> {[2]}";
      "(prependt {[1 2 3]} 1) -> {[1 1 2 3]}";
      "(prependt {[1 2 3] {[3 4]}} 1) -> {[1 1 2 3] {[1 3 4]}}";
      "(prependt {[1 2 3] {[3 4]} {[5 6]}} 7) -> {[7 1 2 3] {[7 3 4]} {[7 5 6]}}";
    ], "";

    "appendt", [],
    [
      "(appendt {[]} 1) -> {[1]}";
      "(appendt {[]} 2) -> {[2]}";
      "(appendt {[1 2 3]} 1) -> {[1 2 3 1]}";
      "(appendt {[1 2 3] {[3 4]}} 1) -> {[1 2 3 1] {[3 4 1]}}";
      "(appendt {[1 2 3] {[3 4]} {[5 6]}} 7) -> {[1 2 3 7] {[3 4 7]} {[5 6 7]}}";
    ], "";

    "replacet", [],
    [
      "(replacet {[]} 1 2) -> {[]}";
      "(replacet {[1]} 1 2) -> {[2]}";
      "(replacet {[1 3 4]} 1 2) -> {[2 3 4]}";
      "(replacet {[1 3 4] {[4 5 6]}} 4 7) -> {[1 3 7] {[7 5 6]}}";
    ], "";

    "sumnodes", [],
    [
      "(sumnodes {}) -> {}";
      "(sumnodes {[]}) -> {0}";
      "(sumnodes {[1]}) -> {1}";
      "(sumnodes {[1] {[1 2 3]} {[4 8]}}) -> {1 {6} {12}}";
    ], "";

    "flattenl", [
      "join", "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))";
    ], [
      "(flattenl {}) -> []";
      "(flattenl {[1]}) -> [1]";
      "(flattenl {[1] {[2]} {[3]}}) -> [1 2 3]";
      "(flattenl {[1 1 1] {[2]} {[3]}}) -> [1 1 1 2 3]";
      "(flattenl {[1 1 1] {[2 5 7]} {[3]}}) -> [1 1 1 2 5 7 3]";
    ], "Flattens a tree of lists into a list. Requires the specification of $join$.";

    "sumtrees", [],
    [
      "(sumtrees []) -> []";
      "(sumtrees [{} {1 {2} {3}}]) -> [0 6]";
      "(sumtrees [{5 {6}} {1}]) -> [11 1]";
    ], "";

    "dropmax", [
      (* "max", "(lambda (a) (foldl a (lambda (c b) (if (< c b) b c)) 0))"; *)
    ], [
      "(dropmax [3 5 2]) -> [3 2]";
      "(dropmax [3 1 2]) -> [1 2]";
      "(dropmax [1 5 2]) -> [1 2]";
    ], "Removes the largest number in a list. Requires the specification of $max$.";

    "shiftl", [
      "reverse", "(lambda (a) (foldl a (lambda (c b) (cons b c)) []))";
    ], [
      "(shiftl []) -> []";
      "(shiftl [1]) -> [1]";
      "(shiftl [1 2]) -> [2 1]";
      "(shiftl [5 2 3]) -> [2 3 5]";
      "(shiftl [1 2 3 4]) -> [2 3 4 1]";
    ], "Shift all items in a list to the left. Requires the specification of $append$.";

    "shiftr", [
      "reverse", "(lambda (a) (foldl a (lambda (c b) (cons b c)) []))";
    ], [
      "(shiftr []) -> []";
      "(shiftr [1]) -> [1]";
      "(shiftr [1 2]) -> [2 1]";
      "(shiftr [0 2 3]) -> [3 0 2]";
      "(shiftr [1 2 3 4]) -> [4 1 2 3]";
      "(shiftr [2 9 7 4]) -> [4 2 9 7]";
    ], "Shift all items in a list to the right. Requires the specification of $last$.";

    "Dedup", [
      "member", "(lambda (b a) (foldl b (lambda (d c) (| d (= a c))) #f))";
    ], [
      "(Dedup []) -> []";
      "(Dedup [1]) -> [1]";
      "(Dedup [1 2 5]) -> [1 2 5]";
      "(Dedup [1 2 5 2]) -> [1 5 2]";
      "(Dedup [1 1 1 2 5 2]) -> [1 5 2]";
      "(Dedup [3 3 3 5 5 5]) -> [3 5]";
      "(Dedup [1 2 3 2 1]) -> [3 2 1]";
    ], "Removes duplicate elements from a list. Requires the specification of $member$.";

    "searchnodes", [
      "member", "(lambda (b a) (foldl b (lambda (d c) (| d (= a c))) #f))";
    ], [
      "(searchnodes {} 1) -> #f";
      "(searchnodes {[3 2] {[4 1]}} 2) -> #t";
      "(searchnodes {[3 2] {[4 1]}} 8) -> #f";
      "(searchnodes {[3 4] {[5]} {[6 4]}} 6) -> #t";
      "(searchnodes {[1 3] {[5]} {[2 3]}} 3) -> #t";
      "(searchnodes {[1 3] {[5]} {[2 3]}} 4) -> #f";
    ], "";

    "selectnodes", [
      "join", "(lambda (a) (foldl a (lambda (c b) (foldr c (lambda (e d) (cons d e)) b)) []))";
      "pred", "(lambda (a) (= 0 (% a 2)))";
    ], [
      "(selectnodes {}) -> []";
      "(selectnodes {1 {10} {25}}) -> [10]";
      "(selectnodes {1 {10} {20}}) -> [10 20]";
      "(selectnodes {30 {15} {25}}) -> [30]";
    ], "";

    "dropmins", [
      "min", "(lambda (a) (foldl a (lambda (c b) (if (< c b) c b)) inf))";
    ], [
      "(dropmins []) -> []";
      "(dropmins [[1]]) -> [[]]";
      "(dropmins [[1 3 5] [5 3 2]]) -> [[3 5] [5 3]]";
      "(dropmins [[8 4 7 2] [4 6 2 9] [3 4 1 0]]) -> [[8 4 7] [4 6 9] [3 4 1]]";
    ], "";

    "cprod", [],
    [
      "(f []) -> [[]]";
      "(f [[]]) -> []";
      "(f [[] []]) -> []";
      "(f [[1 2 3] [4] [5 6]]) -> [[1 4 5] [1 4 6] [2 4 5] [2 4 6] [3 4 5] [3 4 6]]";
    ], "";

    "tconcat", [],
    [
      "(tconcat {1} {2 {3} {4}}) -> {1 {2 {3} {4}}}";
      "(tconcat {1 {2} {3}} {2 {3} {4}}) -> {1 {2 {2 {3} {4}}} {3 {2 {3} {4}}}}";
      "(tconcat {1 {2} {3 {4}}} {2 {3}}) -> {1 {2 {2 {3}}} {3 {4 {2 {3}}}}}";
    ], "";

    "count_nodes", [],
    [
      "(count_nodes {}) -> 0";
      "(count_nodes {2}) -> 1";
      "(count_nodes {2 {3} {4}}) -> 3";
      "(count_nodes {2 {3 {0}} {4 {9} {8}}}) -> 6";
    ], "";

    "largest_n", [],
    [
      "(largest_n 3 [[1 2 3] [3 4] [3 2 7]]) -> [7 4 3]";
      "(largest_n 2 [[1 2 3] [3 7] [3 2 7]]) -> [7 7]";
      "(largest_n 1 [[1 2 3] [3 4] [3 2 7]]) -> [7]";
    ], "";

    "evens", [],
    [
      "(evens []) -> []";
      "(evens [1]) -> []";
      "(evens [1 2]) -> [2]";
      "(evens [1 2 3 4]) -> [2 4]";
      "(evens [5 6 3 9 8 4]) -> [6 8 4]";
    ], "Filters out the odd numbers in a list, leaving the even numbers.";

    "intersect", [],
    [
      "(intersect [2 3 1] [5 3 4]) -> [3]";
      "(intersect [2 3 1] [3 5 4]) -> [3]";
      "(intersect [2 3 8] [3 5 8]) -> [3 8]";
      "(intersect [1 2 3 0] [3 1 0 9]) -> [0 1 3]";
    ], "";
  ]

(** Get a JSON object containing all captured information from a single run. *)
let get_json (testcase_name, testcase_bk, testcase_examples, testcase_desc) runtime solution config : Json.json =
  let timers = [
    "search", Search.timer;
    "deduction", Deduction.timer;
  ] in
  let counters = [
    "search", Search.counter;
    "deduction", Deduction.counter;
  ] in
  `Assoc [
    "timers", `List (List.map timers ~f:(fun (name, timer) -> `Assoc [name, Timer.to_json timer]));
    "counters", `List (List.map counters ~f:(fun (name, counter) -> `Assoc [name, Counter.to_json counter]));
    "testcase", `Assoc [
      "name", `String testcase_name;
      "background", `List (List.map ~f:(fun n -> `String n) testcase_bk);
      "examples", `List (List.map ~f:(fun n -> `String n) testcase_examples);
      "description", `String testcase_desc;
    ];
    "solution", `String solution;
    "runtime", `Float runtime;
    "config", `String (Config.to_string config);
  ]  

let time_solve config (_, bk_strs, example_strs, _) : (Expr.t list * Time.Span.t) =
  let bk = List.map bk_strs ~f:(fun (name, impl) -> name, Expr.of_string impl) in
  let examples = List.map example_strs ~f:Example.of_string in

  (* Attempt to synthesize from specification. *)
  Util.with_runtime (fun () ->
      let solutions = Search.solve ~init:Search.extended_init ~config ~bk examples in
      Ctx.to_alist solutions
      |> List.map ~f:(fun (name, lambda) ->
          `Let (name, Expr.normalize lambda, `Id "_")))

let command =
  let spec =
    let open Command.Spec in
    empty
    +> flag "-c" ~aliases:["--config"] (optional string) ~doc:" read configuration from file"
    +> flag "-f" ~aliases:["--input"] (optional string) ~doc:" read specification from file"
    +> flag "-d" ~aliases:["--debug"] (optional string)
      ~doc:" write debugging information to file in JSON format"
    +> flag "-s" ~aliases:["--stdin"] no_arg ~doc:" read specification from standard input"
    +> flag "-v" ~aliases:["--verbose"] no_arg ~doc:" print progress messages while searching"
    +> flag "-V" ~aliases:["--very-verbose"] no_arg ~doc:" print many progress messages while searching"
    +> flag "-z" ~aliases:["--use-z3"] no_arg ~doc:" use Z3 for pruning"
    +> anon ("testcase" %: string)
  in

  Command.basic
    ~summary:"Run test cases and print timing results"
    spec
    (fun config_file spec_file json_file use_stdin verbose very_verbose use_solver testcase_name () ->
       let config =
         let open Config in
         (* Either load the initial config from a file or use the default config. *)
         let initial_config = 
           match config_file with
           | Some file -> In_channel.read_all file |> of_string
           | None -> default
         in
         (* Apply any changes from command line flags. *)
         {
           initial_config with
           verbosity =
             if verbose || very_verbose then
               if very_verbose then 2 else 1
             else 0;
           use_solver;
         }
       in

       let spec =
         if use_stdin then
           let input_lines = In_channel.input_all stdin |> String.split_lines in
           let bk_strs, example_strs =
             match List.findi ~f:(fun _ line -> line = "") input_lines with
             | Some (sep_index, _) ->
               List.take input_lines sep_index, List.drop input_lines (sep_index + 1)
             | None -> [], input_lines
           in
           let bk =
             List.concat_map bk_strs ~f:(fun bk_str ->
                 match Util.lsplit2_on_str bk_str ~on:" " with
                 | Some bk -> [bk]
                 | None -> begin
                     printf "Invalid background knowledge string: %s\n" bk_str;
                     exit (-1)
                   end)
           in
           ("", bk, example_strs, "")
         else
           match List.find ~f:(fun (name, _, _, _) -> name = testcase_name) testcases with
           | Some spec -> spec
           | None -> begin
               printf "No testcases with the name '%s' found." testcase_name;
               exit (-1)
             end
       in

       let (solutions, solve_time) = time_solve config spec in
       let solutions_str = List.map solutions ~f:Expr.to_string |> String.concat ~sep:"\n" in
       let solve_time_str = Time.Span.to_short_string solve_time in

       (* Print out results summary. *)
       printf "Solved %s in %s. Solutions:\n%s\n" testcase_name solve_time_str solutions_str;

       (* Write debug information to a file, if requested. *)
       match json_file with
       | Some file ->
         let (name, bk_strs, example_strs, desc) = spec in
         let bk_printable = List.map bk_strs ~f:(fun (name, lambda) -> name ^ " = " ^ lambda) in

         Json.to_file ~std:true file
           (get_json
              (name, bk_printable, example_strs, desc)
              (Time.Span.to_sec solve_time)
              solutions_str
              config)
       | None -> ())

let () = Command.run command
