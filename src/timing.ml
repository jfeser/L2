open Core.Std
open Printf

let testcases =
  [
    [
      "car",
      [
        "(mycar [0]) -> 0";
        "(mycar [1 0]) -> 1";
        "(mycar [2 1 0]) -> 2";
      ], "Returns the first element in a list.";

      "cdr",
      [
        "(mycdr [0]) -> []";
        "(mycdr [1 0]) -> [0]";
        "(mycdr [2 1 0]) -> [1 0]";
      ], "Returns a list with the first element dropped.";

      "dupli",
      [
        "(dupli []) -> []";
        "(dupli [1]) -> [1 1]";
        "(dupli [1 2 3]) -> [1 1 2 2 3 3]";
      ], "Duplicates each element in a list.";

      "incr",
      [
        "(incr []) -> []";
        "(incr [1]) -> [2]";
        "(incr [1 2]) -> [2 3]";
        "(incr [1 2 3 4]) -> [2 3 4 5]";
      ], "Increments each number in a list by one.";

      "add",
      [
        "(add [] 1) -> []";
        "(add [1] 1) -> [2]";
        "(add [1 2] 1) -> [2 3]";
        "(add [1 2] 2) -> [3 4]";
        "(add [1 2 3 4] 5) -> [6 7 8 9]";
      ], "Adds a number to each element of a list.";

      "evens",
      [
        "(evens []) -> []";
        "(evens [1]) -> []";
        "(evens [1 2]) -> [2]";
        "(evens [1 2 3 4]) -> [2 4]";
        "(evens [5 6 3 9 8 4]) -> [6 8 4]";
      ], "Filters out the odd numbers in a list, leaving the even numbers.";
      
      "reverse",
      [
        "(reverse []) -> []";
        "(reverse [0]) -> [0]";
        "(reverse [0 1]) -> [1 0]";
        "(reverse [0 1 2]) -> [2 1 0]"
      ], "Reverses a list.";

      "last",
      [
        "(last [1]) -> 1";
        "(last [1 2]) -> 2";
        "(last [1 2 3]) -> 3";
        "(last [1 3 5 8]) -> 8"
      ], "Returns the last element in a list.";

      "length",
      [
        "(length []) -> 0";
        "(length [0]) -> 1";
        "(length [0 0]) -> 2";
        "(length [0 0 0]) -> 3";
      ], "Returns the length of a list.";

      "max",
      [
        "(max []) -> 0";
        "(max [0]) -> 0";
        "(max [0 2 1]) -> 2";
        "(max [1 6 2 5]) -> 6";
        "(max [1 6 7 5]) -> 7";
        "(max [10 25 7 9 18]) -> 25";
        "(max [100 25 7 9 18]) -> 100";
      ], "Returns the largest number in a list, or zero if the list is empty.";

      "multfirst",
      [
        "(multfirst []) -> []";
        "(multfirst [1 0]) -> [1 1]";
        "(multfirst [0 1 0]) -> [0 0 0]";
        "(multfirst [2 0 2 3]) -> [2 2 2 2]";
      ], "Replaces every item in a list with the first item.";

      "multlast",
      [
        "(multlast []) -> []";
        "(multlast [1 0]) -> [0 0]";
        "(multlast [0 1 0]) -> [0 0 0]";
        "(multlast [2 0 2 3]) -> [3 3 3 3]";
      ], "Replaces every item in a list with the last item.";

      "append",
      [
        "(append [] 1) -> [1]";
        "(append [] 2) -> [2]";
        "(append [1 0] 2) -> [1 0 2]";
      ], "Appends an item to a list.";

      "member",
      [
        "(member [] 0) -> #f";
        "(member [0] 0) -> #t";
        "(member [0] 1) -> #f";
        "(member [0 1 0] 0) -> #t";
        "(member [0 1 0] 1) -> #t";
        "(member [1 6 2 5] 2) -> #t";
        "(member [5 6 2] 6) -> #t";
        "(member [1 2 5] 3) -> #f";
      ], "Checks whether an item is a member of a list.";

      "incrs",
      [
        "(incrs []) -> []";
        "(incrs [[1]]) -> [[2]]";
        "(incrs [[1] [2]]) -> [[2] [3]]";
        "(incrs [[1 2] [3 4]]) -> [[2 3] [4 5]]";
      ], "For each list in a list of lists, increments each number in the list by one.";

      "zeroes",
      [
        "(zeroes []) -> []";
        "(zeroes [0]) -> []";
        "(zeroes [1 0]) -> [1]";
        "(zeroes [1 0 2]) -> [1 2]";
      ], "Filters out the zeroes in a list.";

      "concat",
      [
        "(concat [] []) -> []";
        "(concat [0] []) -> [0]";
        "(concat [1 0] [0]) -> [1 0 0]";
        "(concat [1 0 2] [3 4]) -> [1 0 2 3 4]";
      ], "Appends a list to the end of another list.";

      "sums",
      [
        "(sums []) -> []";
        "(sums [[]]) -> [0]";
        "(sums [[1] []]) -> [1 0]";
        "(sums [[1 2] [3 4]]) -> [3 7]";
      ], "For list in a list of lists, sums the list.";

      "join",
      [
        "(join []) -> []";
        "(join [[] [1 0]]) -> [1 0]";
        "(join [[1 0] []]) -> [1 0]";
        "(join [[1 0] [2 3] [6] [4 5]]) -> [1 0 2 3 6 4 5]";
      ], "Concatenates together a list of lists.";

      "insert", 
      [
        "(insert [] 1) -> [1]";
        "(insert [] 2) -> [2]";
        "(insert [0 1] 2) -> [0 1 2]";
        "(insert [0 1] 1) -> [0 1 1]";
        "(insert [0 1] 0) -> [0 0 1]";
        "(insert [0 1 2] 0) -> [0 0 1 2]";
      ], "Inserts a number into a sorted list, maintaining the sort order.";

      "count",
      [
        "(count [] 1) -> 0";
        "(count [1 0] 1) -> 1";
        "(count [0 0 1] 0) -> 2";
        "(count [1 2 2 2 4 4 5] 2) -> 3";
        "(count [1 2 2 2 4 4 5] 4) -> 2";
        "(count [1 2 2 2 4 4 5] 5) -> 1";
      ], "Counts the number of times an element appears in a list.";

    ], "Simple list examples";

    [
      "value",
      [
        "(myvalue {1}) -> 1";
        "(myvalue {2 {} {}}) -> 2"
      ], "Returns the value at the root of a tree.";

      "incrt",
      [
        "(incrt {}) -> {}";
        "(incrt {1}) -> {2}";
        "(incrt {1 {2}}) -> {2 {3}}";
      ], "Increments the value of each node in a tree by one.";

      "sumt",
      [
        "(sumt {}) -> 0";
        "(sumt {1}) -> 1";
        "(sumt {1 {2} {3}}) -> 6";
      ], "Sums the nodes of a tree.";

      "leaves",
      [
        "(join []) -> []";
        "(join [[] [1 0]]) -> [1 0]";
        "(join [[1 0] []]) -> [1 0]";
        "(join [[1 0] [2 3] [6] [4 5]]) -> [1 0 2 3 6 4 5]";
        
        "(leaves {}) -> []";
        "(leaves {1}) -> [1]";
        "(leaves {1 {2} {3}}) -> [2 3]";
        "(leaves {1 {2} {3 {4}}}) -> [2 4]";
        "(leaves {1 {2 {1} {5}} {3 {4}}}) -> [1 5 4]";
      ], "Returns a list of the leaves of a tree.";

      "count_leaves",
      [
        "(sum []) -> 0";
        "(sum [1]) -> 1";
        "(sum [1 2 3]) -> 6";
        "(sum [1 1 1 1]) -> 4";

        "(count_leaves {}) -> 0";
        "(count_leaves {5}) -> 1";
        "(count_leaves {3 {2}}) -> 1";
        "(count_leaves {3 {2} {5}}) -> 2";
        "(count_leaves {3 {2 {3}} {5}}) -> 2";
        "(count_leaves {3 {2 {3} {5}} {5 {5}}}) -> 3";
        "(count_leaves {3 {2 {3} {5}} {5 {5} {4}}}) -> 4";
        "(count_leaves {5 {5 {5 {5 {5 {5 {5 {5}}}}}}}}) -> 1";
      ], "Counts the number of leaves in a tree.";

      "membert",
      [
        "(membert {} 1) -> #f";
        "(membert {1} 1) -> #t";
        "(membert {0 {5} {6} {8}} 6) -> #t";
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
    ], "Simple tree examples";

    [
      "flatten",
      [
        "(join []) -> []";
        "(join [[] [1 0]]) -> [1 0]";
        "(join [[1 0] []]) -> [1 0]";
        "(join [[1 0] [2 3] [6] [4 5]]) -> [1 0 2 3 6 4 5]";

        "(flatten {}) -> []";
        "(flatten {1}) -> [1]";
        "(flatten {1 {2} {3}}) -> [1 2 3]";
      ], "Flattens a tree into a list. Requires the specification of $join$.";

      "height",
      [
        "(max []) -> 0";
        "(max [0]) -> 0";
        "(max [0 2 1]) -> 2";
        "(max [1 6 2 5]) -> 6";
        "(max [1 6 7 5]) -> 7";
        "(max [10 25 7 9 18]) -> 25";
        "(max [100 25 7 9 18]) -> 100";

        "(height {}) -> 0";
        "(height {1}) -> 1";
        "(height {100 {100} {100}}) -> 2";
        "(height {100 {100} {100 {100 {100}}}}) -> 4";
        "(height {100 {100 {100 {100 {100}}}} {100}}) -> 5";
        "(height {90 {6 {5} {6} {8}} {7} {9} {5}}) -> 3";
      ], "Returns the height of a tree. Requires the specification of $map$.";
      
      "average",
      [
        "(sum []) -> 0";
        "(sum [1]) -> 1";
        "(sum [1 2 3]) -> 6";
        "(sum [1 1 1 1]) -> 4";

        "(length []) -> 0";
        "(length [0]) -> 1";
        "(length [0 0]) -> 2";
        "(length [0 0 0]) -> 3";
        "(average [0]) -> 0";
        "(average [0 1 5]) -> 2";
        "(average [1 1 1 1]) -> 1";
        "(average [4 5 7 8]) -> 6";
      ], 
      "Returns the average of a list of numbers. Requires the specification of $length$ and $sum$ as well.";

      "dropaverage",
      [
        "(sum []) -> 0";
        "(sum [1]) -> 1";
        "(sum [1 2 3]) -> 6";
        "(sum [1 1 1 1]) -> 4";
        "(length []) -> 0";
        "(length [0]) -> 1";
        "(length [0 0]) -> 2";
        "(length [0 0 0]) -> 3";
        "(average [0]) -> 0";
        "(average [0 1 5]) -> 2";
        "(average [1 1 1 1]) -> 1";
        "(average [4 5 7 8]) -> 6";
        "(dropaverage [0 1 5]) -> [5]";
        "(dropaverage [1 1 1 1]) -> [1 1 1 1]";
        "(dropaverage [4 5 7 8]) -> [7 8]";
      ], "Removes all numbers smaller than the average of a list. Requires the specification of $sum$, $length$, and $average$.";

      "dropmax",
      [
        "(max []) -> 0";
        "(max [0]) -> 0";
        "(max [0 2 1]) -> 2";
        "(max [1 6 2 5]) -> 6";
        "(max [1 6 7 5]) -> 7";
        "(max [10 25 7 9 18]) -> 25";
        "(max [100 25 7 9 18]) -> 100";
        "(dropmax [3 5 2]) -> [3 2]";
        "(dropmax [3 1 2]) -> [1 2]";
        "(dropmax [1 5 2]) -> [1 2]";
      ], "Removes the largest number in a list. Requires the specification of $max$.";

      "shiftl",
      [
        "(append [] 1) -> [1]";
        "(append [] 2) -> [2]";
        "(append [1 0] 2) -> [1 0 2]";

        "(shiftl []) -> []";
        "(shiftl [1]) -> [1]";
        "(shiftl [1 2]) -> [2 1]";
        "(shiftl [5 2 3]) -> [2 3 5]";
        "(shiftl [1 2 3 4]) -> [2 3 4 1]";
      ], "Shift all items in a list to the left. Requires the specification of $append$.";

      "shiftr",
      [
        "(last [1]) -> 1";
        "(last [1 0]) -> 0";
        "(last [1 0 5]) -> 5";
        
        "(shiftr []) -> []";
        "(shiftr [1]) -> [1]";
        "(shiftr [1 2]) -> [2 1]";
        "(shiftr [1 2 3]) -> [3 1 2]";
        "(shiftr [1 2 3 4]) -> [4 1 2 3]";
        "(shiftr [1 9 7 4]) -> [4 1 9 7]";
      ], "Shift all items in a list to the right. Requires the specification of $last$.";
      
      "dedup",
      [
        "(member [] 0) -> #f";
        "(member [0] 0) -> #t";
        "(member [0] 1) -> #f";
        "(member [0 1 0] 0) -> #t";
        "(member [0 1 0] 1) -> #t";
        "(member [1 6 2 5] 2) -> #t";
        "(member [5 6 2] 6) -> #t";
        "(member [1 2 5] 3) -> #f";

        "(dedup []) -> []";
        "(dedup [1]) -> [1]";
        "(dedup [1 2 5]) -> [1 2 5]";
        "(dedup [1 2 5 2]) -> [1 5 2]";
        "(dedup [1 1 1 2 5 2]) -> [1 5 2]";
        "(dedup [3 3 3 5 5 5]) -> [3 5]";
        "(dedup [1 2 3 2 1]) -> [3 2 1]";
      ], "Removes duplicate elements from a list. Requires the specification of $member$.";
    ], "Multi-component examples";

  (* "compress", *)
  (* [ *)
  (*   "(compress []) -> []"; *)
  (*   "(compress [1]) -> [1]"; *)
  (*   "(compress [1 1 1]) -> [1]"; *)
  (*   "(compress [1 2 1]) -> [1 2 1]"; *)
  (*   "(compress [1 2 2 1]) -> [1 2 1]"; *)
  (*   "(compress [1 2 2 1 1 4 4]) -> [1 2 1 4]"; *)
  (*   "(compress [1 1 1 1 1 2 2 2 2 1 1 4 4]) -> [1 2 1 4]"; *)
  (* ]; *)

  (* ("cprod", ["(f []) -> [[]]"; *)
  (*            "(f [[]]) -> []"; *)
  (*            "(f [[] []]) -> []"; *)
  (*            "(f [[1 2 3] [4] [5 6]]) -> [[1 4 5] [1 4 6] [2 4 5] [2 4 6] [3 4 5] [3 4 6]]"; *)
  (*           ], []), *)
  (* ""; *)


  (* ("power", ["(f []) -> [[]]"; *)
  (*            "(f [0]) -> [[] [0]]"; *)
  (*            "(f [0 1]) -> [[] [1] [0] [0 1]]"; *)
  (*           ], []), *)
  (* ""; *)
    
  (* ("drop", ["(f [] 0) -> []"; *)
  (*           "(f [1] 0) -> [1]"; *)
  (*           "(f [] 1) -> []"; *)
  (*           "(f [] 2) -> []"; *)
  (*           "(f [0 1] 0) -> [0 1]"; *)
  (*           "(f [0 1] 1) -> [1]"; *)
  (*           "(f [0 1] 2) -> []"; *)
  (*           "(f [1 1 1] 0) -> [1 1 1]"; *)
  (*           "(f [1 1 1] 1) -> [1 1]"; *)
  (*           "(f [1 1 1] 2) -> [1]"; *)
  (*           "(f [1 1 1] 3) -> []"; *)
  (*            ], ["[]"]), *)
  (* "(if (= 0 n) l (drop (cdr l) (- n 1)))"; *)

  (* ("frequency", ["(f [1]) -> [1]"; *)
  (*                "(f [1 2]) -> [1 1]"; *)
  (*                "(f [1 2 1]) -> [2 1 2]"; *)
  (*               ], ["0"]), *)
  (* ""; *)
  ]

let all_cases =
  List.concat_map testcases ~f:(fun (cases, _) -> List.map cases ~f:(fun (name, _, _) -> name))

let time_solve verbose (name, example_strs, desc) =
  begin
    let examples = List.map example_strs ~f:Util.parse_example in
    let start_time = Time.now () in
    let solutions = Search.solve ~verbose examples in
    let end_time = Time.now () in
    let solve_time = Time.diff end_time start_time in
    let solutions_str =
      Util.Ctx.to_alist solutions
      |> List.map ~f:(fun (name, lambda) ->
                      let lambda = Expr.normalize lambda in
                      Expr.to_string (`Let (name, lambda, `Id "_")))
      |> String.concat ~sep:"\n"
    in
    printf "Solved %s in %s. Solutions:\n%s\n\n"
           name
           (Time.Span.to_short_string solve_time)
           solutions_str;
    flush stdout;
    name, solve_time, solutions_str, desc
  end

let output_table results =
  let pe = print_endline in
  let pf = printf in
  begin
    pe "\\begin{tabular}{l | l l p{10cm}}";
    pe "\\toprule";
    pe "Category & Name & Time & Description \\\\";
    List.iter 
      results 
      ~f:(fun (cases, desc) -> 
          begin
            pf "\\midrule\\multirow{%d}{2cm}{%s} \\\\\n" (List.length cases) desc;
            List.iter 
              cases 
              ~f:(fun (name, time, _, desc) -> 
                  pf "& %s & %s & %s \\\\\\n" name (Time.Span.to_short_string time) desc);
          end);
    pe "\\bottomrule";
    pe "\\end{tabular}";

    pe "\\begin{tabular}{l | l p{10cm}}";
    pe "\\toprule";
    pe "Category & Name & Implementation \\\\";
    List.iter 
      results 
      ~f:(fun (cases, desc) -> 
          begin
            pf "\\midrule\\multirow{%d}{2cm}{%s} \\\\\n" (List.length cases) desc;
            List.iter 
              cases 
              ~f:(fun (name, _, impl, _) ->
                  let impl' =
                    List.fold_left
                      ["%"; "#"; "_"]
                      ~init:impl
                      ~f:(fun impl' char ->
                          String.substr_replace_all impl' ~pattern:char ~with_:("\\" ^ char))
                  in
                  pf "& %s & %s \\\\\n" name impl');
          end);
    pe "\\bottomrule";
    pe "\\end{tabular}";
  end

let command =
  let spec = 
    let open Command.Spec in
    empty
    +> flag "-t" ~aliases:["--table"] no_arg ~doc:" print out a result table in LaTeX format"
    +> flag "-v" ~aliases:["--verbose"] no_arg ~doc:" print progress messages while searching"
    +> anon (sequence ("testcase" %: string))
  in
  Command.basic
    ~summary:"Run test cases and print timing results"
    spec
    (fun table verbose testcase_names () ->
     let testcases = match testcase_names with
       | [] -> testcases
       | _ ->
          List.map testcases 
                   ~f:(fun (cases, desc) -> 
                       List.filter cases ~f:(fun (name, _, _) -> List.mem testcase_names name), desc)
     in
     let results =
       List.map testcases ~f:(fun (cases, desc) -> List.map cases ~f:(time_solve verbose), desc)
     in
     if table then output_table results else ())

let () = Command.run command
      

