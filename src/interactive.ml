open Core.Std
open Printf

let read_input () =
  let input = ref [] in
  let _done = ref false in
  (while not !_done do
    let line = input_line stdin in
      if line = ""
      then _done := true
      else input := !input @ [line]
  done);
  !input

let solve bk_strs example_strs =
  begin
    let bk = List.map bk_strs ~f:(fun (name, impl) -> name, Util.parse_expr impl) in
    let examples = List.map example_strs ~f:Util.parse_example in
    let start_time = Time.now () in
    let solutions = Search.solve ~init:Search.extended_init ~bk examples in
    let end_time = Time.now () in
    let solve_time = Time.diff end_time start_time in
    let solutions_str =
      Util.Ctx.to_alist solutions
      |> List.map
           ~f:(fun (name, lambda) ->
               match lambda with
               | `Let (_, lambda', _) ->
                  sprintf "%s = %s" name (lambda' |> Expr.to_string)
               | _ -> failwith "Unexpected expression.")
      |> String.concat ~sep:"\n"
    in
    printf "Solved in %s. Solutions:\n%s\n\n"
           (Time.Span.to_short_string solve_time) solutions_str;
    flush stdout;
  end

let () =
  try
    while true do
      let input = read_input () in
      solve [] input
    done
  with End_of_file -> ()
