open Core.Std
open Ast

exception RuntimeError of string

(** Curried function for concating list without file seperator*)
let concat str = String.concat ~sep:"" str

(*Take the subrstring from a to b*)
let substring st a b = String.sub st ~pos:a ~len:(b-a)

(** Evaluate an expression in the provided context. *)
let rec eval_fun (exp:expr) =
  match exp with
  | `Id id               -> id
  | `Num x               -> string_of_int x
  | `Bool x              -> string_of_bool x
  | `Op (op, uneval_args) ->
     (let args = List.map ~f:(eval_fun) uneval_args in
      match args with 
                 | [x; y] -> (concat ["("; operator_to_str op ; " "; x ;" "; y ; ")"])
                 | _ -> raise (RuntimeError ("Bad argument to " ^ 
                                           (Ast.operator_to_str op))))
  | `Apply (`Id (id), uneval_args) ->
     (let args = List.map ~f:(eval_fun) uneval_args in
      match args with 
                 | [x; y] -> (concat ["("; id ; " "; x ;" "; y ; ")"])
                 | _ -> raise (RuntimeError "Bad argument to `Apply for function f"))
  | _ -> raise (RuntimeError "Invalid input expression (used an unsupported element of 'typ'.")

(*Makes Z3 string for defining constants*)

let rec define_consts args = 
  match args with
  |[] -> ""
  | hd::t1 -> concat ["(declare-const ";hd;" Int)\n";define_consts t1 ] (*TODO: Support to be potentially added for types from typed expressions later*)
(*generates Z3 string for arguments to go inside of Z3 define-fun*)

let rec make_fun_args args = match args with
  |[] -> ""
  | hd::t1 -> 
    let (id,_) = hd in
    concat ["(";id;" Int)";make_fun_args t1 ] (*TODO: Support to be potentially added for types from typed expressions later*)

(*Combines the Z3 make_fun_args output with eval_fun along with some other string element to complete the define-fun Z3 line*)
let define_fun args expr = concat ["(define-fun f (";make_fun_args args;") Int "; eval_fun expr; ")\n"]

(*returns a list of constants in expression exp that are not already in args (i.e. all non paramater variables in the expression)*)
let rec get_consts args (exp:expr) = 
  let contains args st = ((List.filter ~f:(fun elm -> elm = st) args) <> []) in
  let add_if_const args id = (match contains args id with
  | false -> concat [id; " "]
  | _ -> "") in
  match exp with
  | `Id id               -> add_if_const args id
  | `Op (_, uneval_args) ->
     (let op_params = List.map ~f:(get_consts args) uneval_args in
      match op_params with 
                 | [x; y] -> concat [x;" ";y]
                 | _ -> ""  )
  | _ -> ""

let find_and_filter_consts args exp = 
   List.filter ~f:(fun x -> x <> "") 
    (String.split ~on:' ' 
      (get_consts (List.map ~f:(fun (id,_) -> id) args) exp))

(*Parses values from the value list for assert statement*)
let rec traverse_assert_vals (values:value list) = match values with
  |[] -> ""
  | `Num(hd)::t1 -> 
    concat [string_of_int hd; " ";traverse_assert_vals t1 ]
  | _ -> raise (RuntimeError("This type of 'value' is not supported"))

(*generates the Z3 line of code for assert statements*)
let traverse_asserts (values:(value list * value)) = 
  let (in_args, out) = values in match out with
  | `Num o -> concat ["(assert (= (f "; traverse_assert_vals in_args;") ";string_of_int o;"))\n"]
  | _ -> raise (RuntimeError("This type of 'value' is not supported"))

(*calls traverse_asserts on every element in the value list then turns this all into a string (similar to maping the concating)*)
let rec define_asserts (values:(value list * value) list) = match values with
  |[] -> ""
  | hd::t1 -> 
    concat [traverse_asserts hd;define_asserts t1 ]

(*generates the get-value Z3 code based on constants passed in*)
let rec define_tail args = 
  match args with
  |[] -> ""
  | hd::t1 -> concat ["(get-value (";hd;"))\n";define_tail t1 ] (*TODO: Support to be potentially added for types from typed expressions later*)

(*Calls all Z3 generating functions and compiles all Z3 code into one long string*)
let generate_z3 (lambda:typed_id list * expr) (values:(value list * value) list) = 
  let (args,exp) = lambda in
  let consts = find_and_filter_consts args exp in
  concat [define_consts consts; define_fun args exp; define_asserts values; "(check-sat)\n";define_tail consts]

(** Code for the syscall method comes from Wikipedia *)
let syscall cmd =
  let ic, oc = Unix.open_process cmd in
  let buf = Buffer.create 16 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  let _ = Unix.close_process (ic, oc) in
  (Buffer.contents buf)

(*Cleans and further parses output *)
let clean_pair ls = 
  let ls = String.sub ls ~pos:2 ~len:((String.length ls) - 4) in 
  let index = String.index ls ' ' in
  let len = String.length(ls) in
  match index with
  | Some ind -> 
    let val1 = String.strip (substring ls ind len) in
    let val2 = if (String.contains val1 '(') then (substring val1 1 ((String.length val1)-1)) else val1 in
    let val3 = concat (String.split ~on:' ' val2) in
    ((String.strip (substring ls 0 ind)), (String.strip val3))
  | None -> assert false (* every z3 pair should have a variable then a space and then a numeric value *)

(*Parses output of Z3*)
let parse_z3_out (split_res:string list) = 
match List.hd split_res with
| Some "sat" -> Some (match List.tl split_res with
  | Some ls -> List.map ~f:(clean_pair) ((List.filter ~f:(fun f -> f <> "")) ls)
  | None -> raise (RuntimeError "Z3 error, Z3 input was not valid"))
| Some "unsat" -> None
| _ -> raise (RuntimeError "Z3 error, Z3 input was not valid")

(*Returns the value that coresponds to a perticular ID*)
let lookup id vals = 
  match List.filter ~f:(fun pair -> let (e, _) = pair in e = id) vals with
  | [(_,v)] -> `Num((int_of_string v))
  | [] -> `Id(id)
  | _ -> assert false

(*goes the the expression exp and replaces all constants with values which have been solved for by z3*)
let rec find_and_replace vals (exp:expr) = 
  match vals with 
  | Some v ->
    (match exp with 
    | `Id id               ->  (lookup id v)
    | `Num x               -> `Num(x)
    | `Bool x              -> `Bool(x)
    | `Op (op, uneval_args) ->
       (let args = List.map ~f:(find_and_replace vals) uneval_args in
        match args with 
                   | [x; y] -> `Op(op, [x;y])
                   | _ -> raise (RuntimeError ("Bad argument to " ^ 
                                             (Ast.operator_to_str op))))
    | `Apply (id, uneval_args) -> 
      (let args = List.map ~f:(find_and_replace vals) uneval_args in
        match args with 
                   | [x; y] -> `Apply(id, [x;y])
                   | _ -> raise (RuntimeError "Poor number of args for function CHANGE THIS!!"))
    | _ -> raise (RuntimeError "Invalid input expression (used an unsupported element of 'typ'."))
  | None -> raise (RuntimeError "The expression was unsatisfiable")

(*Evaluates Z3 input string and returns constants found*)
let z3_solve raw_z3 = 
  let (prefix, suffix) = ("unprocessedZ3", ".smt2") in
  let (file_name, oc) = Filename.open_temp_file prefix suffix in
      Printf.fprintf oc "%s\n" raw_z3;   
      close_out_noerr oc;
      let z3_out = syscall (concat ["Z3 -smt2 ";file_name]) in
      let _ = syscall (concat ["rm "; file_name]) in
      parse_z3_out (String.split ~on:'\n' z3_out)

(*Main method of this class, calls all Z3 generating functions then evaluates parses and returns*)
let sat_solve (lambda:expr) (values:(value list * value) list)  =
  match lambda with
  | `Lambda(args, _, exp) -> 
    (let raw_z3 = generate_z3 (args, exp) values in
      find_and_replace (z3_solve raw_z3) exp)
  | _ -> raise (RuntimeError "The value inputted into the Z3 solver was not a '`Lambda' expresssion")

(*creates the list of constraints as a string of runnable z3*)
let rec make_constraints constr vals = 
  match vals with
  | Some _ -> (match constr with
    | hd::tl -> concat ["(or (not ";eval_fun (find_and_replace vals hd);") "; (make_constraints tl vals);")"]
    | [] -> "false")
  | None -> assert false

(*adds a new assertion to the list of assertions which invalidate specific nodes of a search that have already been visited*)
let rec build_new_assert vals = 
    match vals with 
    | Some v -> (match v with
      | (id,num)::tl -> concat ["(and (not (= ";id;" "; num;")) ";(build_new_assert (Some tl));")"]
      | _ -> "true")
    | None -> assert false  

(* The powerhorse method of the symbolic solver recesivley calls itself and the sat solver untill it solves a problem or deams it unsatisfiable*)
let rec solve_itteration args exp constr values head asserts tail = 
  match z3_solve (concat [head; define_fun args exp; asserts; tail]) with 
  | Some s1_vals -> (
    let new_fun = (define_fun args (find_and_replace (Some s1_vals) exp)) in 
    let new_z3 = concat [head; new_fun;"(assert ";make_constraints constr (Some s1_vals);")\n"; tail] in
    match z3_solve new_z3 with
    | Some _ -> solve_itteration args exp constr values head (concat [asserts;"(assert ";build_new_assert (Some s1_vals);")\n"]) tail
    | None -> find_and_replace (Some s1_vals) exp)
  | None -> raise (RuntimeError "The expression was unsatisfiable")

(*The main method of the symbolic solver handles a few edge cases and then calls the solve_itteration method*)
let symb_solve (lambda:expr) (constraints:expr list) (values:(value list * value) list) = 
  match constraints with
  | [] -> sat_solve lambda values
  | _ ->  match lambda with
    | `Lambda (args, _, exp) -> 
      let consts = find_and_filter_consts args exp in
      let (head, asserts,tail) = (define_consts consts, define_asserts values, concat ["(check-sat)\n";define_tail consts]) in
      solve_itteration args exp constraints values head asserts tail;
    | _ -> raise (RuntimeError "The value inputted into the Z3 solver was not a '`Lambda' expresssion")

;;
