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
  | `Nil                 -> ""
  | `Op (op, uneval_args) ->
     (let args = List.map ~f:(eval_fun) uneval_args in
      match args with 
                 | [x; y] -> (concat ["("; operator_to_str op ; " "; x ;" "; y ; ")"])
                 | _ -> raise (RuntimeError ("Bad argument to " ^ 
                                           (Ast.operator_to_str op))))
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
let generate_Z3 (lambda:typed_id list * expr) (values:(value list * value) list) = 
  let (args,exp) = lambda in
  let consts = List.filter ~f:(fun x -> x <> "") 
    (String.split ~on:' ' 
      (get_consts (List.map ~f:(fun (id,_) -> id) args) exp)) in
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

(* File for unprocessed Z3 to be written to*)
let file = "t_unprocessedZ3.smt2"

(*Cleans and further parses output *)
let clean_pair ls = 
  let ls = String.sub ls ~pos:2 ~len:((String.length ls) - 4) in 
  let index = String.index ls ' ' in
  let len = String.length(ls) in
  match index with
  | Some ind -> ((String.strip (substring ls 0 ind)), (String.strip (substring ls ind len)))
  | None -> assert false (* every z3 pair should have a variable then a space and then a numeric value *)

(*Parses output of Z3*)
let parse_z3_out (split_res:string list) = 
match List.hd split_res with
| Some "sat" -> (match List.tl split_res with
  | Some ls -> List.map ~f:(clean_pair) ((List.filter ~f:(fun f -> f <> "")) ls)
  | None -> raise (RuntimeError "Z3 error, Z3 input was not valid"))
| Some "unsat" -> raise (RuntimeError "The probablem was unsatisfiable")
| _ -> raise (RuntimeError "Z3 error, Z3 input was not valid")

let lookup id vals = 
  match List.filter ~f:(fun pair -> let (e, _) = pair in e = id) vals with
  | [(_,v)] -> `Num((int_of_string v))
  | [] -> `Id(id)
  | _ -> assert false

let rec find_and_replace vals (exp:expr) = 
  match exp with 
  | `Id id -> (lookup id vals)
  | `Num x               -> `Num(x)
  | `Bool x              -> `Bool(x)
  | `Nil                 -> `Nil
  | `Op (op, uneval_args) ->
     (let args = List.map ~f:(find_and_replace vals) uneval_args in
      match args with 
                 | [x; y] -> `Op(op, [x;y])
                 | _ -> raise (RuntimeError ("Bad argument to " ^ 
                                           (Ast.operator_to_str op))))
  | _ -> raise (RuntimeError "Invalid input expression (used an unsupported element of 'typ'.")

(*Main method of this class, calls all Z3 generating functions then evaluates parses and returns*)
let symb_solve (lambda:expr) (values:(value list * value) list)  = 
  match lambda with
  | `Lambda(ids, exp) -> 
    (let raw_Z3 = generate_Z3 (ids, exp) values in
    let file = "t_unprocessedZ3.smt2" in
    let oc = open_out file in
      Printf.fprintf oc "%s\n" raw_Z3;   
      close_out_noerr oc; 
      let z3_out = syscall (concat ["Z3 -smt2 ";file]) in
      find_and_replace (parse_z3_out (String.split ~on:'\n' z3_out)) exp)
  | _ -> raise (RuntimeError "The value inputted into the Z3 solver was not a '`Lambda' expresssion")
;;
