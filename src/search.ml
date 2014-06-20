open Core.Std
open Ast
open Eval
open Util

(** A build set is a mapping from integers to sets of expressions. *)
module IntSet = Map.Make(Int)
type build_set = typed_expr list IntSet.t

(** An example is a list of input expressions and a resulting
expression. The target function will be evaluated with the input
expressions as arguments and checked against the evaluated result. *)
type example = expr list * expr

exception Solved of expr
exception SolveError of string

let solve_error msg = raise (SolveError msg)

let example_to_string (inputs, result) = 
  let inputs_str = inputs |> List.map ~f:expr_to_string |> String.concat ~sep:" " in
  let result_str = expr_to_string result in
  inputs_str ^ " -> " ^ result_str

(** Add an expression to a build set. *)
let add_expr (map: build_set) (x: typed_expr) : build_set =
  let (e, _) = x in
  IntSet.change map (size e) (function
                               | None -> Some [x]
                               | Some xs -> Some (x::xs))

(** Get the type of an example. Always results in an Arrow_t. Needs a
type context, because the example could contain ids that need to be
resolved. *)
let typeof_example (ctx: type_ctx) (example: example) : typ =
  let (inputs, result) = example in
  let input_types = List.map ~f:(typeof_expr ctx) inputs in
  let result_type = typeof_expr ctx result in
  Arrow_t (input_types, result_type)

(** Infer a function signature from input/output examples. *)
let signature (ctx: type_ctx) (examples: example list) : typ =
  let types = List.map ~f:(typeof_example ctx) examples in
  match types with
  | [] -> solve_error "Example list is empty."
  | x::xs -> List.fold_left xs ~f:specialize ~init:x

let fresh_name = 
  let c = ref 0 in
  let fresh () = c := !c + 1; Printf.sprintf "x%d" !c in
  fresh

(** Create n fresh variable names. *)
let fresh_names (n: int) : id list =
  List.range 0 n |> List.map ~f:(fun _ -> fresh_name ())

(** Create initial typed variables for each argument in the signature
    using names. *)
let initial_vars (sign: typ) : typed_expr list =
  let Arrow_t (input_types, _) = sign in
  let names = fresh_names @@ List.length input_types in
  List.map2_exn input_types names ~f:(fun t n -> (`Id n, t))

(** Create a type context from a list of typed ids. *)
let create_ctx (vars: typed_expr list) : type_ctx =
  List.fold vars ~f:(fun ctx (e, t) -> match e with
                                       | `Id n -> bind ctx ~key:n ~data:t
                                       | _ -> ctx)
            ~init:(empty_type_ctx)

(** Returns a function that checks a function against the provided
    examples. target_name is the name that the function is bound to in
    the provided definition. *)
let oracle (examples: example list) (target_name: id) : [< `Define of id * expr ] -> bool =
  (fun def ->
   List.for_all 
     examples
     ~f:(fun (input, result) -> let app = `Apply (`Id target_name, input) in
                                let prog = [(def :> expr); app] in
                                try (prog_eval prog) = (eval (empty_eval_ctx) result) with
                                  _ -> false))

let select (map: build_set) (pred: typ -> bool) (size: int) : typed_expr list =
  match IntSet.find map size with
  | Some exprs -> List.filter exprs ~f:(fun (_, t) -> pred t)
  | None -> ((* Printf.printf "No exprs of size %d.\n" size; *) [])

let solve ?(init=[]) ?(tctx=(empty_type_ctx)) ?(ectx=(empty_eval_ctx)) 
          (examples: example list) =
  let target_name = "f" in

  (* Generate typed names to bind each argument in each example to. *)
  let sign = signature tctx examples in
  let argument_ids = initial_vars sign in
  let argument_names = List.map ~f:(fun (`Id n, t) -> (n, t)) argument_ids in

  (* Generate the set of initial expressions from the argument names
  and any provided expressions. *)
  let initial =
    (List.map ~f:(fun e -> (e, typeof_expr (empty_type_ctx) e)) init) @
      argument_ids in
  
  (* Generate an oracle function from the examples and the name of the
  target function. *)
  let check = oracle examples target_name in

  (* Create a type context from the target function signature and
  typed arguments so that expressions can be typed correctly. *)
  let ctx = create_ctx initial |> bind ~key:target_name ~data:sign in

  (* Create a mutable set to hold expressions sorted by size. *)
  let build = ref (IntSet.empty) in
  let i = ref 1 in

  (** Check all expressions using the oracle. Raise a Solve exception
  if a solution is found. *)
  let check_exprs (exprs: expr list) : unit =
    List.iter 
      exprs
      ~f:(fun e -> 
          let def = `Define (target_name, `Lambda (argument_names, e)) in
          (* Printf.printf "Checked: %s\n" (expr_to_string def); *)
          (if check def then raise (Solved def) else
             try build := add_expr !build (e, typeof_expr ctx e) with 
               _ -> ()))
  in

  let rec select_children ?prev:(prev=[]) types sizes : expr list list =
    match types, sizes with
    | [], [] -> []
    | [tp], [s] -> select !build (tp prev) s |> List.map ~f:(fun (e, _) -> [e])
    | tp::tps, s::ss -> 
       (* Select all possible arguments for this position using the
       type predicate and size parameters. *)
       let arg_choices = select !build (tp prev) s in
       
       (* For each choice of argument, select all possible remaining
       arguments. *)
       List.map ~f:(fun (e, t) -> select_children ~prev:(prev @ [t]) tps ss
                                  |> List.map ~f:(fun cx -> e::cx)) arg_choices
       |> List.concat_no_order
    | _ -> solve_error "Mismatched operator arity and type predicates." in

  let arg_sizes depth arity : int list list = 
    m_partition depth arity |> List.map ~f:permutations |> List.concat |> uniq
  in

  try
    begin
      (* Check all initial expressions and add them to the build set. *)
      initial |> List.map ~f:(fun (e, _) -> e) |> check_exprs;

      while true do
        (* Derive all expressions of size i from each operator. *)
        List.iter
          operators
          ~f:(fun op ->
              let arity = op.arity in
              List.iter
                (arg_sizes !i arity)
                ~f:(fun sizes -> 
                    select_children op.input_types sizes
                    |> List.map ~f:(fun args -> `Op (op.name, args))
                    |> check_exprs));

        (* Derive all expressions of size i using a recursive call to
        the synthesized function. *)
        let Arrow_t (its, _) = sign in
        let preds = List.map its ~f:(fun it -> (fun _ t -> t = it)) in
        let arity = List.length its in
        List.iter (arg_sizes !i arity)
                  ~f:(fun sizes -> 
                      select_children preds sizes
                      |> List.map 
                           ~f:(fun args -> `Apply (`Id target_name, args))
                      |> check_exprs);
        
        i := !i + 1;
      done;
      solve_error "Completed solve loop without finding solution.";
    end
  with
  | Solved expr -> expr
;;

let solve_catamorphic ?init:(init=[]) examples : expr =
  (* let _ = List.iter examples ~f:(fun ex -> Printf.printf "%s\n" (example_to_string ex)) in *)
  let Arrow_t (input_types, result_type) = signature (empty_type_ctx) examples in
  (* let _ = Printf.printf "%s\n" (typ_to_string (signature (empty_type_ctx) examples)) in *)
  match input_types with
  (* If the input is a list of 'a, assume that f can be implemented
    using a left fold. *)
  | [List_t elem_type] -> 
     let target_name = "f" in
     let apply_t ac el = `Apply (`Id target_name, [ac; el]) in
     (match examples with 
      | [] -> solve_error "No examples provided."
      | base::recursive ->
         let (_, base_o) = base in
         
         (* Extract examples for the lambda passed to foldl. *)
         let f_examples =
           List.map
             ~f:(fun (i, o) ->
                 (match i with
                  | [`List l] -> (match List.fold_left ~f:apply_t ~init:base_o l with
                                  | `Apply (_, [a; e]) -> ([a; e], o)
                                  | _ -> solve_error "Multiple base expressions provided.")
                  | _ -> solve_error "Too many arguments in example."))
             recursive in

         (* Create a type context that includes the type of the lambda
         bound to the target name. *)
         let f_sign = Arrow_t ([result_type; elem_type], result_type) in
         let f_ctx = bind (empty_type_ctx) ~key:target_name ~data:f_sign in

         (* let _ = List.iter f_examples ~f:(fun ex -> Printf.printf "%s\n" (example_to_string ex)) in *)
         (match solve ~init:init ~tctx:f_ctx f_examples with
          | `Define (_, lambda) -> 
             let arg_name = fresh_name () in
             `Define (target_name, 
                      `Lambda ([(arg_name, List_t elem_type)],
                               `Op (Foldl, [`Id arg_name; lambda; base_o])))
          | _ -> solve_error "Solving for lambda failed."))
  (* Otherwise, perform a general search for f. *)
  | _ -> solve ~init:init examples
