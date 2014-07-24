open Core.Std
open Ast
open Eval
open Util

(** A build set is a mapping from integers to sets of typed expressions. *)
module IntMap = Map.Make(Int)
module TypedExpr =
  struct
    type t = typed_expr
    let t_of_sexp = typed_expr_of_sexp
    let sexp_of_t = sexp_of_typed_expr
    let compare = compare_typed_expr
  end
module TypedExprSet = Set.Make(TypedExpr)
type build_set = TypedExprSet.t IntMap.t

exception SolveError of string

exception Solved of program
exception SolvedExpr of expr
exception TimedOut

let solve_error msg = raise (SolveError msg)

(** Add an expression to a build set. *)
let add (map: build_set) (x: typed_expr) : build_set =
  let (e, _) = x in
  IntMap.change map (size e) (function
                               | None -> Some (TypedExprSet.singleton x)
                               | Some xs -> Some (TypedExprSet.add xs x))

let contains (map: build_set) (x: typed_expr) = 
  let (e, _) = x in
  match IntMap.find map (size e) with
  | Some s -> TypedExprSet.mem s x
  | None -> false

(** Get the type of an example. Always results in an Arrow_t. *)
let typeof_example (ctx: type_ctx) (example: example) : typ =
  let (`Apply (_, inputs)), result = example in
  let input_types = List.map ~f:(typeof_expr ctx) (inputs :> expr list) in
  let result_type = typeof_expr ctx (result :> expr) in
  Arrow_t (input_types, result_type)

(** Extract the name of the target function from a list of examples. *)
let get_target_name (examples: example list) : id =
  match List.map ~f:(fun ex -> let (`Apply (`Id n, _)), _ = ex in n) examples with
  | [] -> solve_error "Example list is empty."
  | name::rest -> if List.for_all rest ~f:((=) name) then name
                  else solve_error "Multiple target names in example list."

(** Infer a function signature from input/output examples. *)
let signature (examples: example list) : typ =
  let name = get_target_name examples in
  match examples with
  | x::xs -> let init_ctx = bind (Util.empty_ctx ())
                                 ~key:name
                                 ~data:(typeof_example (Util.empty_ctx ()) x) in
             let final_ctx = 
               xs |> List.fold ~init:init_ctx
                               ~f:(fun ctx ex -> let example_typ = typeof_example ctx ex in
                                                 if example_typ = (lookup_exn name ctx)
                                                 then bind ctx ~key:name ~data:example_typ
                                                 else solve_error "Inconsistent types in example list.") in
             lookup_exn name final_ctx
  | [] -> solve_error "Example list is empty."

let counter =
  let count = ref (-1) in
  fun () -> incr count; !count

let fresh_name ?(prefix = "x") () = Printf.sprintf "%s%d" prefix (counter ())

(** Create n fresh variable names. *)
let fresh_names (n: int) : id list =
  List.range 0 n |> List.map ~f:(fun _ -> fresh_name ())

(** Create a type context from a list of typed ids. *)
let create_ctx (vars: typed_expr list) : type_ctx =
  List.fold vars ~f:(fun ctx (e, t) -> match e with
                                       | `Id n -> bind ctx ~key:n ~data:t
                                       | _ -> ctx)
            ~init:(Util.empty_ctx ())

let apply_candidate (def: [< `Define of id * expr ]) (inputs: expr list) : value =
  let `Define (id, _) = def in
  let app = `Apply (`Id id, inputs) in
  let prog = [(def :> expr); app] in
  prog_eval prog
   
let select (map: build_set) (pred: typ -> bool) (size: int) : typed_expr list =
  match IntMap.find map size with
  | Some exprs -> TypedExprSet.filter exprs ~f:(fun (_, t) -> pred t) 
                  |> TypedExprSet.to_list
  | None -> []

let solve_verifier ?(max_depth=None)
                   (init: typed_expr list)
                   (verify: expr -> Verify.status) : expr option =
  (* Create a type context from the target function signature and
  typed arguments so that expressions can be typed correctly. *)
  let ctx = create_ctx init in

  (* Create a mutable set to hold expressions sorted by size. *)
  let build = ref (IntMap.empty) in
  let i = ref 1 in

  (** Check all expressions using the oracle. Raise a Solve exception
  if a solution is found. *)
  let check_exprs ?allow_const:(ac = false) (exprs: expr list) : unit =
    build :=
      List.fold exprs
                ~init:(!build)
                ~f:(fun build_set expr ->
                    (* Attempt to simplify the
                    expression. Simplification can fail if the
                    expression is found to contain an illegal
                    operation. *)
                    match Rewrite.simplify expr with
                    | Some simple_expr ->
                       (* Check whether the expression is already in
                       the build set, meaning that it has already been
                       checked. *)
                       let typed_expr = simple_expr, typeof_expr ctx expr in
                       if contains build_set typed_expr
                       then build_set
                       else (match verify expr with
                             | Verify.Valid -> raise (SolvedExpr expr)
                             | Verify.Invalid ->
                                if (Rewrite.is_constant simple_expr) && (not ac)
                                then build_set
                                else add build_set typed_expr
                             | Verify.Error -> build_set)
                    | None -> build_set)
          in

  let rec select_children ?prev:(prev=[]) types sizes : expr list list =
    match types, sizes with
    | [], [] -> []
    | [tp], [s] -> select !build (tp prev) s 
                   |> List.map ~f:(fun (e, _) -> [Rewrite.complicate e])
    | tp::tps, s::ss ->
       (* Select all possible arguments for this position using the
       type predicate and size parameters. *)
       let arg_choices = select !build (tp prev) s 
                         |> List.map ~f:(fun (e, t) -> (Rewrite.complicate e, t)) in
       
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
      init |> List.map ~f:(fun (e, _) -> e) |> check_exprs ~allow_const:true;

      while true do
        (* Derive all expressions of size i from each operator. *)
        List.iter operators
          ~f:(fun op ->
                      List.iter (arg_sizes !i op.arity)
                ~f:(fun sizes -> 
                    select_children op.input_types sizes
                    |> List.map ~f:(fun args -> `Op (op.name, args))
                    |> check_exprs));
        Int.incr i;
        match max_depth with
        | Some max -> if !i >= max then raise TimedOut else ()
        | None -> ()
      done;
      solve_error "Completed solve loop without finding solution.";
    end
  with
  | SolvedExpr expr -> Some expr
  | TimedOut -> None

let solve ?(init=[])
          ?(max_depth=None)
          (examples: example list)
          (constraints: constr list) : function_def option =
  (* Extract the name of the target function from the examples. *)
  let target_name = get_target_name examples in

  let sig_ = signature examples in
  match sig_ with 
  | Arrow_t (input_types, _) -> 
     let target_args = List.map input_types 
                                ~f:(fun typ -> (fresh_name ()), typ) in

     (* Generate the set of initial expressions from the argument
     names and any provided expressions. *)
     let initial = (List.map init ~f:(fun expr -> expr, typeof_expr (Util.empty_ctx ()) expr))
                   @ (List.map target_args ~f:(fun (name, typ) -> `Id name, typ)) in

     (* Generate an oracle function from the examples. *)
     let verify expr =
       let target_def = `Define (target_name, `Lambda (target_args, expr)) in
       Verify.verify examples constraints target_def
     in

     (match solve_verifier ~max_depth:max_depth initial verify with
      | Some expr -> Some (`Define (target_name, `Lambda (target_args, expr)))
      | None -> None)
  | _ -> solve_error "Examples do not represent a function."

let rec solve_catamorphic ?(init=[]) (examples: example list) : function_def list =
  let _ = List.map ~f:(fun e -> print_endline (example_to_string e)) examples in

  match signature examples with
  (* If the signature is list 'a -> list 'b, then assume f can be
    implemented using either map or filter. *)
  | Arrow_t ([List_t _], List_t _) ->
     let extract_lists (ex: example) = match ex with
       | (`Apply (_, [`List (i, _)])), `List (o, _) -> i, o
       | _ -> solve_error "Expression does not conform to type." in

     (* If the input and output lists are the same length in every
     example, assume f can be implemented using map. *)
     if List.for_all examples ~f:(fun ex -> let i, o = extract_lists ex in 
                                            (List.length i) = (List.length o))
     then solve_map ~init:init examples

     (* If there is an example with a shorter output list than its
     input list, implement with filter. Otherwise, use fold, since it
     is the most general. *)
     else 
       if List.exists examples ~f:(fun ex -> let i, o = extract_lists ex in 
                                             (List.length i) > (List.length o))
       then solve_filter ~init:init examples
       else solve_fold ~init:init examples

  (* If the input is list 'a -> 'b, assume that f can be implemented
    using a fold. *)
  | Arrow_t ([List_t _], _) -> solve_fold ~init:init examples

  (* Otherwise, perform a general search for f. *)
  | _ -> match solve ~init:init examples [] with
         | Some def -> [def]
         | None -> []

and solve_fold ?(init=[]) (examples: example list) : function_def list =
  let Arrow_t ([List_t elem_type], _) = signature examples in

  (* Locate the base case example and extract the initial value for
     the fold. Base case examples are those that look like f([]) -> x. *)
  let partition_base ex = (match ex with
                           | (`Apply (_, [`List ([], _)])), _ -> `Fst ex
                           | rex -> `Snd rex) in
  let base, recursive = List.partition_map examples ~f:partition_base in

  (match List.dedup ~compare:compare_example base with
   | [(`Apply (_, _)), fold_init] ->
      (* Extract examples for the lambda that is passed to fold. *)
      let lambda_name = fresh_name () in
      let apply_lambda (acc: const_app) (elem: const) : example_lhs = 
        `Apply (`Id lambda_name, [acc; (elem :> const_app)]) in
      let (lambda_examples: example list) =
        List.map recursive ~f:(fun ((`Apply (_, [`List (x::xs, _)])), result) ->
                               (List.fold xs ~init:(apply_lambda (fold_init :> const_app) x)
                                          ~f:(fun a e -> apply_lambda (a :> const_app) e)),
                               result) in

      (* Solve for the lambda using extracted examples. *)
      let lambda_def = solve_catamorphic ~init:init lambda_examples in

      (* Generate the definition of the target function and return. *)
      let name = get_target_name examples in
      let list_name = fresh_name () in
      lambda_def @
        [`Define (name, `Lambda ([list_name, List_t elem_type],
                                 `Op (Fold, [`Id list_name; `Id lambda_name; (fold_init :> expr)])))]
   | _ -> solve_error "Multiple return values for the same input.")

and solve_filter ?(init=[]) (examples: example list) : function_def list =
  let Arrow_t ([List_t elem_type], _) = signature examples in
  let lambda_name = fresh_name () in
  let filter_ex ret elem : example = (`Apply (`Id lambda_name, [(elem :> const_app)])), `Bool ret in
  let lambda_examples = 
    List.concat_map examples 
                    ~f:(fun ((`Apply (_, [`List (input, _)])), `List (result, _)) ->
                        let retained, removed = List.partition_tf input ~f:(List.mem result) in
                        (List.map retained ~f:(filter_ex true) @
                          (List.map removed ~f:(filter_ex false)))) in
  let lambda_def = solve_catamorphic ~init:init lambda_examples in
  let name = get_target_name examples in
  let list_name = fresh_name () in
  lambda_def @
    [`Define (name, `Lambda ([list_name, List_t elem_type],
                             `Op (Filter, [`Id list_name; `Id lambda_name])))]

and solve_map ?(init=[]) (examples: example list) : function_def list =
  let Arrow_t ([List_t elem_type], _) = signature examples in
  let lambda_name = fresh_name () in
  let map_ex elem ret = (`Apply (`Id lambda_name, [(elem :> const_app)])), ret in
  let (lambda_examples: example list) =
    List.concat_map examples ~f:(fun ((`Apply (_, [`List (input, _)])), `List (result, _)) ->
                                 List.map2_exn input result ~f:map_ex) in
  let lambda_def = solve_catamorphic ~init:init lambda_examples in
  let name = get_target_name examples in
  let list_name = fresh_name () in
  lambda_def @
    [`Define (name, `Lambda ([list_name, List_t elem_type],
                             `Op (Map, [`Id list_name; `Id lambda_name])))]
