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

exception Solved of function_def
exception SolveError of string

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
let target_name (examples: example list) : id = 
  match List.map ~f:(fun ex -> let (`Apply (`Id n, _)), _ = ex in n) examples with
  | [] -> solve_error "Example list is empty."
  | name::rest -> if List.for_all rest ~f:((=) name) then name
                  else solve_error "Multiple target names in example list."

(** Infer a function signature from input/output examples. *)
let signature (examples: example list) : typ =
  let name = target_name examples in
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
            ~init:(Util.empty_ctx ())

let apply_candidate (def: [< `Define of id * expr ]) (inputs: expr list) : value =
  let `Define (id, _) = def in
  let app = `Apply (`Id id, inputs) in
  let prog = [(def :> expr); app] in
  prog_eval prog

(** Returns a function that checks a function against the provided
    examples. target_name is the name that the function is bound to in
    the provided definition. *)
let oracle (examples: example list) : [< `Define of id * expr ] -> bool =
  (fun def -> List.for_all 
                examples ~f:(fun (input, result) -> 
                             try (prog_eval [(def :> expr); (input :> expr)]) = (result :> value) with
                               RuntimeError _ -> false))
   
let select (map: build_set) (pred: typ -> bool) (size: int) : typed_expr list =
  match IntMap.find map size with
  | Some exprs -> TypedExprSet.filter exprs ~f:(fun (_, t) -> pred t) 
                  |> TypedExprSet.to_list
  | None -> []

let solve ?(init=[]) (examples: example list) : function_def =
  (* Extract the name of the target function from the examples. *)
  let name = target_name examples in

  (* Generate typed names to bind each argument in each example to. *)
  let sig_ = signature examples in
  let argument_ids = initial_vars sig_ in
  let argument_names = List.map ~f:(fun (`Id n, t) -> (n, t)) argument_ids in

  (* Generate the set of initial expressions from the argument names
  and any provided expressions. *)
  let initial = (List.map ~f:(fun e -> (e, typeof_expr (Util.empty_ctx ()) e)) init) @
                  argument_ids in
  
  (* Generate an oracle function from the examples. *)
  let check = oracle examples in

  (* Create a type context from the target function signature and
  typed arguments so that expressions can be typed correctly. *)
  let ctx = create_ctx initial |> bind ~key:name ~data:sig_ in

  (* Create a mutable set to hold expressions sorted by size. *)
  let build = ref (IntMap.empty) in
  let i = ref 1 in

  (** Check all expressions using the oracle. Raise a Solve exception
  if a solution is found. *)
  let check_exprs ?allow_const:(ac = false) (exprs: expr list) : unit =
    List.iter 
      exprs
      ~f:(fun e ->
          match Rewrite.simplify e with
          | Some se -> let te = se, typeof_expr ctx e in
                       if not (contains !build te)
                       then
                         begin
                           let def = `Define (name, `Lambda (argument_names, e)) in
                           if check def then raise (Solved def)
                           else
                             if ac || (not (Rewrite.is_constant se)) then
                               begin
                                 (* Printf.printf "%s -> %s\n" (expr_to_string e) (expr_to_string se); *)
                                 try build := add !build te with _ -> ()
                               end
                             else ()
                         end
                       else ()
          | None -> ())
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
      initial |> List.map ~f:(fun (e, _) -> e) |> check_exprs ~allow_const:true;

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

        (* (* Derive all expressions of size i using a recursive call to *)
        (* the synthesized function. *) *)
        (* let Arrow_t (its, _) = sign in *)
        (* let preds = List.map its ~f:(fun it -> (fun _ t -> t = it)) in *)
        (* let arity = List.length its in *)
        (* List.iter (arg_sizes !i arity) *)
        (*           ~f:(fun sizes -> *)
        (*               select_children preds sizes *)
        (*               |> List.map *)
        (*                    ~f:(fun args -> `Apply (`Id target_name, args)) *)
        (*               |> check_exprs); *)
        
        i := !i + 1;
      done;
      solve_error "Completed solve loop without finding solution.";
    end
  with
  | Solved expr -> expr
;;

let rec solve_catamorphic ?(init=[]) (examples: example list) : function_def list =
  match signature examples with
  (* If the signature is list 'a -> list 'a, then assume f can be
    implemented using filter. *)
  | Arrow_t ([List_t et1], List_t et2) when et1 = et2 -> 
     let extract_lists (ex: example) = match ex with (`Apply (_, [`List (i, _)])), `List (o, _) -> i, o in
     (* If the input and output lists are the same length in every
     example, assume f can be implemented using map. *)
     if List.for_all examples ~f:(fun ex -> let i, o = extract_lists ex in (List.length i) = 
                                                                             (List.length o))
     then solve_map ~init:init examples

     (* If there is an example with a shorter output list than its
     input list, implement with filter. Otherwise, use fold, since it
     is the most general. *)
     else 
       if List.exists examples ~f:(fun ex -> let i, o = extract_lists ex in (List.length i) > 
                                                                              (List.length o))
       then solve_filter ~init:init examples
       else solve_fold ~init:init examples

  (* If the input is a list of 'a, assume that f can be implemented
    using a fold. *)
  | Arrow_t ([List_t _], _) -> solve_fold ~init:init examples

  (* Otherwise, perform a general search for f. *)
  | _ -> [solve ~init:init examples]

and solve_fold ?(init=[]) (examples: example list) : function_def list =
  let Arrow_t ([List_t elem_type], _) = signature examples in

  (* Locate the base case example and extract the initial value for
     the fold. Base case examples are those that look like f([]) -> x. *)
  let partition_base ex = (match ex with
                           | (`Apply (_, [`List ([], _)])), _ -> `Fst ex
                           | rex -> `Snd rex) in
  let base, recursive = List.partition_map examples ~f:partition_base in

  (match base with
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
      let name = target_name examples in
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
  let name = target_name examples in
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
  let name = target_name examples in
  let list_name = fresh_name () in
  lambda_def @
    [`Define (name, `Lambda ([list_name, List_t elem_type],
                             `Op (Map, [`Id list_name; `Id lambda_name])))]

