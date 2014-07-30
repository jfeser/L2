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

type body = program * example list * typ String.Map.t * const_app String.Map.t list

type spec = {
  target: expr -> expr;
  examples: example list;
  tctx: typ String.Map.t;
  vctxs: const_app String.Map.t list;
  fold_depth: int;
}

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
                               ~f:(fun ctx ex ->
                                   let example_typ = typeof_example ctx ex in
                                   let existing_typ = (lookup_exn name ctx) in
                                   if example_typ = existing_typ
                                   then bind ctx ~key:name ~data:example_typ
                                   else solve_error (Printf.sprintf
                                                       "Inconsistent types in example list (%s and %s). %s"
                                                       (typ_to_string example_typ)
                                                       (typ_to_string existing_typ)
                                                       (String.concat ~sep:" "
                                                                      (List.map ~f:example_to_string
                                                                                examples)))) in
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
  | Arrow_t (input_types, ret_typ) ->
     let target_args = List.map input_types
                                ~f:(fun typ -> (fresh_name ()), typ) in
     let target_def expr = `Define (target_name, `Lambda (target_args, ret_typ, expr)) in

     (* Generate the set of initial expressions from the argument
     names and any provided expressions. *)
     let initial = (List.map init ~f:(fun expr -> expr, typeof_expr (Util.empty_ctx ()) expr))
                   @ (List.map target_args ~f:(fun (name, typ) -> `Id name, typ)) in

     (* Generate an oracle function from the examples. *)
     let verify expr =
       Verify.verify examples constraints (target_def expr)
     in

     (match solve_verifier ~max_depth:max_depth initial verify with
      | Some expr -> Some (target_def expr)
      | None -> None)
  | _ -> solve_error "Examples do not represent a function."

let get_example_typ_ctx (examples: example list)
                        (arg_names: string list) : typ String.Map.t =
  match signature examples with
  | Arrow_t (arg_typs, _) ->
     let name_typ_pairs = List.zip_exn arg_names arg_typs in
     String.Map.of_alist_exn name_typ_pairs
  | _ -> solve_error "Examples do not represent a function."

let get_example_value_ctxs (examples: example list)
                           (arg_names: string list) : const_app String.Map.t list =
  List.map examples
           ~f:(fun ((`Apply (_, inputs)), _) ->
               let name_value_pairs = List.zip_exn arg_names inputs in
               String.Map.of_alist_exn name_value_pairs)

let ctx_merge outer_ctx inner_ctx =
  String.Map.merge outer_ctx inner_ctx
                   ~f:(fun ~key:_ value ->
                       match value with
                       | `Both (_, ictx_v) -> Some ictx_v
                       | `Left octx_v -> Some octx_v
                       | `Right ictx_v -> Some ictx_v)

let const_base_cases typ =
  match typ with
  | Num_t -> [`Num 0; `Num 1]
  | Bool_t -> [`Bool true; `Bool false]
  | List_t elem_typ -> [`List ([], elem_typ)]
  | _ -> solve_error "Not a constant type."

let create_spec target examples tctx vctxs fold_depth =
  { target = target; examples = examples;
    tctx = tctx; vctxs = vctxs; fold_depth = fold_depth; }

(* Map is an appropriate implementation when one of the inputs is a
   list and the output is a list of the same length. *)
let map_bodies (spec: spec) : spec list =
  let map_example lambda_name input result =
    (`Apply (`Id lambda_name, [input])), result
  in
  let map_examples examples vctxs lambda_name list_name =
    List.map2_exn vctxs examples
                  ~f:(fun vctx (_, result) ->
                      let vctx' = String.Map.remove vctx list_name in
                      match (String.Map.find_exn vctx list_name), result with
                      | (`List (x, _)), (`List (y, _)) ->
                         List.map2_exn x y ~f:(fun i o ->
                                               (map_example lambda_name (i :> const_app) o), vctx')
                      | _ -> [])
    |> List.concat
    |> List.unzip
  in

  match signature spec.examples with
  | Arrow_t (arg_typs, List_t elem_typ) ->
     (* Extract the name of the target function and generate the
        names of the target function's arguments. The types of the
        target function's arguments are available in the type
        signature. *)
     let arg_names = List.map arg_typs ~f:(fun _ -> fresh_name ()) in
     let target_args = List.zip_exn arg_names arg_typs in

     (* Generate type and value contexts. There is one overall type
        context, since each example should have the same type, but
        there will be a value context for each example. *)
     let tctx = ctx_merge (get_example_typ_ctx spec.examples arg_names) spec.tctx in
     let vctxs = List.map2_exn (get_example_value_ctxs spec.examples arg_names) spec.vctxs
                               ~f:(fun ivctx ovctx -> ctx_merge ivctx ovctx) in

     (* Select all lists that are the same length as the result for
     every example and that differ from the result on at least one
     example. *)
     tctx
     |> String.Map.filter
          ~f:(fun ~key:name ~data:typ ->
              match typ with
              | List_t _ ->
                 List.for_all2_exn vctxs spec.examples
                                   ~f:(fun vctx (_, result) ->
                                       match (String.Map.find_exn vctx name), result with
                                       | (`List (x, _)), (`List (y, _)) -> (List.length x) = (List.length y)
                                       | (`Apply _), (`List _) -> true
                                       | _ -> solve_error "Examples do not have a consistent type.")
                 && List.exists2_exn vctxs spec.examples
                                     ~f:(fun vctx (_, result) ->
                                         match (String.Map.find_exn vctx name), result with
                                         | (`List (x, _)), (`List (y, _)) -> x <> y
                                         | (`Apply _), (`List _) -> false
                                         | _ -> solve_error "Examples do not have a consistent type.")
              | _ -> false)
     |> String.Map.keys

     (* Generate a list of new specifications from the selected names. *)
     |> List.map ~f:(fun list_name ->
                     let lambda_tctx = String.Map.remove tctx list_name in
                     let lambda_name = fresh_name ~prefix:"f" () in
                     let lambda_examples,
                         lambda_vctxs = map_examples spec.examples vctxs lambda_name list_name in
                     let target lambda =
                       spec.target (`Lambda (target_args, elem_typ, `Op (Map, [`Id list_name; lambda]))) in
                     create_spec target lambda_examples lambda_tctx lambda_vctxs spec.fold_depth)
     |> List.filter ~f:(fun spec -> match spec.examples with
                                    | [] -> false
                                    | _ -> true)
  | _ -> []

let filter_bodies (spec: spec) : spec list =
  let filter_example lambda_name input result : example =
    (`Apply (`Id lambda_name, [input])), `Bool result
  in
  let filter_examples examples vctxs lambda_name list_name =
    List.map2_exn vctxs examples
                  ~f:(fun vctx (_, result) ->
                      let vctx' = String.Map.remove vctx list_name in
                      match (String.Map.find_exn vctx list_name), result with
                      | (`List (x, _)), (`List (y, _)) ->
                         let retained, removed = List.partition_tf x ~f:(List.mem y) in
                         List.map retained ~f:(fun i -> filter_example lambda_name (i :> const_app) true)
                         @ List.map removed ~f:(fun i -> filter_example lambda_name (i :> const_app) false)
                         |> List.map ~f:(fun ex -> ex, vctx')
                      | _ -> [])
    |> List.concat
    |> List.unzip
  in

  match signature spec.examples with
  | Arrow_t (arg_typs, List_t res_elem_typ) ->
     let arg_names = List.map arg_typs ~f:(fun _ -> fresh_name ()) in
     let target_args = List.zip_exn arg_names arg_typs in

     let tctx = ctx_merge (get_example_typ_ctx spec.examples arg_names) spec.tctx in
     let vctxs = List.map2_exn (get_example_value_ctxs spec.examples arg_names) spec.vctxs
                               ~f:(fun ivctx ovctx -> ctx_merge ivctx ovctx) in

     (* Select all list arguments which are a superset of the result
     for every example and a strict superset of the result for at
     least one example. *)
     tctx
     |> String.Map.filter
          ~f:(fun ~key:name ~data:typ ->
              match typ with
              | List_t elem_typ when elem_typ = res_elem_typ ->
                 List.for_all2_exn vctxs spec.examples
                                   ~f:(fun vctx (_, result) ->
                                       match (String.Map.find_exn vctx name), result with
                                       | (`List (x, _)), (`List (y, _)) -> Util.superset x y
                                       | (`Apply _), (`List _) -> true
                                       | _ -> solve_error "Examples do not have a consistent type.")
                 && List.exists2_exn vctxs spec.examples
                                     ~f:(fun vctx (_, result) ->
                                         match (String.Map.find_exn vctx name), result with
                                         | (`List (x, _)), (`List (y, _)) -> Util.strict_superset x y
                                         | (`Apply _), (`List _) -> false
                                         | _ -> solve_error "Examples do not have a consistent type.")
              | _ -> false)
     |> String.Map.keys
     |> List.map ~f:(fun list_name ->
                     let lambda_tctx = String.Map.remove tctx list_name in
                     let lambda_name = fresh_name ~prefix:"f" () in
                     let lambda_examples,
                         lambda_vctxs = filter_examples spec.examples vctxs lambda_name list_name in
                     let target lambda =
                       spec.target (`Lambda (target_args, Bool_t, `Op (Filter, [`Id list_name; lambda]))) in
                     create_spec target lambda_examples lambda_tctx lambda_vctxs spec.fold_depth)
     |> List.filter ~f:(fun spec -> match spec.examples with
                                    | [] -> false
                                    | _ -> true)
  | _ -> []

(* Foldl and foldr are the most general functions. They are
appropriate whenever one of the inputs is a list. If another of the
arguments can act as a base case, it is used. Otherwise, a default
base case is used for each type. *)
let fold_bodies (spec: spec) : spec list =
  let extract_base_cases (examples: example list) : const list =
    let base_cases =
      examples
      |> List.filter_map ~f:(fun (`Apply (_, inputs), result) ->
                             match inputs with
                             | [`List ([], _)] -> Some result
                             | _ -> None)
      |> List.dedup
    in
    match base_cases with
    | [] -> (match signature examples with
             | Arrow_t (_, Num_t) -> [`Num 0; `Num 1]
             | Arrow_t (_, Bool_t) -> [`Bool true; `Bool false]
             | Arrow_t (_, List_t elem_typ) -> [`List ([], elem_typ)]
             | _ -> solve_error "Examples do not represent a function.")
    | [base] -> [base]
    | _::_::_ -> solve_error "Examples contain multiple base cases."
  in

  let remove_names ctx list_expr init_expr =
    let ctx' = match list_expr with
      | `Id list_name -> String.Map.remove ctx list_name
      | _ -> ctx
    in
    match init_expr with
      | `Id init_name -> String.Map.remove ctx' init_name
      | _ -> ctx'
  in

  let fold_examples examples vctxs lambda_name list_expr init_expr =
    let apply_lambda acc elem : example_lhs =
      `Apply (`Id lambda_name, [acc; (elem :> const_app)])
    in
    let lookup ctx id : const_app = match id with
      | `Id name -> String.Map.find_exn ctx name
      | `Bool x -> `Bool x
      | `Num x -> `Num x
      | `List x -> `List x
      | _ -> solve_error "Bad constant."
    in
    List.zip_exn vctxs examples
    |> List.filter_map ~f:(fun (vctx, (_, result)) ->
                           let vctx' = remove_names vctx list_expr init_expr in
                           let init = lookup vctx init_expr in
                           match lookup vctx list_expr with
                           | `List (x::xs, _) ->
                              let (foldr_example: example) =
                                (List.fold_right xs
                                                 ~init:(apply_lambda init x)
                                                 ~f:(fun e a -> apply_lambda (a :> const_app) e)),
                                result in
                              let (foldl_example: example) =
                                (List.fold_left xs
                                                ~init:(apply_lambda init x)
                                                ~f:(fun a e -> apply_lambda (a :> const_app) e)),
                                result in
                              Some (foldr_example, foldl_example, vctx')
                           | _ -> None)
    |> Util.unzip3
  in

  match signature spec.examples with
  | Arrow_t (arg_typs, res_typ) when spec.fold_depth > 0 ->
     let arg_names = List.map arg_typs ~f:(fun _ -> fresh_name ()) in
     let target_args = List.zip_exn arg_names arg_typs in

     let tctx = ctx_merge (get_example_typ_ctx spec.examples arg_names) spec.tctx in
     let vctxs = List.map2_exn (get_example_value_ctxs spec.examples arg_names) spec.vctxs
                               ~f:(fun ivctx ovctx -> ctx_merge ivctx ovctx) in

     let init_names =
       tctx
       |> String.Map.filter ~f:(fun ~key:_ ~data:typ -> typ = res_typ)
       |> String.Map.keys
     in

     let list_names =
       tctx
       |> String.Map.filter ~f:(fun ~key:_ ~data:typ -> match typ with List_t _ -> true | _ -> false)
       |> String.Map.keys
     in

     (* Each list argument needs to be paired with an initial
     value. The initial value must be an expression, since it could be
     either an argument or a constant. *)
     list_names
     |> List.concat_map ~f:(fun list_name ->
                            let base_cases = extract_base_cases spec.examples in
                            let list_expr = ((`Id list_name) :> expr) in
                            List.map init_names ~f:(fun init_name -> list_expr, `Id init_name)
                            @ List.map base_cases ~f:(fun base_case -> list_expr, (base_case :> expr)))

     (* Take each argument pair and generate a body for each of foldl, foldr. *)
     |> List.concat_map
          ~f:(fun ((list_expr: expr), init_expr) ->
              let lambda_tctx = remove_names tctx list_expr init_expr in
              let lambda_name = fresh_name ~prefix:"f" () in
              let foldr_examples, foldl_examples, lambda_vctxs =
                fold_examples spec.examples vctxs lambda_name list_expr init_expr in
              let foldr_target lambda =
                spec.target (`Lambda (target_args, res_typ, `Op (Fold, [list_expr; lambda; init_expr]))) in
              let foldl_target lambda =
                spec.target (`Lambda (target_args, res_typ, `Op (Foldl, [list_expr; lambda; init_expr]))) in
              [ create_spec foldr_target foldr_examples lambda_tctx lambda_vctxs (spec.fold_depth - 1);
                create_spec foldl_target foldl_examples lambda_tctx lambda_vctxs (spec.fold_depth - 1); ])
     |> List.filter ~f:(fun spec -> match spec.examples with
                                    | [] -> false
                                    | _ -> true)
  | _ -> []

let solve_catamorphic_looped ?(init=[]) ?(start_depth=3) (examples: example list) : program =
  let target_name = get_target_name examples in
  let initial_spec = create_spec (fun lambda -> `Define (target_name, lambda))
                                 examples
                                 String.Map.empty
                                 (List.map examples ~f:(fun _ -> String.Map.empty))
                                 1
  in

  let rec generate_specs (specs: spec list) : spec list =
    match specs with
    | [] -> []
    | specs ->
       let leaf_nodes, internal_nodes =
         List.partition_map specs
                            ~f:(fun parent ->
                                let children = []
                                               @ (map_bodies parent)
                                               @ (filter_bodies parent)
                                               @ (fold_bodies parent) in
                                match children with
                                | [] -> `Fst parent
                                | children -> `Snd children) in
       leaf_nodes @ (generate_specs (List.concat internal_nodes))
  in

  let specs = generate_specs [initial_spec] in

  let _ = List.iter specs
                    ~f:(fun spec ->
                        Printf.printf "%s %s\n"
                                      (expr_to_string (spec.target (`Id "lambda")))
                                      (String.concat ~sep:" " (List.map ~f:example_to_string spec.examples))) in

  let depth = ref start_depth in
  try
    while true do
      let solution_m =
        List.find_map specs
                      ~f:(fun spec ->
                          match signature spec.examples with
                          | Arrow_t (lambda_arg_typs, lambda_res_typ) ->
                             let lambda_args = List.map lambda_arg_typs ~f:(fun typ -> (fresh_name ()), typ) in
                             let lambda expr = `Lambda (lambda_args, lambda_res_typ, expr) in
                             let verify expr =
                               let prog = [spec.target (lambda expr)] in
                               let _ = Printf.printf "%s\n" (List.to_string prog ~f:expr_to_string) in
                               match Verify.verify_examples prog examples with
                               | true -> Verify.Valid
                               | false -> Verify.Invalid
                             in
                             let init' = (String.Map.to_alist spec.tctx
                                          |> List.map ~f:(fun (name, typ) -> `Id name, typ))
                                         @ (List.map init ~f:(fun expr -> expr, typeof_expr (Util.empty_ctx ()) expr))
                                         @ (List.map lambda_args ~f:(fun (name, typ) -> `Id name, typ)) in
                             (match solve_verifier ~max_depth:(Some !depth) init' verify with
                              | Some expr -> Some [spec.target (lambda expr)]
                              | None -> None)
                          | _ -> solve_error "Lambda examples do not represent a function.") in
      Int.incr depth;
      match solution_m with
      | Some solution -> raise (Solved solution)
      | None -> ()
    done;
    solve_error "Exited solve loop without finding a solution."
  with
  | Solved prog -> prog
