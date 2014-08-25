open Core.Std
open Printf
open Ast
open Infer
open Util

(** A build set is a mapping from integers to sets of (expression, type) pairs. *)
module BuildSet = struct
  module IntMap = Map.Make (Int)
  module TypedExpr =
    struct
      type t = expr * typ with sexp, compare
    end
  module TypedExprSet = Set.Make (TypedExpr)
  type t = TypedExprSet.t IntMap.t

  let empty = IntMap.empty

  let add set texpr =
    IntMap.change set
                  (let expr, _ = texpr in size expr)
                  (function
                    | None -> Some (TypedExprSet.singleton texpr)
                    | Some xs -> Some (TypedExprSet.add xs texpr))
                  
  let mem set texpr =
    match IntMap.find set (let expr, _ = texpr in size expr) with
    | Some size_set -> TypedExprSet.mem size_set texpr
    | None -> false

  let select set size typ =
    match IntMap.find set size with
    | Some exprs -> 
       TypedExprSet.filter exprs ~f:(fun (_, typ') -> implements typ typ')
       |> TypedExprSet.to_list
    | None -> []
end

type spec = {
  target: expr -> expr -> expr;
  examples: example list;
  signature: typ;
  tctx: typ Ctx.t;
  vctxs: expr Ctx.t list;
  fold_depth: int;
}

exception SolveError of string

exception Solved of expr
exception SolvedTarget of (expr -> expr)
exception TimedOut

let solve_error msg = raise (SolveError msg)

(** Extract the name of the target function from a list of examples. *)
let get_target_name (examples: example list) : id =
  let target_names = 
    List.map examples ~f:(fun ex -> match ex with
                                    | (`Apply (`Id n, _)), _ -> n
                                    | _ -> solve_error "Malformed example.")
  in
  match target_names with
  | [] -> solve_error "Example list is empty."
  | name::rest -> if List.for_all rest ~f:((=) name) then name
                  else solve_error "Multiple target names in example list."

(** Infer a function signature from input/output examples. *)
let signature ?(ctx=Ctx.empty ()) (examples: example list) : typ =
  let inputs, results = List.unzip examples in
  let res_typ =
    match typ_of_expr (infer ctx (`List results)) with
    | App_t ("list", [t]) -> t
    | t -> solve_error (sprintf "Unexpected result type: %s" (typ_to_string t))
  in
  let typ =
    match inputs with
    | (`Apply (_, args))::_ -> 
       let num_args = List.length args in
       Arrow_t (List.range 0 num_args |> List.map ~f:(fun _ -> fresh_free 0), res_typ)
    | _ -> solve_error (sprintf "Malformed example inputs.")
  in
  let ctx =
    let name = get_target_name examples in
    Ctx.bind ctx name typ
  in
  List.iter inputs ~f:(fun input -> let _ = infer ctx input in ()); typ

let solve_verifier ?(max_depth=None) 
                   (init: (expr * typ) list) 
                   (verify: expr -> Verify.status) : expr option =
  (* Create initial context containing the expressions in init. *)
  let ctx = List.fold init
                      ~init:(Ctx.empty ())
                      ~f:(fun ctx (expr, typ) -> 
                          match expr with
                          | `Id name -> Ctx.bind ctx name typ
                          | _ -> ctx)
  in

  (* Create a mutable set to hold expressions sorted by size. *)
  let build = ref (BuildSet.empty) in
  let i = ref 1 in

  (** Check all expressions using the oracle. Raise a Solve exception
  if a solution is found. *)
  let check_exprs ?allow_const:(ac = false) (exprs: expr list) : unit =
    build :=
      List.fold exprs
                ~init:(!build)
                ~f:(fun build' expr ->
                    (* printf "%s\n" (expr_to_string expr); *)
                    try
                      let typ = typ_of_expr (infer ctx expr) in
                      (* Attempt to simplify the
                    expression. Simplification can fail if the
                    expression is found to contain an illegal
                    operation. *)
                      match Rewrite.simplify expr with
                      | Some simple_expr ->
                         (* Check whether the expression is already in
                       the build set, meaning that it has already been
                       checked. *)
                         let typed_expr = simple_expr, typ in
                         if BuildSet.mem build' typed_expr
                         then build'
                         else (match verify expr with
                               | Verify.Valid -> raise (Solved expr)
                               | Verify.Invalid ->
                                  if (Rewrite.is_constant simple_expr) && (not ac)
                                  then build'
                                  else BuildSet.add build' typed_expr
                               | Verify.Error -> build')
                      | None -> build'
                    with Infer.TypeError _ -> build'
                   )
  in

  let rec select_children types sizes : expr list list =
    match types, sizes with
    | [], [] -> []
    | [typ], [size] ->
       BuildSet.select !build size typ |> List.map ~f:(fun (e, _) -> [Rewrite.complicate e])
    | t::ts, s::ss ->
       (* Select all possible arguments for this position using the
       type predicate and size parameters. *)
       let arg_choices = 
         BuildSet.select !build s t |> List.map ~f:(fun (e, t) -> Rewrite.complicate e, t) in

       let rec replace_quant name typ qtyp = match qtyp with
         | Var_t {contents = Quant name'} when name = name' -> typ
         | Var_t {contents = Link qtyp'} -> replace_quant name typ qtyp'
         | Arrow_t (args, ret) -> 
            Arrow_t (List.map args ~f:(replace_quant name typ), replace_quant name typ ret)
         | App_t (const, args) -> App_t (const, List.map ~f:(replace_quant name typ) args)
       in

       (* For each choice of argument, select all possible remaining arguments. *)
       List.map arg_choices
                ~f:(fun (arg, arg_typ) -> 
                    (* If the current argument is polymorphic, set all
                    other instances of the type variable to the
                    selected type. *)
                    let ts = match t with
                      | App_t ("list", [Var_t {contents = Quant name}]) -> 
                         List.map ts ~f:(replace_quant name arg_typ)
                      | Var_t {contents = Quant name} -> List.map ts ~f:(replace_quant name arg_typ)
                      | _ -> ts
                    in
                    select_children ts ss |> List.map ~f:(fun args -> arg::args))
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
        List.iter Op.metadata_by_op
                  ~f:(fun (op, meta) ->
                      let Arrow_t (inputs, _) = meta.Op.typ in
                      List.iter (arg_sizes !i (Op.arity op))
                                ~f:(fun sizes ->
                                    select_children inputs sizes
                                    |> List.map ~f:(fun args -> `Op (op, args))
                                    |> check_exprs));
        Int.incr i;
        match max_depth with
        | Some max -> if !i >= max then raise TimedOut else ()
        | None -> ()
      done;
      solve_error "Completed solve loop without finding solution.";
    end
  with
  | Solved expr -> Some expr
  | TimedOut -> None

let solve ?(init=[])
          ?(max_depth=None)
          (examples: example list)
          (constraints: constr list) : (expr -> expr) option =
  (* Extract the name of the target function from the examples. *)
  let name = get_target_name examples in
  let sig_ = signature examples in
  match sig_ with
  | Arrow_t (input_types, _) ->
     let args = List.map input_types ~f:(fun typ -> (Fresh.name "x"), typ) in
     let arg_names = List.map args ~f:(fun (name, _) -> name) in
     let target body expr = `Let (name, `Lambda (arg_names, body), expr) in

     (* Generate the set of initial expressions from the argument
     names and any provided expressions. *)
     let initial = (List.map init ~f:(fun expr -> expr, typ_of_expr (infer (Ctx.empty ()) expr)))
                   @ (List.map args ~f:(fun (name, typ) -> `Id name, typ)) in

     (* Generate an oracle function from the examples. *)
     let verify body = Verify.verify examples constraints (target body) in

     (match solve_verifier ~max_depth:max_depth initial verify with
      | Some body -> Some (target body)
      | None -> None)
  | _ -> solve_error "Examples do not represent a function."

let get_example_typ_ctx (examples: example list) (arg_names: string list) : typ Ctx.t =
  match signature examples with
  | Arrow_t (arg_typs, _) ->
     let name_typ_pairs = List.zip_exn arg_names arg_typs in
     Ctx.of_alist_exn name_typ_pairs
  | _ -> solve_error "Examples do not represent a function."

let get_example_value_ctxs (examples: example list) (arg_names: string list) : expr Ctx.t list =
  List.map examples ~f:(fun ((`Apply (_, inputs)), _) ->
                        let name_value_pairs = List.zip_exn arg_names inputs in
                        Ctx.of_alist_exn name_value_pairs)

let ctx_merge outer_ctx inner_ctx =
  Ctx.merge outer_ctx inner_ctx ~f:(fun ~key:_ value ->
                                    match value with
                                    | `Both (_, ictx_v) -> Some ictx_v
                                    | `Left octx_v -> Some octx_v
                                    | `Right ictx_v -> Some ictx_v)

let const_base_cases typ =
  match typ with
  | Const_t Num_t -> [`Num 0; `Num 1]
  | Const_t Bool_t -> [`Bool true; `Bool false]
  | App_t ("list", [_]) -> [`List []]
  | _ -> solve_error "Not a constant type."

let create_spec target examples signature tctx vctxs fold_depth =
  { target = target; examples = examples; signature = signature;
    tctx = tctx; vctxs = vctxs; fold_depth = fold_depth; }

let dedup_examples spec =
  let examples, vctxs = 
    List.zip_exn spec.examples spec.vctxs
    |> List.dedup ~compare:(fun (e1, _) (e2, _) -> compare_example e1 e2)
    |> List.unzip
  in
  { spec with examples = examples; vctxs = vctxs; }

(* Map is an appropriate implementation when one of the inputs is a
   list and the output is a list of the same length. *)
let map_bodies (spec: spec) : spec list =
  let map_example lambda_name input result =
    (`Apply (`Id lambda_name, [input])), result
  in
  let map_examples examples vctxs lambda_name list_name =
    List.map2_exn vctxs examples
                  ~f:(fun vctx (_, result) ->
                      let vctx' = Ctx.unbind vctx list_name in
                      match (Ctx.lookup_exn vctx list_name), result with
                      | `List x, `List y ->
                         List.map2_exn x y ~f:(fun i o -> (map_example lambda_name i o), vctx')
                      | _ -> [])
    |> List.concat
    |> List.unzip
  in

  if spec.examples = [] then [] else
    match signature spec.examples with
    | Arrow_t (arg_typs, App_t ("list", [res_elem_typ])) ->
       (* Extract the name of the target function and generate the
        names of the target function's arguments. The types of the
        target function's arguments are available in the type
        signature. *)
       let arg_names = List.map arg_typs ~f:(fun _ -> Fresh.name "x") in

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
       |> Ctx.filter_mapi
            ~f:(fun ~key:name ~data:typ ->
                match typ |> normalize with
                | App_t ("list", [elem_typ]) ->
                   if List.for_all2_exn vctxs spec.examples
                                        ~f:(fun vctx (_, result) ->
                                            match Ctx.lookup_exn vctx name, result with
                                            | `List x, `List y -> List.length x = List.length y
                                            | `Apply _, `List _ -> true
                                            | _ -> solve_error "Examples do not have a consistent type.")
                      && List.exists2_exn vctxs spec.examples
                                          ~f:(fun vctx (_, result) ->
                                              match (Ctx.lookup_exn vctx name), result with
                                              | `List x, `List y -> x <> y
                                              | `Apply _, `List _ -> false
                                              | _ -> solve_error "Examples do not have a consistent type.")
                   then Some elem_typ
                   else None
                | _ -> None)
       |> Ctx.to_alist

       (* Generate a list of new specifications from the selected names. *)
       |> List.map ~f:(fun (list_name, input_elem_typ) ->
                       let lambda_tctx = Ctx.unbind tctx list_name in
                       let lambda_name = Fresh.name "f" in
                       let lambda_examples,
                           lambda_vctxs = map_examples spec.examples vctxs lambda_name list_name in
                       let lambda_signature = Arrow_t ([input_elem_typ], res_elem_typ) in
                       let target lambda =
                         spec.target (`Lambda (arg_names, `Apply (`Id "map", [`Id list_name; lambda]))) in
                       create_spec target lambda_examples lambda_signature lambda_tctx lambda_vctxs spec.fold_depth)
       |> List.map ~f:(dedup_examples)
    | _ -> []

let filter_bodies (spec: spec) : spec list =
  let filter_example lambda_name input result : example =
    (`Apply (`Id lambda_name, [input])), `Bool result
  in
  let filter_examples examples vctxs lambda_name list_name =
    List.map2_exn vctxs examples
                  ~f:(fun vctx (_, result) ->
                      let vctx' = Ctx.unbind vctx list_name in
                      match Ctx.lookup_exn vctx list_name, result with
                      | `List x, `List y ->
                         let retained, removed = List.partition_tf x ~f:(List.mem y) in
                         List.map retained ~f:(fun i -> filter_example lambda_name i true)
                         @ List.map removed ~f:(fun i -> filter_example lambda_name i false)
                         |> List.map ~f:(fun ex -> ex, vctx')
                      | _ -> [])
    |> List.concat
    |> List.unzip
  in

  if spec.examples = [] then [] else
    match signature spec.examples with
    | Arrow_t (arg_typs, App_t ("list", [res_elem_typ])) ->
       let arg_names = List.map arg_typs ~f:(fun _ -> Fresh.name "x") in
       let tctx = ctx_merge (get_example_typ_ctx spec.examples arg_names) spec.tctx in
       let vctxs = List.map2_exn (get_example_value_ctxs spec.examples arg_names) spec.vctxs
                                 ~f:(fun ivctx ovctx -> ctx_merge ivctx ovctx) in

       (* Select all list arguments which are a superset of the result
        for every example and a strict superset of the result for at
        least one example. *)
       tctx
       |> Ctx.filter_mapi
            ~f:(fun ~key:name ~data:typ ->
                match typ |> normalize with
                | App_t ("list", [elem_typ]) when elem_typ = res_elem_typ ->
                   if List.for_all2_exn vctxs spec.examples
                                        ~f:(fun vctx (_, result) ->
                                            match (Ctx.lookup_exn vctx name), result with
                                            | `List x, `List y -> Util.superset x y
                                            | `Apply _, `List _ -> true
                                            | _ -> solve_error "Examples do not have a consistent type.")
                      && List.exists2_exn vctxs spec.examples
                                          ~f:(fun vctx (_, result) ->
                                              match (Ctx.lookup_exn vctx name), result with
                                              | `List x, `List y -> Util.strict_superset x y
                                              | `Apply _, `List _ -> false
                                              | _ -> solve_error "Examples do not have a consistent type.")
                   then Some elem_typ
                   else None
                | _ -> None)
       |> Ctx.to_alist
       |> List.map ~f:(fun (list_name, input_elem_typ) ->
                       let lambda_tctx = Ctx.unbind tctx list_name in
                       let lambda_name = Fresh.name "f" in
                       let lambda_examples,
                           lambda_vctxs = filter_examples spec.examples vctxs lambda_name list_name in
                       let lambda_signature = Arrow_t ([input_elem_typ], Const_t Bool_t) in
                       let target lambda =
                         spec.target (`Lambda (arg_names, `Apply (`Id "filter", [`Id list_name; lambda]))) in
                       create_spec target lambda_examples lambda_signature lambda_tctx lambda_vctxs spec.fold_depth)
       |> List.map ~f:(dedup_examples)
    | _ -> []

(* Foldl and foldr are the most general functions. They are
 appropriate whenever one of the inputs is a list. If another of the
 arguments can act as a base case, it is used. Otherwise, a default
 base case is used for each type. *)
let fold_bodies (spec: spec) : spec list =
  let extract_base_cases (examples: example list) : expr list =
    let base_cases =
      examples
      |> List.filter_map ~f:(function
                              | (`Apply (_, [`List []]), result) -> Some result
                              | _ -> None)
      |> List.dedup
    in
    match base_cases with
    | [] -> (match signature examples with
             | Arrow_t (_, Const_t Num_t) -> [`Num 0; `Num 1]
             | Arrow_t (_, Const_t Bool_t) -> [`Bool true; `Bool false]
             | Arrow_t (_, App_t ("list", [_])) -> [`List []]
             | _ -> solve_error "Examples do not represent a function.")
    | [base] -> [base]
    | _::_::_ -> solve_error "Examples contain multiple base cases."
  in

  let remove_names ctx list_name init_expr =
    let ctx' = Ctx.unbind ctx list_name in
    match init_expr with
      | `Id init_name -> Ctx.unbind ctx' init_name
      | _ -> ctx'
  in

  let fold_examples examples vctxs lambda_name list_name init_expr =
    let list_expr = `Id list_name in
    let apply_lambda acc elem = `Apply (`Id lambda_name, [acc; elem]) in
    let lookup ctx id : expr = match id with
      | `Id name -> Ctx.lookup_exn ctx name
      | `Bool x -> `Bool x
      | `Num x -> `Num x
      | `List x -> `List x
      | _ -> solve_error "Bad constant."
    in
    List.zip_exn vctxs examples
    |> List.filter_map 
         ~f:(fun (vctx, (_, result)) ->
             let vctx' = remove_names vctx list_name init_expr in
             match lookup vctx init_expr, lookup vctx list_expr with
             | ((`List _) as init), `List (x::xs)
             | ((`Bool _) as init), `List (x::xs)
             | ((`Num _) as init), `List (x::xs) ->
                let example = List.fold_right xs
                                              ~init:(apply_lambda init x)
                                              ~f:(fun e a -> apply_lambda a e),
                              result in
                Some (example, example, vctx')
             | _ -> None)
    |> Util.unzip3
  in

  if spec.examples = [] then [] else
    match signature spec.examples with
    | Arrow_t (arg_typs, res_typ) when spec.fold_depth > 0 ->
       let arg_names = List.map arg_typs ~f:(fun _ -> Fresh.name "x") in
       let tctx = ctx_merge (get_example_typ_ctx spec.examples arg_names) spec.tctx in
       let vctxs = List.map2_exn (get_example_value_ctxs spec.examples arg_names) spec.vctxs
                                 ~f:(fun ivctx ovctx -> ctx_merge ivctx ovctx) in

       let lists =
         tctx
         |> Ctx.filter_mapi ~f:(fun ~key:_ ~data:typ -> 
                                match typ |> normalize with
                                | App_t ("list", [elem_typ]) -> Some elem_typ 
                                | _ -> None)
         |> Ctx.to_alist
       in

       let init_exprs =
         tctx
         |> Ctx.filter ~f:(fun ~key:_ ~data:typ -> implements res_typ typ)
         |> Ctx.keys
         |> List.map ~f:(fun name -> `Id name)
       in

       let base_exprs = extract_base_cases spec.examples in

       (* Each list argument needs to be paired with an initial
        value. The initial value must be an expression, since it could
        be either an argument or a constant. *)
       List.cartesian_product lists (init_exprs @ base_exprs)

       (* Take each argument pair and generate a body for each of foldl, foldr. *)
       |> List.concat_map
            ~f:(fun ((list_name, input_elem_typ), init_expr) ->
                let list_expr = `Id list_name in
                let lambda_tctx = remove_names tctx list_name init_expr in
                let lambda_name = Fresh.name "f"  in
                let lambda_signature = Arrow_t ([res_typ; input_elem_typ], res_typ) in
                let foldr_examples, foldl_examples, lambda_vctxs =
                  fold_examples spec.examples vctxs lambda_name list_name init_expr in
                let foldr_target lambda =
                  spec.target (`Lambda (arg_names, `Apply (`Id "foldr", [list_expr; lambda; init_expr]))) in
                let foldl_target lambda =
                  spec.target (`Lambda (arg_names, `Apply (`Id "foldl", [list_expr; lambda; init_expr]))) in
                [ create_spec foldr_target foldr_examples lambda_signature lambda_tctx lambda_vctxs 
                              (spec.fold_depth - 1);
                  create_spec foldl_target foldl_examples lambda_signature lambda_tctx lambda_vctxs 
                              (spec.fold_depth - 1); ])
       |> List.map ~f:dedup_examples
    | _ -> []

let solve_catamorphic_looped ?(init=[]) ?(start_depth=3) (examples: example list) : expr -> expr =
  let target_name = get_target_name examples in
  let initial_spec = create_spec (fun body expr -> `Let (target_name, body, expr))
                                 examples
                                 (signature examples)
                                 (Ctx.empty ())
                                 (List.map examples ~f:(fun _ -> Ctx.empty ()))
                                 3
  in

  let rec generate_specs (specs: spec list) : spec list =
    match specs with
    | [] -> []
    | specs ->
       let child_specs = List.concat_map specs 
                                         ~f:(fun parent ->
                                             (map_bodies parent)
                                             @ (filter_bodies parent)
                                             @ (fold_bodies parent))
       in
       specs @ (generate_specs child_specs)
  in

  let specs = generate_specs [initial_spec] in

  (* let _ = List.iter specs *)
  (*                   ~f:(fun spec -> *)
  (*                       Printf.printf "%s %s\n" *)
  (*                                     (expr_to_string (spec.target (`Id "lambda") (`Id "x"))) *)
  (*                                     (String.concat ~sep:" " (List.map ~f:example_to_string spec.examples)))  *)
  (* in *)
  
  let depth = ref start_depth in
  try
    while true do
      let solution_m =
        List.find_map specs
                      ~f:(fun spec ->
                          match spec.signature with
                          | Arrow_t (lambda_arg_typs, _) ->
                             let lambda_args = List.map lambda_arg_typs ~f:(fun _ -> Fresh.name "x") in
                             let lambda body = `Lambda (lambda_args, body) in
                             let verify expr =
                               (* let _ = Printf.printf "%s\n" (List.to_string prog ~f:expr_to_string) in *)
                               match Verify.verify_examples (spec.target (lambda expr)) examples with
                               | true -> Verify.Valid
                               | false -> Verify.Invalid
                             in
                             let init' = (Ctx.to_alist spec.tctx
                                          |> List.map ~f:(fun (name, typ) -> `Id name, typ))
                                         @ (List.map init ~f:(fun expr -> 
                                                              expr, typ_of_expr (infer (Ctx.empty ()) expr)))
                                         @ (List.map2_exn lambda_args 
                                                          lambda_arg_typs 
                                                          ~f:(fun name typ -> `Id name, typ)) in
                             (match solve_verifier ~max_depth:(Some !depth) init' verify with
                              | Some expr -> Some (spec.target (lambda expr))
                              | None -> None)
                          | _ -> solve_error "Lambda examples do not represent a function.") in
      Int.incr depth;
      match solution_m with
      | Some solution -> raise (SolvedTarget solution)
      | None -> ()
    done;
    solve_error "Exited solve loop without finding a solution."
  with
  | SolvedTarget target -> target
