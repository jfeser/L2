open Core.Std
open Printf

open Ast
open Infer
open Structure
open Util

module Typ = struct type t = Ast.typ with compare, sexp end
module TypedExpr = struct type t = typed_expr end
module TypMemoizer = Sstream.Memoizer (Typ) (TypedExpr)

module SimpleMemoizer =
  Sstream.Memoizer (struct type t = typed_expr list with compare, sexp end) (Expr)

type config = {
  verbosity: int;
  untyped: bool;
  deduction: bool;
  infer_base: bool;
  max_exhaustive_depth: int;
}

let default_config = {
  verbosity=0;
  untyped=false;
  deduction=true;
  infer_base=true;
  max_exhaustive_depth=7;
}

let default_init =
  ["0"; "1"; "[]"; "#f"]
  |> List.map ~f:(fun str -> parse_expr str |> infer (Ctx.empty ()))

let matrix_of_texpr_list ~size (texprs: typed_expr list) : typed_expr Sstream.matrix =
  let init_sizes = List.map texprs ~f:(fun e -> e, size e) in
  let max_size =
    List.fold_left init_sizes ~init:0 ~f:(fun x (_, y) -> if x > y then x else y) 
  in
  List.range ~stop:`inclusive 1 max_size
  |> List.map ~f:(fun s ->
      List.filter_map init_sizes ~f:(fun (e, s') ->
          if s = s' then Some e else None))
  |> Sstream.of_list

let arrow_error () = failwith "Operator is not of type Arrow_t."

let rec simple_enumerate
    ?(memo=SimpleMemoizer.empty ())
    init
  : expr Sstream.matrix =
  let open Sstream in
  let init_matrix =
    matrix_of_texpr_list ~size:(fun e -> Expr.cost (expr_of_texpr e)) init
    |> map_matrix ~f:(expr_of_texpr)
  in

  let args_matrix num_args =
    let choose prev_args =
      slazy (fun () ->
          map_matrix (SimpleMemoizer.get memo init (fun () -> simple_enumerate ~memo:memo init))
            ~f:(fun arg -> prev_args @ [arg]))
    in
    match List.range 0 num_args with
    | _::xs -> (List.fold_left xs ~init:choose ~f:(fun acc _ -> compose acc choose)) []
    | [] -> failwith "Cannot generate args matrix with no arguments."
  in

  let callable_matrix apply_callable callable_typ = match callable_typ with
    | Arrow_t (arg_typs, _) ->
      let num_args = List.length arg_typs in
      let prefix = repeat_n num_args [] in
      let matrix = slazy (fun () -> map_matrix (args_matrix num_args) ~f:apply_callable) in
      concat prefix matrix
    | _ -> arrow_error ()
  in
  let op_matrix op op_typ =
    callable_matrix (fun args -> `Op (op, args)) op_typ
  in
  let apply_matrix func func_typ =
    callable_matrix (fun args -> `Apply (func, args)) func_typ
  in

  let (op_matrices : expr matrix list) =
    List.map Expr.Op.all ~f:(fun op -> 
        let meta = Expr.Op.meta op in 
        op_matrix op meta.Expr.Op.typ)
  in

  let (apply_matrices : expr matrix list) =
    List.filter init ~f:(fun texpr ->
        match typ_of_expr texpr with
        | Arrow_t _ -> true
        | _ -> false)
    |> List.map ~f:(fun func -> apply_matrix (expr_of_texpr func) (typ_of_expr func))
  in
  merge (init_matrix::(op_matrices @ apply_matrices))

let rec enumerate
    ?(ops=Expr.Op.all)
    ?(memo=TypMemoizer.empty ())
    init 
    typ 
  : typed_expr Sstream.matrix =
  let open Sstream in

  (* Init is finite, so we can construct an init stream by breaking
     init into a list of size classes and returning that list as a
     stream. *)
  let init_matrix = 
    List.filter init ~f:(fun e -> is_unifiable typ (typ_of_expr e))
    |> matrix_of_texpr_list ~size:(fun e -> Expr.cost (expr_of_texpr e))
  in

  (* Generate an argument list matrix that conforms to the provided list of types. *)
  let args_matrix (arg_typs: typ list) =
    let choose (prev_args: typed_expr list) : (typed_expr list) matrix =
      (* Split the argument type list into the types of the arguments
         that have already been selected and the head of the list of
         remaining types (which will be the type of the current
         argument). *)
      let prev_arg_typs, (current_typ::_) =
        (* Instantiate the argument types in the same context. Free
           type variables should be shared across arguments. For example,
           when instantiating the argument types for equals: (a, a) ->
           bool, both a's should map to the same free type. *)
        let arg_typs' =
          let ctx = Ctx.empty () in
          List.map arg_typs ~f:(instantiate ~ctx:ctx 0)
        in
        List.split_n arg_typs' (List.length prev_args)
      in

      (* Unify the types of the previous arguments with the actual
         selected types. By the size effects of unify, this should fill
         in any type variables in the current type that have already been
         bound. *)
      let prev_selected_typs =
        let ctx = Ctx.empty () in
        List.map prev_args ~f:(fun arg -> instantiate ~ctx:ctx 0 (typ_of_expr arg))
      in
      List.iter2_exn prev_arg_typs prev_selected_typs ~f:unify_exn;

      let current_typ' = normalize (generalize (-1) current_typ) in

      (* Generate the argument matrix lazily so that it will not be
         created until the prefix classes are exhausted. *)
      slazy (fun () ->
          map_matrix
            (TypMemoizer.get memo current_typ' (fun () ->
                 enumerate ~memo:memo init current_typ'))
            ~f:(fun arg -> prev_args @ [arg]))
    in
    match arg_typs with
    | _::xs -> (List.fold_left xs ~init:choose ~f:(fun acc _ -> compose acc choose)) []
    | [] -> failwith "Cannot generate args matrix with no arguments."
  in

  let callable_matrix apply_callable callable_typ = match callable_typ with
    | Arrow_t (arg_typs, ret_typ) ->
      let prefix = repeat_n (List.length arg_typs) [] in
      let matrix = slazy (fun () -> map_matrix (args_matrix arg_typs) ~f:(apply_callable ret_typ)) in
      concat prefix matrix
    | _ -> arrow_error ()
  in
  let op_matrix op op_typ =
    callable_matrix (fun ret_typ args -> Op ((op, args), ret_typ)) op_typ
  in
  let apply_matrix func func_typ =
    callable_matrix (fun ret_typ args -> Apply ((func, args), ret_typ)) func_typ
  in

  (* The op stream is infinite, so it needs more careful handling. *)
  let op_matrices =
    List.map ops ~f:(fun op -> op, Expr.Op.meta op)
    (* Filter all operators that can return the correct type. *)
    |> List.filter ~f:(fun (_, meta) ->
        match meta.Expr.Op.typ with
        | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
        | _ -> arrow_error ())

    (* Unify the return type of the operator with the input type. By
       the side effects of unify, all the other free type variables in
       the operator type will reflect the substitution. Now we have
       correct types for the arguments. *)
    |> List.map ~f:(fun (op, meta) ->
        match instantiate 0 typ, instantiate 0 meta.Expr.Op.typ with
        | typ', (Arrow_t (_, ret_typ) as op_typ) ->
          unify_exn typ' ret_typ;
          op, normalize (generalize (-1) op_typ)
        | _ -> arrow_error ())

    (* Generate a matrix for each operator. *)
    |> List.map ~f:(fun (op, op_typ) -> op_matrix op op_typ)
  in

  let apply_matrices =
    init
    |> List.filter ~f:(fun texpr -> 
        match typ_of_expr texpr with
        | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
        | _ -> false)
    |> List.map ~f:(fun texpr ->
        match instantiate 0 typ, instantiate 0 (typ_of_expr texpr) with
        | typ', (Arrow_t (_, ret_typ) as func_typ) ->
          unify_exn typ' ret_typ;
          texpr, normalize (generalize (-1) func_typ)
        | _ -> arrow_error ())
    |> List.map ~f:(fun (func, func_typ) -> apply_matrix func func_typ)
  in
  merge (init_matrix::(op_matrices @ apply_matrices))
  |> map ~f:(List.filter ~f:(fun x ->
      let e = expr_of_texpr x in
      match Rewrite.simplify (List.map init ~f:expr_of_texpr) e with
      | Some e' -> Expr.cost e' >= Expr.cost e
      | None -> false))

let solve_single
    ?(init=[])
    ?(ops=Expr.Op.all)
    ?(verify=Verify.verify_examples ~ctx:(Ctx.empty ()))
    ~config
    (examples: example list) =
  let initial_spec =
    let target_name = Example.name examples in
    let target ctx expr =
      let body = Ctx.lookup_exn ctx target_name in
      `Let (target_name, body, expr)
    in
    { Spec.target;
      Spec.holes =
        Ctx.of_alist_exn [
          target_name, 
          { examples = List.map examples ~f:(fun ex -> ex, Ctx.empty ());
            signature = Example.signature examples;
            tctx = Ctx.empty ();
          };
        ];
      Spec.cost = 1;
    }
  in

  let generate_specs (specs: Spec.t list) : Spec.t list =
    List.concat_map specs ~f:(fun parent ->
        (Spec.map_bodies ~deduce_examples:config.deduction parent)
        @ (Spec.filter_bodies ~deduce_examples:config.deduction parent)
        @ (Spec.fold_bodies ~deduce_examples:config.deduction ~infer_base:config.infer_base parent)
        @ (Spec.foldt_bodies ~deduce_examples:config.deduction ~infer_base:config.infer_base parent)
        @ (Spec.recurs_bodies ~deduce_examples:config.deduction parent)
      )
  in

  let matrix_of_hole hole =
    let init' =
      (Ctx.to_alist hole.tctx |> List.map ~f:(fun (name, typ) -> Id (name, typ))) @ init
    in
    match hole.signature with
    | Arrow_t (arg_typs, ret_typ) ->
      let args = List.map arg_typs ~f:(fun typ -> Fresh.name "x", typ) in
      let arg_names, _ = List.unzip args in
      let init'' = init' @ (List.map args ~f:(fun (name, typ) -> Id (name, typ))) in
      if config.untyped then
        simple_enumerate init''
        |> Sstream.map_matrix ~f:(fun expr -> `Lambda (arg_names, expr))
      else
        enumerate init'' ret_typ
        |> Sstream.map_matrix ~f:(fun texpr -> `Lambda (arg_names, expr_of_texpr texpr))
    | typ ->
      if config.untyped then
        simple_enumerate init'
      else
        enumerate init' typ |> Sstream.map_matrix ~f:expr_of_texpr
  in

  let choose name hole ctx : (expr Ctx.t) Sstream.matrix =
    Sstream.map_matrix (matrix_of_hole hole) ~f:(Ctx.bind ctx name)
  in

  let solver_of_spec spec =
    let ctx_matrix = match Ctx.to_alist spec.Spec.holes with
      | [] -> failwith "Specification has no holes."
      | (name, hole)::hs ->
        (List.fold_left hs
           ~init:(choose name hole)
           ~f:(fun matrix (name', hole') ->
               Sstream.compose matrix (choose name' hole')))
          (Ctx.empty ())
    in
    ctx_matrix
    |> Sstream.map_matrix 
      ~f:(fun ctx -> 
          let target = spec.Spec.target ctx in
          log config.verbosity 2 (sprintf "Examined %s." (Expr.to_string (target (`Id "_"))));
          if verify target examples then Some target else None)
  in

  (* Search a spec up to a specified maximum depth. *)
  let search max_depth spec : (expr -> expr) option =
    let solver = solver_of_spec spec in
    let rec search' depth : (expr -> expr) option =
      if depth >= max_depth 
      then begin
        log config.verbosity 1 (sprintf "Searched %s to depth %d." (Spec.to_string spec) depth);
        None 
      end else
        let row = Sstream.next solver in
        match List.find_map row ~f:ident with
        | Some result -> Some result
        | None -> search' (depth + 1)
    in search' 0
  in

  let rec search_unbounded depth specs =
    match List.find_map specs ~f:(search depth) with
    | Some result -> result
    | None ->
      if depth >= config.max_exhaustive_depth then
        search_unbounded 1 (generate_specs specs)
      else
        search_unbounded (depth + 1) specs
  in
  search_unbounded 1 [initial_spec]

let solve ?(config=default_config) ?(bk=[]) ?(init=default_init) examples =
  (* Check examples. *)
  (if not (List.map examples ~f:(fun ex -> ex, Ctx.empty ()) |> Example.check)
   then failwith "Examples do not represent a function.");

  let tctx =
    List.fold_left bk ~init:(Ctx.empty ()) ~f:(fun ctx (name, impl) ->
        Ctx.bind ctx name (typ_of_expr (infer ctx impl)))
  in
  let vctx =
    List.fold_left bk ~init:Eval.stdlib_vctx
      ~f:(fun ctx (name, impl) ->
          Ctx.bind ctx name (`Closure (impl, ctx)))
  in

  let init =
    init @ (Ctx.to_alist tctx |> List.map ~f:(fun (name, typ) -> Id (name, typ)))
  in

  let verify ?(limit=100) target examples =
    try
      match target (`Id "_") with
      | `Let (name, body, _) ->
        let _ = infer (Ctx.bind tctx name (fresh_free 0)) body in
        Verify.verify_examples ~ctx:vctx target examples
      | _ -> failwith "Bad result from solve_single."
    with
    | TypeError _ -> false
    | Ctx.UnboundError _ -> false
  in

  Ctx.bind (Ctx.empty ()) (Example.name examples)
    ((solve_single ~init ~verify ~config examples) (`Id "_"))
