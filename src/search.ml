open Core.Std
open Printf
open Ast
open Infer
open Util

exception SolveError of string

exception Solved of expr
exception SolvedTarget of (expr -> expr)
exception TimedOut

let solve_error msg = raise (SolveError msg)

module Stream = struct
  include Stream

  type 'a stream = 'a t
  type 'a matrix = ('a list) stream

  (* Concatenate two streams together. The second stream will not be
  inspected until the first stream is exhausted. *)
  let concat s1 s2 =
    from (fun _ ->
          match peek s1 with
          | Some _ -> Some (next s1)
          | None -> (match peek s2 with
                     | Some _ -> Some (next s2)
                     | None -> None))

  (* Map a function over a stream. *)
  let map s ~f = from (fun _ -> try Some (f (next s)) with Failure -> None)
  let map_matrix s ~f = map s ~f:(List.map ~f:f)

  (* Create an infinite stream of 'value'. *)
  let repeat (value: 'a) : 'a stream = from (fun _ -> Some value)

  (* Create a finite stream of 'value' of length 'n'. *)
  let repeat_n (n: int) (value: 'a) : 'a stream =
    List.range 0 n |> List.map ~f:(fun _ -> value) |> of_list

  let trans : (('a stream) list -> ('a list) stream) = function
    | [] -> repeat []
    | ss -> from (fun _ -> Some (List.map ss ~f:next))

  let diag (s: ('a stream) stream) : (('a list) stream) =
    from (fun i -> Some (List.map (npeek (i + 1) s) ~f:next))

  let join (x: ('a matrix) matrix) : 'a matrix =
    x |> map ~f:trans |> diag |> map ~f:(fun y -> y |> List.concat |> List.concat)

  let compose (f: 'a -> 'b matrix) (g: 'b -> 'c matrix) (x: 'a) : 'c matrix =
    x |> f |> (map ~f:(List.map ~f:g)) |> join

  let group s ~break =
    from (fun _ ->
          let rec collect () =
            match npeek 2 s with
            | [] -> None
            | [_] -> Some [next s]
            | [x; y] -> if break x y then Some [next s] else collect ()
            | _ -> failwith "Stream.npeek returned a larger list than expected."
          in collect ())

  let merge (ss: ('a matrix) list) : 'a matrix =
    from (fun _ ->
          Some (ss
                |> List.filter_map ~f:(fun s -> try Some (next s) with Failure -> None)
                |> List.concat))

  let rec drop s ~f = match peek s with
    | Some x -> if f x then (junk s; drop s ~f:f) else ()
    | None -> ()

  let flatten (m: 'a matrix) : 'a stream =
    let current = ref [] in
    from (fun _ -> match !current with
                   | x::xs -> current := xs; Some x
                   | [] -> drop m ~f:((=) []);
                           (try (match next m with
                                 | [] -> failwith "Failed to drop empty rows."
                                 | x::xs -> current := xs; Some x)
                            with Failure -> None))
end

module MemoStream = struct
  module Typ = struct type t = typ with compare, sexp end
  module TypMap = Map.Make(Typ)

  type memo_stream = {
    index: int ref;
    head: typed_expr list Int.Table.t;
    stream: typed_expr Stream.matrix;
  }

  type t = memo_stream TypMap.t ref

  let empty () = ref TypMap.empty

  (* Get access to a stream of results for 'typ'. *)
  let get memo typ stream : typed_expr Stream.matrix =
    let mstream = match TypMap.find !memo typ with
      | Some s -> s
      | None ->
         let s = { index = ref 0; head = Int.Table.create (); stream = stream (); } in
         memo := TypMap.add !memo ~key:typ ~data:s; s
    in
    Stream.from
      (fun i -> 
       let sc = i + 1 in
       if sc <= !(mstream.index) then Some (Int.Table.find_exn mstream.head sc)
       else (List.range ~stop:`inclusive (!(mstream.index) + 1) sc
             |> List.iter
                  ~f:(fun j ->
                      try Int.Table.add_exn mstream.head ~key:j ~data:(Stream.next mstream.stream);
                          incr mstream.index;
                      with Stream.Failure -> ());
             if sc = !(mstream.index) then Some (Int.Table.find_exn mstream.head sc) else None))
end

let rec enumerate memo init typ : typed_expr Stream.matrix =
  let open Stream in
  let arrow_error () = solve_error "Operator is not of type Arrow_t." in

  (* printf "enumerate %s %s.\n" *)
  (*        (List.to_string init ~f:(fun e -> expr_to_string (expr_of_texpr e))) *)
  (*        (typ_to_string typ); *)

  (* Init is finite, so we can construct an init stream by breaking
  init into a list of size classes and returning that list as a
  stream. *)
  let (init_matrix: typed_expr matrix) =
    let init_sizes =
      List.filter init ~f:(fun e -> is_unifiable typ (typ_of_expr e))
      |> List.map ~f:(fun e -> e, size (expr_of_texpr e))
    in
    let max_size = List.fold_left init_sizes ~init:0 ~f:(fun x (_, y) -> if x > y then x else y) in
    List.range ~stop:`inclusive 1 max_size
    |> List.map ~f:(fun s ->
                    List.filter_map init_sizes ~f:(fun (e, s') -> if s = s' then Some e else None))
    |> of_list
  in

  (* Generate an argument list matrix that conforms to the provided list of types. *)
  let args_matrix = function
    | arg_typ::arg_typs ->
       let choose typ (prev_args: typed_expr list) : (typed_expr list) matrix =
         (* Generate the argument matrix lazily so that it will not be
         created until the prefix classes are exhausted. *)
         slazy (fun () -> map_matrix (MemoStream.get memo typ (fun () -> enumerate memo init typ))
                                     ~f:(fun arg -> prev_args @ [arg]))
       in
       let choose_all =
         List.fold_left arg_typs
                        ~init:(choose arg_typ)
                        ~f:(fun choose' arg_typ' -> compose choose' (choose arg_typ')) in
       choose_all []
    | [] -> solve_error "Cannot generate args matrix with no arguments."
  in

  let op_matrix op op_typ = match op_typ with
    | Arrow_t (arg_typs, _) ->
       (* The args matrix will start at size 1. Wrapping with an
       operator increases the size by 1, so the first size class will
       be empty, since it would correspond to an operator with no
       arguments. *)
       let prefix = repeat_n (List.length arg_typs) [] in
       let matrix =
         slazy (fun () -> map_matrix (args_matrix arg_typs) ~f:(fun args -> Op ((op, args), op_typ)))
       in
       concat prefix matrix
    | _ -> arrow_error ()
  in

  (* The op stream is infinite, so it needs more careful handling. *)
  let op_matrices =
    Op.metadata_by_op
    (* Filter all operators that can return the correct type. *)
    |> List.filter ~f:(fun (_, meta) ->
                       match meta.Op.typ with
                       | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
                       | _ -> arrow_error ())

    (* Unify the return type of the operator with the input type. By
    the side effects of unify, all the other free type variables in
    the operator type will reflect the substitution. Now we have
    correct types for the arguments. *)
    |> List.map ~f:(fun (op, meta) ->
                    match instantiate 0 typ, instantiate 0 meta.Op.typ with
                    | typ', (Arrow_t (_, ret_typ) as op_typ) ->
                       unify_exn typ' ret_typ;
                       op, normalize (generalize (-1) op_typ)
                    | _ -> arrow_error ())

    (* Generate a matrix for each operator. *)
    |> List.map ~f:(fun (op, op_typ) -> op_matrix op op_typ)
  in
  merge ([init_matrix] @ op_matrices)

type spec = {
  target: expr -> expr -> expr;
  examples: example list;
  signature: typ;
  tctx: typ Ctx.t;
  vctxs: expr Ctx.t list;
  fold_depth: int;
}

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

let solve_verifier init typ verify =
  let strm = enumerate (MemoStream.empty ()) init typ
             |> Stream.flatten
             |> Stream.map ~f:expr_of_texpr in
  Stream.from
    (fun _ ->
     Option.map (Stream.peek strm) ~f:(fun expr -> if verify expr
                                                   then Some (Stream.next strm)
                                                   else (Stream.junk strm; None)))

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
         |> Ctx.filter ~f:(fun ~key:_ ~data:typ -> is_unifiable res_typ typ)
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

let solve_catamorphic_looped ?(init=[]) (examples: example list) : expr -> expr =
  let target_name = get_target_name examples in
  let initial_spec = create_spec (fun body expr -> `Let (target_name, body, expr))
                                 examples
                                 (signature examples)
                                 (Ctx.empty ())
                                 (List.map examples ~f:(fun _ -> Ctx.empty ()))
                                 1
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

  (* print_endline "Completed structure analysis. Inferred structures:"; *)
  (* let _ = List.iter specs *)
  (*                   ~f:(fun spec -> *)
  (*                       printf "%s\n\t%s\n" *)
  (*                              (expr_to_string (spec.target (`Id "lambda") (`Id "_"))) *)
  (*                              (String.concat ~sep:" " (List.map ~f:example_to_string spec.examples))) *)
  (* in *)
  (* print_newline (); *)

  (* Create a solver from a specification. A solver is a verification
  function paired with a stream of candidates. *)
  let create_solver spec = match spec.signature with
    | Arrow_t (arg_typs, ret_typ) ->
       let args = List.map arg_typs ~f:(fun typ -> Fresh.name "x", typ) in
       let arg_names, _ = List.unzip args in
       let init' =
         (Ctx.to_alist spec.tctx |> List.map ~f:(fun (name, typ) -> Id (name, typ)))
         @ (List.map init ~f:(fun expr -> infer (Ctx.empty ()) expr))
         @ (List.map args ~f:(fun (name, typ) -> Id (name, typ)))
       in
       let strm =
         enumerate (MemoStream.empty ()) init' ret_typ
         |> Stream.flatten
         |> Stream.map ~f:expr_of_texpr
       in
       let target expr = spec.target (`Lambda (arg_names, expr)) in
       let verify target = Verify.verify_examples target examples in
       strm, target, verify
    | _ -> solve_error "Lambda examples do not represent a function."
  in
  let solvers = List.map specs ~f:create_solver in

  (* print_endline "Starting search..."; *)
  try
    while true do
      let strm, target, verify =
        List.reduce_exn solvers
                        ~f:(fun ((s1, _, _) as x1)  ((s2, _, _) as x2) ->
                            match (Stream.peek s1), (Stream.peek s2) with
                            | Some e1, Some e2 -> if (size e1) < (size e2) then x1 else x2
                            | Some _, None -> x1
                            | None, Some _ -> x2
                            | None, None -> solve_error "All streams exhausted.")
      in
      let expr = Stream.next strm in
      (* printf "CAND %d %d %s\n" (Stream.count strm) (size expr) (expr_to_string (target expr (`Id "_"))); *)
      if verify (target expr) then raise (SolvedTarget (target expr)) else ()
    done;
    solve_error "Exited solve loop without finding a solution."
  with
  | SolvedTarget target -> target
