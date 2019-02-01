open Core
open Core_extended.Std
open Hypothesis
open Collections
module Sk = Skeleton
module Sp = Specification

exception Bottom

exception Non_unifiable

type example = ExprValue.t list * ExprValue.t [@@deriving sexp]

let timer =
  let t = Timer.empty () in
  let n = Timer.add_zero t in
  n "scan" "Total time spent scanning abstract example lists." ;
  n "unify" "Total time spent unifying expressions." ;
  n "eval" "Total time spent evaluating exprs." ;
  t

let run_with_time name f = Timer.run_with_time timer name f

let examples_of_file : string -> example list =
 fun fn -> Sexp.load_sexps fn |> List.map ~f:[%of_sexp: example]

let examples_of_channel : In_channel.t -> example list =
 fun ch -> Sexp.input_sexps ch |> List.map ~f:[%of_sexp: example]

let rec occurs : ExprValue.t -> id:string -> bool =
 fun e ~id ->
  match e with
  | `Num _ | `Bool _ | `Unit -> false
  | `Id v -> v = id
  | `List l -> List.exists l ~f:(occurs ~id)
  | `Tree t -> Tree.exists t ~f:(occurs ~id)
  | `Apply (f, args) -> occurs f ~id || List.exists args ~f:(occurs ~id)
  | `Op (_, args) -> List.exists args ~f:(occurs ~id)
  | e -> failwiths "Unexpected expr." e [%sexp_of: ExprValue.t]

let rec apply_unifier : ExprValue.t String.Map.t -> ExprValue.t -> ExprValue.t =
  let module Ctx = String.Map in
  fun ctx e ->
    match e with
    | `Num _ | `Bool _ | `Unit -> e
    | `Id v -> ( match Ctx.find ctx v with Some e' -> e' | None -> e )
    | `List l -> `List (List.map l ~f:(apply_unifier ctx))
    | `Tree t -> `Tree (Tree.map t ~f:(apply_unifier ctx))
    | `Apply (f, args) ->
        `Apply (apply_unifier ctx f, List.map args ~f:(apply_unifier ctx))
    | `Op (op, args) -> `Op (op, List.map args ~f:(apply_unifier ctx))
    | e -> failwiths "Unexpected expr." e [%sexp_of: ExprValue.t]

let compose :
    ExprValue.t String.Map.t -> ExprValue.t String.Map.t -> ExprValue.t String.Map.t
    =
 fun u1 u2 ->
  let merge outer inner =
    String.Map.fold
      ~f:(fun ~key:name ~data:typ m -> String.Map.set ~key:name ~data:typ m)
      ~init:outer inner
  in
  merge u1 (String.Map.map ~f:(fun t -> apply_unifier u1 t) u2)

let rec unify_exn : ExprValue.t -> ExprValue.t -> ExprValue.t String.Map.t =
  let module Ctx = String.Map in
  fun e1 e2 ->
    match (e1, e2) with
    | `Id v1, `Id v2 when v1 = v2 -> Ctx.empty
    | `Id v1, `Id v2 when v1 <> v2 -> Ctx.singleton v1 e2
    | `List [], `List [] -> Ctx.empty
    | `List [], `List (_ :: _)
     |`List [], `Op (Expr.Op.Cons, _)
     |`List (_ :: _), `List []
     |`Op (Expr.Op.Cons, _), `List [] ->
        raise Non_unifiable
    | `List (hd :: tl), `List (hd' :: tl') ->
        let u = unify_exn hd hd' in
        let u' = unify_exn (`List tl) (`List tl') in
        compose u u'
    | `List (hd :: tl), `Op (Expr.Op.Cons, [hd'; tl'])
     |`Op (Expr.Op.Cons, [hd'; tl']), `List (hd :: tl) ->
        let u = unify_exn hd hd' in
        let u' = unify_exn (`List tl) tl' in
        compose u u'
    | `Num x1, `Num x2 -> if x1 = x2 then Ctx.empty else raise Non_unifiable
    | `Bool x1, `Bool x2 -> if x1 = x2 then Ctx.empty else raise Non_unifiable
    | `Id v, e | e, `Id v ->
        if occurs e ~id:v then raise Non_unifiable else Ctx.singleton v e
    | es -> failwiths "Unexpected exprs." es [%sexp_of: ExprValue.t * ExprValue.t]

let unify : ExprValue.t -> ExprValue.t -> ExprValue.t String.Map.t Option.t =
 fun e1 e2 ->
  try Some (run_with_time "unify" (fun () -> unify_exn e1 e2))
  with Non_unifiable -> None

let unify_example : example -> example -> example Option.t =
  let module Let_syntax = Option.Let_syntax.Let_syntax in
  fun ex1 ex2 ->
    let args1, ret1 = ex1 in
    let args2, ret2 = ex2 in
    try
      let%bind args = List.zip args1 args2 in
      let%bind args_u =
        List.fold args ~init:(Some String.Map.empty) ~f:(fun u (a1, a2) ->
            let%bind u = u in
            let%map u' = unify a1 a2 in
            compose u' u )
      in
      let%map ret_u = unify ret1 ret2 in
      let u = compose ret_u args_u in
      (List.map args1 ~f:(apply_unifier u), apply_unifier u ret1)
    with exn ->
      Error.tag_arg (Error.of_exn exn) "Failure in unify_example." (ex1, ex2)
        [%sexp_of: example * example]
      |> Error.raise

let infer_example :
       op:string
    -> specs:example list
    -> ctx:Value.t StaticDistance.Map.t
    -> example
    -> Sp.t list =
  let module Let_syntax = Option.Let_syntax.Let_syntax in
  fun ~op ~specs ~ctx ex ->
    try
      let possible_specs =
        run_with_time "scan" (fun () ->
            List.filter_map specs ~f:(unify_example ex)
            |> List.dedup_and_sort ~compare:Polymorphic_compare.compare )
      in
      let args, _ = ex in
      let arity = List.length args in
      match possible_specs with
      | [] ->
          (* printf "No examples found. (%s)\n" op; *)
          (* printf "%s\n" (Sexp.to_string_hum ([%sexp_of:example] ex)); *)
          (* print_newline (); *)
          List.repeat arity Sp.bottom
      | [(args', _)] ->
          List.map args' ~f:(fun a ->
              match ExprValue.to_value a with
              | Ok v -> Examples.singleton (ctx, v) |> Examples.to_spec
              | Error _ -> Sp.top )
      | _ -> List.repeat arity Sp.top
    with exn ->
      Error.tag_arg (Error.of_exn exn) "Failure in infer_example." (op, ex)
        [%sexp_of: string * example]
      |> Error.raise

let infer_examples :
       specs:example list String.Map.t
    -> op:string
    -> args:Sk.t list
    -> Examples.example list
    -> Sp.t list =
 fun ~specs ~op ~args exs ->
  try
    let arity = List.length args in
    match String.Map.find specs op with
    | Some op_specs ->
        let arg_specs =
          List.map exs ~f:(fun (ctx, ret) ->
              try
                let expr_ctx = StaticDistance.Map.map ctx ~f:Expr.of_value in
                let fresh_name = Util.Fresh.mk_fresh_name_fun () in
                let hole_names = Int.Table.create () in
                let arg_evals =
                  List.map args
                    ~f:
                      (Sk.to_expr ~ctx:expr_ctx ~of_hole:(fun hole ->
                           match Hashtbl.find hole_names hole.Hole.id with
                           | Some name -> `Id name
                           | None ->
                               let name = fresh_name () in
                               Hashtbl.add_exn hole_names ~key:hole.Hole.id
                                 ~data:name ;
                               `Id name ))
                  |> List.map ~f:ExprValue.of_expr
                  |> List.map ~f:(fun ev ->
                         try
                           run_with_time "eval" (fun () ->
                               Eval.partial_eval
                                 ~ctx:(failwith "TODO: Replace with library.")
                                 ~recursion_limit:100 ev )
                         with Eval.HitRecursionLimit -> `Id (fresh_name ()) )
                in
                let ret_eval = ExprValue.of_value ret in
                infer_example ~op ~specs:op_specs ~ctx (arg_evals, ret_eval)
              with Eval.RuntimeError _ ->
                (* printf "ERROR: %s\n" (Error.to_string_hum err); *)
                List.repeat arity Sp.bottom )
          |> List.transpose
          |> fun a ->
          Option.value_exn ~message:"BUG: Bad result from infer_example." a
        in
        List.map arg_specs ~f:(fun arg_spec ->
            if List.exists arg_spec ~f:(Sp.equal Sp.bottom) then Sp.bottom
            else
              let arg_exs =
                List.filter_map arg_spec ~f:(fun sp ->
                    match Sp.data sp with
                    | Sp.Top -> None
                    | Examples.Examples exs -> Some (Examples.to_list exs)
                    | _ -> failwith "BUG: Unexpected specification." )
                |> List.concat
              in
              match arg_exs with
              | [] -> Sp.top
              | _ -> (
                match Examples.of_list arg_exs with
                | Ok sp -> Examples.to_spec sp
                | Error _ -> Sp.bottom ) )
    | None -> List.repeat arity Sp.top
  with exn ->
    Error.tag_arg (Error.of_exn exn) "Failure in infer_examples." (op, args, exs)
      [%sexp_of: string * Sk.t list * Examples.example list]
    |> Error.raise

let memoized_infer_examples :
       specs:(ExprValue.t list * ExprValue.t) list String.Map.t
    -> op:string
    -> args:Sk.t list
    -> Examples.example list
    -> Sp.t list =
  let memoized =
    Cache.memoize (fun (specs, op, args, exs) -> infer_examples ~specs ~op ~args exs)
  in
  fun ~specs ~op ~args exs -> memoized (specs, op, args, exs)

let push_specs_exn' :
    specs:(ExprValue.t list * ExprValue.t) list String.Map.t -> Sk.t -> Sk.t =
 fun ~specs sk ->
  let rec push_specs_exn sk =
    let spec = Sk.spec sk in
    if Sp.equal spec Sp.bottom then raise Bottom ;
    match Sk.ast sk with
    | Sk.Num _ | Sk.Bool _ | Sk.Id _ | Sk.Hole _ -> sk
    | Sk.List l -> Sk.list (List.map l ~f:push_specs_exn) spec
    | Sk.Tree t -> Sk.tree (Tree.map t ~f:push_specs_exn) spec
    | Sk.Let {bound; body} ->
        Sk.let_ (push_specs_exn bound) (push_specs_exn body) spec
    | Sk.Lambda {num_args; body} -> Sk.lambda num_args (push_specs_exn body) spec
    | Sk.Op {op; args} -> (
      match Sp.data spec with
      | Examples.Examples exs ->
          let name = Expr.Op.to_string op in
          let arg_specs, _ =
            Util.with_runtime (fun () ->
                memoized_infer_examples ~specs ~op:name ~args (Examples.to_list exs)
            )
          in
          let args = List.map2_exn args arg_specs ~f:Sk.replace_spec in
          Sk.op op (List.map args ~f:push_specs_exn) spec
      | _ -> Sk.op op (List.map args ~f:push_specs_exn) spec )
    | Sk.Apply {func; args} -> (
      match (Sp.data spec, Sk.ast func) with
      | Examples.Examples exs, Sk.Id (Sk.Id.Name name) ->
          let arg_specs, _ =
            Util.with_runtime (fun () ->
                memoized_infer_examples ~specs ~op:name ~args (Examples.to_list exs)
            )
          in
          (* printf "Runtime %s.\n" (Time.Span.to_string_hum runtime); *)
          (* printf "Pushing specifications for %s.\n" func_name; *)
          (* print_endline "Args:"; *)
          (* Util.print_sexp args [%sexp_of:Sp.t Sk.t list]; *)
          (* print_endline "Parent spec:"; *)
          (* Util.print_sexp s [%sexp_of:Sp.t]; *)
          (* print_endline "Arg specs:"; *)
          (* Util.print_sexp arg_specs [%sexp_of:Sp.t list]; *)
          (* print_newline (); *)
          let args = List.map2_exn args arg_specs ~f:Sk.replace_spec in
          Sk.apply func (List.map ~f:push_specs_exn args) spec
      | _ -> Sk.apply (push_specs_exn func) (List.map ~f:push_specs_exn args) spec )
  in
  push_specs_exn sk

let spec_dir = "/Users/jack/Documents/l2/repo/component-specs"

let specs : (ExprValue.t list * ExprValue.t) list String.Map.t Lazy.t =
  if Sys.is_directory spec_dir = `Yes then
    let spec_files =
      Sys.ls_dir spec_dir |> List.map ~f:(fun f -> spec_dir ^ "/" ^ f)
    in
    lazy
      ( List.map spec_files ~f:(fun sf ->
            let exs = examples_of_file sf in
            let name =
              Filename.chop_suffix (Filename.basename sf) "-examples.sexp"
            in
            (name, exs) )
      |> String.Map.of_alist_exn )
  else lazy String.Map.empty

let push_specs : Sk.t -> Sk.t Option.t =
 fun sk ->
  try
    let specs = Lazy.force specs in
    let sk' = push_specs_exn' ~specs sk in
    Some sk'
  with Bottom -> None
