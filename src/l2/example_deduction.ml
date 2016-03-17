open Core.Std
open Core_extended.Std

open Synthesis_common
open Hypothesis
open Collections

module Sk = Skeleton
module Sp = Specification

exception Bottom

type example = ExprValue.t list * ExprValue.t

let load_examples : file:string -> (ExprValue.t list * ExprValue.t) list =
  fun ~file ->
    Sexp.load_sexp file
    |> [%of_sexp:(ExprValue.t list * ExprValue.t) list]

exception Non_unifiable

let rec occurs : ExprValue.t -> id:string -> bool = fun e ~id ->
  match e with
  | `Num _
  | `Bool _
  | `Unit -> false
  | `Id v -> v = id
  | `List l -> List.exists l ~f:(occurs ~id)
  | `Tree t -> Tree.exists t ~f:(occurs ~id)
  | `Apply (f, args) -> occurs f ~id || List.exists args ~f:(occurs ~id)
  | `Op (_, args) -> List.exists args ~f:(occurs ~id)
  | e -> failwiths "Unexpected expr." e [%sexp_of:ExprValue.t]

let rec apply_unifier : ExprValue.t String.Map.t -> ExprValue.t -> ExprValue.t =
  let module Ctx = String.Map in
  fun ctx e -> match e with
    | `Num _
    | `Bool _
    | `Unit -> e
    | `Id v -> begin match Ctx.find ctx v with
        | Some e' -> e'
        | None -> e
      end
    | `List l -> `List (List.map l ~f:(apply_unifier ctx))
    | `Tree t -> `Tree (Tree.map t ~f:(apply_unifier ctx))
    | `Apply (f, args) -> `Apply (apply_unifier ctx f, List.map args ~f:(apply_unifier ctx))
    | `Op (op, args) -> `Op (op, List.map args ~f:(apply_unifier ctx))
    | e -> failwiths "Unexpected expr." e [%sexp_of:ExprValue.t]

let compose : ExprValue.t String.Map.t -> ExprValue.t String.Map.t -> ExprValue.t String.Map.t =
  fun u1 u2 ->
  let merge outer inner =
    String.Map.fold ~f:(fun ~key:name ~data:typ m ->
        String.Map.add ~key:name ~data:typ m) ~init:outer inner
  in
  merge u1 (String.Map.map ~f:(fun t -> apply_unifier u1 t) u2)

let rec unify_exn : ExprValue.t -> ExprValue.t -> ExprValue.t String.Map.t =
  let module Ctx = String.Map in
  fun e1 e2 -> match e1, e2 with
    | `Id v1, `Id v2 when v1 = v2 -> Ctx.empty
    | `Id v1, `Id v2 when v1 <> v2 -> Ctx.singleton v1 e2
    | `List [], `List [] -> Ctx.empty
    | `List [], `List (_::_)
    | `List [], `Op (Expr.Op.Cons, _)
    | `List (_::_), `List []
    | `Op (Expr.Op.Cons, _), `List [] -> raise Non_unifiable
    | `List (hd::tl), `List (hd'::tl') ->
      let u = unify_exn hd hd' in
      let u' = unify_exn (`List tl) (`List tl') in
      compose u u'
    | `List (hd::tl), `Op (Expr.Op.Cons, [hd'; tl'])
    | `Op (Expr.Op.Cons, [hd'; tl']), `List (hd::tl) ->
      let u = unify_exn hd hd' in
      let u' = unify_exn (`List tl) tl' in
      compose u u'
    | `Num x1, `Num x2 -> if x1 = x2 then Ctx.empty else raise Non_unifiable
    | `Bool x1, `Bool x2 -> if x1 = x2 then Ctx.empty else raise Non_unifiable
    | `Id v, e | e, `Id v ->
      if occurs e ~id:v then raise Non_unifiable else
        Ctx.singleton v e
    | es -> failwiths "Unexpected exprs." es [%sexp_of: ExprValue.t * ExprValue.t]

let unify : ExprValue.t -> ExprValue.t -> ExprValue.t String.Map.t Option.t =
  fun e1 e2 ->
    try Some (unify_exn e1 e2)
    with Non_unifiable -> None

let rec unify_with : ExprValue.t -> ExprValue.t -> ExprValue.t Option.t =
  fun e1 e2 ->
    try Some (apply_unifier (unify_exn e1 e2) e1)
    with Non_unifiable -> None

let unify_example : example -> example -> example Option.t =
  let module Let_syntax = Option.Let_syntax in
  fun (args1, ret1) (args2, ret2) ->
    let%bind args = List.zip args1 args2 in
    let%bind args_u = List.fold args ~init:(Some String.Map.empty) ~f:(fun u (a1, a2) ->
        let%bind u = u in
        let%map u' = unify a1 a2 in
        compose u' u)
    in
    let%map ret_u = unify ret1 ret2 in
    let u = compose ret_u args_u in
    (List.map args1 ~f:(apply_unifier u), apply_unifier u ret1)

let infer_example :
  specs:example list
  -> ctx:Value.t StaticDistance.Map.t
  -> example
  -> Sp.t list =
  let module Let_syntax = Option.Let_syntax in
  fun ~specs ~ctx ex ->
    let possible_specs =
      List.filter_map specs ~f:(unify_example ex)
      |> List.dedup
    in
    let (args, _) = ex in
    let arity = List.length args in
    match possible_specs with
    | [] -> List.repeat arity Sp.Bottom
    | [(args', _)] ->
      List.map args' ~f:(fun a ->
          match ExprValue.to_value a with
          | Ok v -> Sp.Examples (Sp.Examples.singleton (ctx, v))
          | Error _ -> Sp.Top)
    | _ -> List.repeat arity Sp.Top

let infer_examples :
  specs:(example list) String.Map.t
  -> op:string
  -> args:Sp.t Sk.t list
  -> Sp.Examples.example list
  -> Sp.t list =
  fun ~specs ~op ~args exs ->
    let arity = List.length args in
    match String.Map.find specs op with
    | Some op_specs -> begin
        let m_arg_specs =
          List.map exs ~f:(fun (ctx, ret) ->
              try
                let expr_ctx = StaticDistance.Map.map ctx ~f:Expr.of_value in
                let fresh_name = Util.Fresh.mk_fresh_name_fun () in
                let hole_names = Hole.Id.Table.create () in
                let arg_evals =
                  List.map args ~f:(Sk.to_expr ~ctx:expr_ctx ~of_hole:(fun hole ->
                      match Hole.Id.Table.find hole_names hole.Hole.id with
                      | Some name -> `Id name
                      | None ->
                        let name = fresh_name () in
                        Hole.Id.Table.add_exn hole_names ~key:hole.Hole.id ~data:name;
                        `Id name
                    ))
                  |> List.map ~f:ExprValue.of_expr
                  |> List.map ~f:(fun ev ->
                      try Eval.partial_eval ~ctx:Eval.stdlib_evctx ~recursion_limit:100 ev with
                      | Eval.HitRecursionLimit -> `Id (fresh_name ()))
                in
                let ret_eval = ExprValue.of_value ret in
                infer_example ~specs:op_specs ~ctx (arg_evals, ret_eval)
              with Eval.RuntimeError _ -> List.repeat arity Sp.Bottom)
          |> List.transpose
        in
        
        match m_arg_specs with
        | Some arg_specs -> List.map arg_specs ~f:(fun arg_spec ->
            if List.exists arg_spec ~f:(fun sp -> sp = Sp.Bottom) then Sp.Bottom else
              let arg_exs =
                List.filter_map arg_spec ~f:(function
                    | Sp.Top -> None
                    | Sp.Examples exs -> Some (Sp.Examples.to_list exs)
                    | _ -> failwith "BUG: Unexpected specification.")
                |> List.concat
              in
              match arg_exs with
              | [] -> Sp.Top
              | _ -> begin match Sp.Examples.of_list arg_exs with
                  | Ok sp -> Sp.Examples sp
                  | Error _ -> Sp.Bottom
                end)
        | None -> failwith "BUG: Bad result from infer_example."
      end
    | None -> List.repeat arity Sp.Top

let memoized_infer_examples :
  specs:((ExprValue.t list * ExprValue.t) list) String.Map.t
  -> op:string
  -> args:Sp.t Sk.t list
  -> Sp.Examples.example list
  -> Sp.t list =
  let memoized =
    Cache.memoize (fun (specs, op, args, exs) ->
        infer_examples ~specs ~op ~args exs)
  in
  fun ~specs ~op ~args exs -> memoized (specs, op, args, exs)

let push_specs_exn' :
  specs:((ExprValue.t list * ExprValue.t) list) String.Map.t
  -> Sp.t Sk.t
  -> Sp.t Sk.t
  = fun ~specs sk ->
    let rec push_specs_exn sk = 
      if Sp.equal (Skeleton.annotation sk) Sp.Bottom then raise Bottom;
      match sk with
      | Sk.Num_h (_, s)
      | Sk.Bool_h (_, s)
      | Sk.Id_h (_, s)
      | Sk.Hole_h (_, s) as sk -> if s = Sp.Bottom then raise Bottom else sk
      | Sk.List_h (l, s) -> Sk.List_h (List.map l ~f:push_specs_exn, s)
      | Sk.Tree_h (t, s) -> Sk.Tree_h (Tree.map t ~f:push_specs_exn, s)
      | Sk.Let_h ((bound, body), s) -> Sk.Let_h ((push_specs_exn bound, push_specs_exn body), s)
      | Sk.Lambda_h ((num_args, body), s) -> Sk.Lambda_h ((num_args, push_specs_exn body), s)
      | Sk.Op_h ((op, args), s) -> Sk.Op_h ((op, List.map args ~f:push_specs_exn), s)
      | Sk.Apply_h ((func, args), s) ->
        begin match s, func with
          | Sp.Examples exs, Sk.Id_h (Sk.Id.Name func_name, _) ->
            let arg_specs =
              memoized_infer_examples ~specs ~op:func_name ~args (Sp.Examples.to_list exs)
            in
            printf "Pushing specifications for %s.\n" func_name;
            print_endline "Args:";
            Util.print_sexp args [%sexp_of:Sp.t Sk.t list];
            print_endline "Parent spec:";
            Util.print_sexp s [%sexp_of:Sp.t];
            print_endline "Arg specs:";
            Util.print_sexp arg_specs [%sexp_of:Sp.t list];
            print_newline ();
            let args = List.map2_exn args arg_specs ~f:(fun arg sp ->
                Sk.map_annotation arg ~f:(fun _ -> sp))
            in
            Sk.Apply_h ((func, List.map ~f:push_specs_exn args), s)
          | _ -> Sk.Apply_h ((push_specs_exn func, List.map ~f:push_specs_exn args), s)
        end
    in
    push_specs_exn sk

let push_specs' : specs:((ExprValue.t list * ExprValue.t) list) String.Map.t -> Sp.t Sk.t -> Sp.t Sk.t Option.t = fun ~specs sk ->
  try
    let sk' = push_specs_exn' ~specs sk in
    Some sk'
  with Bottom -> None

let of_spec_files : string list -> (Sp.t Sk.t -> Sp.t Sk.t Option.t) = fun spec_files ->
  let name_to_examples =
    List.map spec_files ~f:(fun sf ->
        let exs = load_examples ~file:sf in
        let name = Filename.chop_suffix (Filename.basename sf) "-examples.sexp" in
        (name, exs))
    |> String.Map.of_alist_exn
  in
  push_specs' ~specs:name_to_examples

let spec_dir = "component-specs"
let spec_files =
  Sys.ls_dir spec_dir
  |> List.map ~f:(fun f -> spec_dir ^ "/" ^ f)
let push_specs = of_spec_files spec_files
