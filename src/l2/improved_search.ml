open Core.Std

open Synthesis_common

open Ast
open Collections
open Hypothesis
open Infer

let counter = Counter.empty ()
let () =
  let n = Counter.add_zero counter in
  n "symb_exec_tried" "Number of expressions where symbolic execution was tried.";
  n "symb_exec_failed" "Number of expressions where symbolic execution failed.";
  n "symb_exec_fatal" "Number of expressions where symbolic execution failed fatally.";
  n "unification_tried" "Number of expressions where unification was tried.";
  n "unification_failed" "Number of expressions where unification failed.";
  n "unification_pruned" "Number of times where an expression was pruned by unification.";
  n "unification_succeeded" "Number of times where unification succeeded.";
  n "push_spec_w_unification" "Tried to push spec using unification procedure."

module L2_CostModel : CostModel_Intf = struct
  module Sk = Skeleton
    
  let id_cost = function
    | Sk.Name name -> begin match name with
        | "foldr"
        | "foldl"
        | "foldt" -> 3
        | "map"
        | "mapt"
        | "filter" -> 2
        | _ -> 1
      end
    | Sk.StaticDistance sd -> 1

  let op_cost = Expr.Op.cost
  let lambda_cost = 1
  let num_cost = 1
  let bool_cost = 1
  let hole_cost = 0
  let let_cost = 1
  let list_cost = 1
  let tree_cost = 1
end

module L2_Hypothesis = Hypothesis.Make(L2_CostModel)

module type Deduction_intf = sig
  val push_specifications : Specification.t Skeleton.t -> Specification.t Skeleton.t Option.t
  val push_specifications_unification : Specification.t Skeleton.t -> Specification.t Skeleton.t Option.t
end

module L2_Deduction : Deduction_intf = struct
  module Sp = Specification
  module Sk = Skeleton

  let type_err name type_ =
    failwiths "Unexpected type for return value of function." (name, type_) <:sexp_of<id * Type.t>>

  let spec_err name spec =
    failwiths "Unexpected spec for return value of function." (name, spec) <:sexp_of<id * Sp.t>>

  let input_err name inp =
    failwiths "Unexpected input value for function." (name, inp) <:sexp_of<id * value>>

  let ret_err name ret =
    failwiths "Unexpected return value of function." (name, ret) <:sexp_of<id * value>>

  let lookup_err name id =
    failwiths "Variable name not present in context." (name, id) <:sexp_of<id * StaticDistance.t>>

  module type Deduce_2_intf = sig
      val name : string
      val examples_of_io : value -> value -> ((value * value) list, unit) Result.t
  end
  
  module Make_deduce_2 (M : Deduce_2_intf) = struct
    let lambda_spec collection_id parent_spec =
      let open Result.Monad_infix in
      match parent_spec with
      | Sp.Examples exs ->
        let m_hole_exs =
          List.map (Sp.Examples.to_list exs) ~f:(fun (ctx, out_v) ->
              let in_v = match StaticDistance.Map.find ctx collection_id with
                | Some in_v -> in_v
                | None -> lookup_err M.name collection_id
              in
              Result.map (M.examples_of_io in_v out_v) ~f:(fun io ->
                  List.map io ~f:(fun (i, o) -> (ctx, [i]), o)))
          |> Result.all
          >>| List.concat
          >>= fun hole_exs ->
          Result.map_error (Sp.FunctionExamples.of_list hole_exs) ~f:(fun _ -> ())
        in
        begin
          match m_hole_exs with
          | Ok hole_exs -> Sp.FunctionExamples hole_exs
          | Error () -> Sp.Bottom
        end
      | Sp.Top -> Sp.Top
      | Sp.Bottom -> Sp.Bottom
      | _ -> spec_err M.name parent_spec

    let deduce spec args =
      let open Result.Monad_infix in
      match args with
      | [ Sk.Id_h (Sk.StaticDistance sd, _) as list; lambda ] when (Sk.annotation lambda) = Sp.Top ->
        let child_spec = lambda_spec sd spec in
        [ list; Sk.map_annotation lambda ~f:(fun _ -> child_spec) ]
      | _ -> args
  end

  module type Deduce_fold_intf = sig
    val name : string
    val is_base_case : value -> bool
    val examples_of_io : value -> value -> ((value * value) list, unit) Result.t
  end

  module Make_deduce_fold (M : Deduce_fold_intf) = struct
    let base_spec collection_id parent_spec =
      match parent_spec with
      | Sp.Examples exs ->
        let exs = Sp.Examples.to_list exs in
        let m_base_exs =
          List.filter exs ~f:(fun (ctx, out_v) ->
              match StaticDistance.Map.find ctx collection_id with
              | Some v -> M.is_base_case v
              | None -> lookup_err (M.name ^ "-base-case") collection_id)
          |> Sp.Examples.of_list
        in
        begin
          match m_base_exs with
          | Ok base_exs -> Sp.Examples base_exs
          | Error _ -> Sp.Bottom
        end
      | Sp.Top -> Sp.Top
      | Sp.Bottom -> Sp.Bottom
      | _ -> spec_err (M.name ^ "-base-case") parent_spec

    let deduce spec args =
      let open Result.Monad_infix in
      match args with
      | [ Sk.Id_h (Sk.StaticDistance sd, _) as input; lambda; base ] ->
        let b_spec = Sk.annotation base in
        let b_spec = if b_spec = Sp.Top then base_spec sd spec else b_spec in
        [ input; lambda; Sk.map_annotation base ~f:(fun _ -> b_spec ) ]
      | _ -> args
  end

  module Deduce_map = Make_deduce_2 (struct
      let name = "map"
      let examples_of_io in_v out_v =
        let out = match out_v with
          | `List out -> out
          | _ -> ret_err name out_v
        in
        let inp = match in_v with
          | `List inp -> inp
          | _ -> input_err name in_v
        in
        Option.value_map (List.zip inp out) ~default:(Error ()) ~f:(fun io -> Ok (io))
    end)

  module Deduce_mapt = Make_deduce_2 (struct
      let name = "mapt"
      let examples_of_io in_v out_v =
        let out = match out_v with
          | `Tree out -> out
          | _ -> ret_err name out_v
        in
        let inp = match in_v with
          | `Tree inp -> inp
          | _ -> input_err name in_v
        in
        Option.map (Tree.zip inp out) ~f:(fun io -> Ok (Tree.flatten io))
        |> Option.value ~default:(Error ())
    end)

  module Deduce_filter = Make_deduce_2 (struct
      let name = "filter"

      let rec f = function
        (* If there are no inputs and no outputs, then there are no
           examples, but filter is valid. *)
        | [], [] -> Some []

        (* If there are some inputs and no outputs, then the inputs
           must have been filtered. *)
        | (_::_ as inputs), [] -> Some (List.map inputs ~f:(fun i -> i, `Bool false))

        (* If there are some outputs and no inputs, then filter is
           not valid. *)
        | [], _::_ -> None

        | i::is, o::os when i = o ->
          Option.map (f (is, os)) ~f:(fun exs -> (i, `Bool true)::exs)

        | i::is, (_::_ as outputs) ->
          Option.map (f (is, outputs)) ~f:(fun exs -> (i, `Bool false)::exs)

      let examples_of_io in_v out_v =
        let out = match out_v with
          | `List out -> out
          | _ -> ret_err name out_v
        in
        let inp = match in_v with
          | `List inp -> inp
          | _ -> input_err name in_v
        in
        Option.value_map (f (inp, out)) ~default:(Error ()) ~f:(fun io -> Ok io)
    end)

  module Deduce_foldl = Make_deduce_fold (struct
      let name = "foldl"
      let is_base_case v = v = `List []
      let examples_of_io _ _ = Error ()
    end)

  module Deduce_foldr = Make_deduce_fold (struct
      let name = "foldr"
      let is_base_case v = v = `List []
      let examples_of_io _ _ = Error ()
    end)

  module Deduce_foldt = Make_deduce_fold (struct
      let name = "foldt"
      let is_base_case v = v = `Tree Tree.Empty
      let examples_of_io _ _ = Error ()
    end)
  
  let deduce_lambda lambda spec =
    let (num_args, body) = lambda in
    if (Sk.annotation body) = Sp.Top then
      let child_spec = match Sp.increment_scope spec with
        | Sp.FunctionExamples exs ->
          let arg_names = StaticDistance.args num_args in
          let child_exs =
            Sp.FunctionExamples.to_list exs
            |> List.map ~f:(fun ((in_ctx, in_args), out) ->
                let value_ctx = StaticDistance.Map.of_alist_exn (List.zip_exn arg_names in_args) in
                let in_ctx = StaticDistance.Map.merge value_ctx in_ctx ~f:(fun ~key:_ v ->
                    match v with
                    | `Both (x, _)
                    | `Left x
                    | `Right x -> Some x)
                in
                (in_ctx, out))
            |> Sp.Examples.of_list_exn
          in
          Sp.Examples child_exs
        | Sp.Bottom -> Sp.Bottom
        | Sp.Top -> Sp.Top
        | _ -> spec_err "<lambda>" spec
      in
      (num_args, Sk.map_annotation body ~f:(fun _ -> child_spec))
    else lambda
  
  let rec push_specifications (skel: Specification.t Skeleton.t) : Specification.t Skeleton.t Option.t =
    let open Option.Monad_infix in
    match skel with
    | Sk.Num_h (_, s)
    | Sk.Bool_h (_, s)
    | Sk.Id_h (_, s)
    | Sk.Hole_h (_, s) -> if s = Sp.Bottom then None else Some skel
    | Sk.List_h (l, s) ->
      let m_l = List.map l ~f:push_specifications |> Option.all in
      m_l >>| fun l -> Sk.List_h (l, s)
    | Sk.Tree_h (t, s) ->
      let m_t = Tree.map t ~f:push_specifications |> Tree.all in
      m_t >>| fun t -> Sk.Tree_h (t, s)
    | Sk.Let_h ((bound, body), s) ->
      let m_bound = push_specifications bound in
      let m_body = push_specifications body in
      m_bound >>= fun bound -> m_body >>| fun body -> Sk.Let_h ((bound, body), s)
    | Sk.Lambda_h (lambda, s) ->
      let (num_args, body) = deduce_lambda lambda s in
      let m_body = push_specifications body in
      m_body >>| fun body -> Sk.Lambda_h ((num_args, body), s)
    | Sk.Op_h ((op, args), s) ->
      let m_args = List.map args ~f:push_specifications |> Option.all in
      m_args >>| fun args -> Sk.Op_h ((op, args), s)
    | Sk.Apply_h ((func, args), s) ->
      let args = match func with
        | Sk.Id_h (Sk.Name "map", _) -> Deduce_map.deduce s args
        | Sk.Id_h (Sk.Name "mapt", _) -> Deduce_mapt.deduce s args
        | Sk.Id_h (Sk.Name "filter", _) -> Deduce_filter.deduce s args
        | Sk.Id_h (Sk.Name "foldl", _) -> Deduce_foldl.deduce s args
        | Sk.Id_h (Sk.Name "foldr", _) -> Deduce_foldr.deduce s args
        | Sk.Id_h (Sk.Name "foldt", _) -> Deduce_foldt.deduce s args
        | _ -> args        
      in
      let m_args =
        if List.exists args ~f:(fun a -> Sk.annotation a = Sp.Bottom) then None else
          Option.all (List.map args ~f:push_specifications)
      in
      let m_func = push_specifications func in
      m_args >>= fun args -> m_func >>| fun func -> Sk.Apply_h ((func, args), s)

    let recursion_limit = 100

  let sterm_of_result r =
    let fresh_name = Util.Fresh.mk_fresh_name_fun () in
    let ctx = ref Hole.Id.Map.empty in
    let module U = Unify in
    let rec f r =
      let module SE = Symbolic_execution in
      let module Sk = Skeleton in
      match r with
      | SE.Num_r x -> U.K (Int.to_string x)
      | SE.Bool_r x -> U.K (if x then "true" else "false")
      | SE.List_r [] -> U.K "[]"
      | SE.List_r (x::xs) -> U.Cons (f x, f (SE.List_r xs))
      | SE.Id_r (Sk.StaticDistance sd) -> U.V (StaticDistance.to_string sd)
      | SE.Id_r (Sk.Name id) -> U.V id
      | SE.Op_r (RCons, [xs; x])
      | SE.Op_r (Cons, [x; xs]) -> U.Cons (f x, f xs)
      | SE.Symbol_r id -> 
        let var = match Hole.Id.Map.find !ctx id with
          | Some var -> var
          | None ->
            let var = fresh_name () in
            ctx := Hole.Id.Map.add !ctx ~key:id ~data:var; var
        in
        U.V var
      | SE.Apply_r _ -> U.V (fresh_name ())
      | SE.Closure_r _
      | SE.Tree_r _
      | SE.Op_r _ -> raise U.Unknown
    in
    try
      let sterm = f r in
      let ctx = Hole.Id.Map.to_alist !ctx |> List.map ~f:Tuple.T2.swap |> String.Map.of_alist_exn in
      Ok (sterm, ctx)
    with U.Unknown -> Error (Error.of_string "Unhandled construct.")

  let rec value_of_term t : value =
    let module U = Unify in
    match t with
    | U.Term ("[]", []) -> `List []
    | U.Term ("true", []) -> `Bool true
    | U.Term ("false", []) -> `Bool false
    | U.Term (s, []) -> `Num (Int.of_string s)
    | U.Term ("Cons", [x; y]) -> begin
        match value_of_term y with
        | `List y -> `List ((value_of_term x)::y)
        | _ -> failwith "Translation error"
      end
    | _ -> failwith "Translation error"
      
  let push_specifications_unification s =
    if (!Config.config).Config.deduction then
      let module SE = Symbolic_execution in
      let module Sp = Specification in
      Counter.incr counter "push_spec_w_unification";
      match Skeleton.annotation s with
      | Sp.Examples exs ->
        let m_new_examples =
          List.fold (Sp.Examples.to_list exs) ~init:(Some Hole.Id.Map.empty) ~f:(fun m_exs (ins, out_e) ->
              Option.bind m_exs (fun exs -> 
                  try
                    Counter.incr counter "symb_exec_tried";
                    
                    (* Try symbolically executing the candidate in the example context. *)
                    let out_a = SE.partially_evaluate ~recursion_limit
                        ~ctx:(StaticDistance.Map.map ins ~f:SE.result_of_value) s
                    in

                    match out_a with
                    | SE.Symbol_r _ -> None
                    | SE.Apply_r _ ->
                      begin
                        match SE.skeleton_of_result out_a with
                        | Some skel ->
                          if (L2_Hypothesis.compute_cost skel) < (L2_Hypothesis.compute_cost s)
                          then None else m_exs
                        | None -> m_exs
                      end
                    | _ -> begin
                        Counter.incr counter "unification_tried";

                        (* Convert output and expected output to terms and
                           unify. If unification fails, discard the candidate. *)
                        match sterm_of_result out_a with
                        | Ok (out_a, symbol_names) -> begin match Unify.sterm_of_value out_e with
                            | Some out_e -> begin try
                                  let sub = Unify.unify_one (Unify.translate out_a) (Unify.translate out_e) in
                                  Counter.incr counter "unification_succeeded";
                                  Some (List.fold sub ~init:exs ~f:(fun exs (var, term) ->
                                      match String.Map.find symbol_names var with
                                      | Some id ->
                                        Hole.Id.Map.add_multi exs ~key:id ~data:(ins, value_of_term term)
                                      | None -> exs))
                                with Unify.Non_unifiable ->
                                  Counter.incr counter "unification_pruned";
                                  None
                              end
                            | None ->
                              Counter.incr counter "unification_failed";
                              m_exs
                          end
                        | Error _ ->
                          Counter.incr counter "unification_failed";
                          m_exs
                      end
                  with
                  (* These are non-fatal errors. We learn nothing about the
                     candidate, but we can't discard it either. *)
                  | SE.EvalError `HitRecursionLimit
                  | SE.EvalError `UnhandledConditional ->
                    Counter.incr counter "symb_exec_failed";
                    m_exs

                  (* All other errors are fatal, so we discard the candidate. *)
                  | SE.EvalError _ ->
                    Counter.incr counter "symb_exec_fatal";
                    None))
        in
        Option.bind m_new_examples (fun new_exs ->
            let new_exs = Hole.Id.Map.map new_exs ~f:Sp.Examples.of_list in
            if Hole.Id.Map.exists new_exs ~f:Result.is_error then None else
              Some (Hole.Id.Map.map new_exs ~f:Or_error.ok_exn))
        |>  Option.map ~f:(fun new_exs -> Skeleton.map_hole s ~f:(fun (hole, old_spec) ->
            let s = Sk.Hole_h (hole, old_spec) in
            match Hole.Id.Map.find new_exs hole.Hole.id with
            | Some exs -> begin match old_spec with
                | Sp.Top -> Skeleton.Hole_h (hole, Sp.Examples exs)
                | _ -> s
              end
            | None -> s))
      | _ -> Some s
    else Some s
end

module L2_Generalizer = struct
  (* This generalizer generates programs of the following form. Each
     hole in the hypotheses that it returns is tagged with a symbol
     name that the generalizer uses to select the hypotheses that can
     be used to fill that hole later.

     L := fun x_1 ... x_n -> E

     E := map I (L)
        | filter I (L)
        | foldl I (L) C
        | ...
        | E'

     E' := car E'
         | cdr E'
         | cons E' E'
         | ...
         | C

     C := 0
        | 1
        | []
        | ...

     I := <identifier in current scope>
  *)

  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list
  
  module type Selector = sig
    val select : Symbol.t -> t list
  end

  module type S = sig
    val generalize : Generalizer.t

    (* The following are implementation details of the
       generalizer. They are exposed for testing purposes. *)
    val generate_constants : t
    val generate_identifiers : t
    val generate_expressions : t
    val generate_lambdas : t
    val generate_combinators : t
  end

  module Symbols = struct
    let lambda = Symbol.create "Lambda"
    let combinator = Symbol.create "Combinator"
    let expression = Symbol.create "Expression"
    let constant = Symbol.create "Constant"
    let identifier = Symbol.create "Identifier"
    let base_case = Symbol.create "BaseCase"    
  end
  
  module Shared = struct
    include Symbols
        
    module Sp = Specification
    module H = L2_Hypothesis

    type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list

    let combinators = [
      "map"; "mapt"; "filter"; "foldl"; "foldr"; "foldt"; "rec"
    ]
    let functions = Ctx.filter Infer.stdlib_tctx ~f:(fun ~key:k ~data:_ ->
        not (List.mem ~equal:String.equal combinators k))

    let generate_constants hole spec =
      let constants = [
        Type.num, [
          H.num 0 spec;
          H.num 1 spec;
          H.num Int.max_value spec;
        ];
        Type.bool, [
          H.bool true spec;
          H.bool false spec;
        ];
        Type.list (Type.quant "a") |> instantiate 0, [
          H.list [] spec;
        ]
      ] in
      List.concat_map constants ~f:(fun (t, xs) ->
          match Infer.Unifier.of_types hole.Hole.type_ t with
          | Some u -> List.map xs ~f:(fun x -> (x, u))
          | None -> [])

    let generate_identifiers hole spec =
      List.filter_map (StaticDistance.Map.to_alist hole.Hole.ctx) ~f:(fun (id, id_t) ->
          Option.map (Unifier.of_types hole.Hole.type_ id_t) ~f:(fun u ->
              H.id_sd id spec, u))

    let generate_expressions hole spec =
      let op_exprs = List.filter_map Expr.Op.all ~f:(fun op ->
          let op_t = instantiate 0 (Expr.Op.meta op).Expr.Op.typ in
          match op_t with
          | Arrow_t (args_t, ret_t) ->
            (* Try to unify the return type of the operator with the type of the hole. *)
            Option.map (Unifier.of_types hole.Hole.type_ ret_t) ~f:(fun u ->
                (* If unification succeeds, apply the unifier to the rest of the type. *)
                let args_t = List.map args_t ~f:(Unifier.apply u) in
                let arg_holes = List.map args_t ~f:(fun t ->
                    H.hole (Hole.create hole.Hole.ctx t expression) Sp.Top)
                in
                H.op (op, arg_holes) spec, u)
          | _ -> None)
      in
      let apply_exprs = List.filter_map (Ctx.to_alist functions) ~f:(fun (func, func_t) ->
          let func_t = instantiate 0 func_t in
          match func_t with
          | Arrow_t (args_t, ret_t) ->
            (* Try to unify the return type of the operator with the type of the hole. *)
            Option.map (Unifier.of_types hole.Hole.type_ ret_t) ~f:(fun u ->
                (* If unification succeeds, apply the unifier to the rest of the type. *)
                let args_t = List.map args_t ~f:(Unifier.apply u) in
                let arg_holes = List.map args_t ~f:(fun t ->
                    H.hole (Hole.create hole.Hole.ctx t expression) Sp.Top)
                in
                H.apply (H.id_name func Sp.Top, arg_holes) spec, u)
          | _ -> None)
      in
      op_exprs @ apply_exprs

    let generate_lambdas hole spec =
      match hole.Hole.type_ with
      (* If the hole has an arrow type, generate a lambda expression with
         the right number of arguments and push the specification down. *)
      | Arrow_t (args_t, ret_t) ->
        let num_args = List.length args_t in
        let arg_names = StaticDistance.args num_args in
        let type_ctx =
          List.fold (List.zip_exn arg_names args_t)
            ~init:(StaticDistance.map_increment_scope hole.Hole.ctx)
            ~f:(fun ctx (arg, arg_t) -> StaticDistance.Map.add ctx ~key:arg ~data:arg_t)
        in
        let lambda =
          H.lambda (num_args, H.hole (Hole.create type_ctx ret_t combinator) Sp.Top) spec
        in
        [ lambda, Unifier.empty ]
      | _ -> []

    let generate_combinators hole spec =
      List.filter_map (Ctx.to_alist Infer.stdlib_tctx) ~f:(fun (func, func_t) ->
          if List.mem ~equal:String.equal combinators func then
            let func_t = instantiate 0 func_t in
            match func_t with
            | Arrow_t (args_t, ret_t) ->
              (* Try to unify the return type of the operator with the type of the hole. *)
              Option.map (Unifier.of_types ret_t hole.Hole.type_) ~f:(fun u ->
                  (* If unification succeeds, apply the unifier to the rest of the type. *)
                  let args_t = List.map args_t ~f:(Infer.Unifier.apply u) in
                  let arg_holes = match (func, args_t) with
                    | "map", [ t1; t2 ]
                    | "mapt", [ t1; t2 ]
                    | "filter", [ t1; t2 ] -> [
                        H.hole (Hole.create hole.Hole.ctx t1 identifier) Sp.Top;
                        H.hole (Hole.create hole.Hole.ctx t2 lambda) Sp.Top;
                      ]
                    | "foldr", [ t1; t2; t3 ]
                    | "foldl", [ t1; t2; t3 ]
                    | "foldt", [ t1; t2; t3 ] -> [
                        H.hole (Hole.create hole.Hole.ctx t1 identifier) Sp.Top;
                        H.hole (Hole.create hole.Hole.ctx t2 lambda) Sp.Top;
                        H.hole (Hole.create hole.Hole.ctx t3 base_case) Sp.Top;
                      ]
                    | name, _ -> failwith (sprintf "Unexpected combinator name: %s" name)
                  in
                  H.apply (H.id_name func Sp.Top, arg_holes) spec, u)
            | _ -> None
          else None)
  end

  module With_components = struct
    include Shared

    let select symbol =
      if symbol = constant then
        [ generate_constants ]
      else if symbol = base_case then
        [ generate_constants; generate_identifiers ]
      else if symbol = identifier then
        [ generate_identifiers ]
      else if symbol = lambda then
        [ generate_lambdas ]
      else if symbol = expression then
        [ generate_expressions; generate_identifiers; generate_constants ]
      else if symbol = combinator then
        [ generate_combinators; generate_expressions; generate_constants ]
      else
        failwiths "Unknown symbol type." symbol Symbol.sexp_of_t

    let generalize hole spec =
      let generators = select hole.Hole.symbol in
      List.concat (List.map generators ~f:(fun g -> g hole spec))
  end

  module No_components = struct
    include Shared

    let select symbol =
      if symbol = constant then
        [ generate_constants ]
      else if symbol = base_case then
        [ generate_identifiers; generate_constants; ]
      else if symbol = identifier then
        [ generate_identifiers ]
      else if symbol = lambda then
        [ generate_lambdas ]
      else if symbol = expression then
        [ ]
      else if symbol = combinator then
        [ generate_combinators; ]
      else
        failwiths "Unknown symbol type." symbol Symbol.sexp_of_t

    let generalize hole spec =
      let generators = select hole.Hole.symbol in
      List.concat (List.map generators ~f:(fun g -> g hole spec))
  end

  module No_lambdas = struct
    include Shared

    let select symbol =
      if symbol = constant then
        [ generate_constants ]
      else if symbol = identifier then
        [ generate_identifiers ]
      else if symbol = lambda then
        [ ]
      else if symbol = expression then
        [ generate_expressions; generate_identifiers; generate_constants ]
      else if symbol = combinator then
        [ generate_expressions; generate_identifiers; generate_constants ]
      else
        failwiths "Unknown symbol type." symbol Symbol.sexp_of_t

    let generalize hole spec =
      let generators = select hole.Hole.symbol in
      List.concat (List.map generators ~f:(fun g -> g hole spec))      
  end
end

module type Prune_intf = sig
  val should_prune : Hypothesis.t -> bool
end

module type Synthesizer_intf = sig
  val synthesize : Hypothesis.t -> cost:int -> Hypothesis.t Option.t
end

module Make_BFS_Synthesizer (G: L2_Generalizer.S) : Synthesizer_intf = struct
  exception SynthesisException of Hypothesis.t Option.t

  let synthesize hypo ~cost:max_cost =
    let open Hypothesis in
    let heap = Heap.create ~cmp:compare_cost () in
    try
      Heap.add heap hypo;
      while true do
        match Heap.pop heap with
        | Some h ->
          (* Take the hole with the smallest id. *)
          let m_hole =
            List.min_elt (holes h) ~cmp:(fun (h1, _) (h2, _) -> Hole.compare h1 h2)
          in
          (match m_hole with
           | Some (hole, spec) ->
             List.iter (G.generalize hole spec) ~f:(fun (c, u) ->
                 if (kind c) = Abstract || Hypothesis.verify c then
                   let h = apply_unifier (fill_hole hole ~parent:h ~child:c) u in

                   match kind c with
                   | Concrete ->
                     let () = printf "%s\n" (Skeleton.to_string_hum (skeleton h)) in
                     if Hypothesis.verify h then raise (SynthesisException (Some h))
                   | Abstract -> Heap.add heap h)
           | None -> failwiths "BUG: Abstract hypothesis has no holes."
                       h Hypothesis.sexp_of_t)
        | None -> raise (SynthesisException None)
      done; None
    with SynthesisException h -> h
end

module type Search_intf = sig
  val search : check_cost:(int -> bool) -> found:(Hypothesis.t -> never_returns) -> Hypothesis.t -> int -> int
end

let create_memoizer () = Memoizer.create L2_Generalizer.No_lambdas.generalize

module Memoized_search : Search_intf = struct
  let memoizer = create_memoizer ()

  let search ~check_cost ~found hypo initial_cost =
    let module H = Hypothesis in
    let rec search (cost: int) =
      (* If the cost of searching this level exceeds the max cost, end the search. *)
      if check_cost cost then cost else
        (* Otherwise, examine the next row in the search tree. *)
        begin
          let num_holes = List.length (H.holes hypo) in
          List.concat_map (Util.m_partition cost num_holes) ~f:(fun hole_costs ->
              List.fold2_exn (H.holes hypo) hole_costs ~init:[ (hypo, Unifier.empty) ]
                ~f:(fun hs (hole, spec) hole_cost -> List.concat_map hs ~f:(fun (p, p_u) ->
                    let children = Memoizer.get memoizer hole spec hole_cost in
                    List.map children ~f:(fun (c, c_u) ->
                        let u = Unifier.compose c_u p_u in
                        let h = H.fill_hole hole ~parent:p ~child:c in
                        h, u))))
          |> List.iter ~f:(fun (h, _) ->
              match H.kind h with
              | H.Concrete -> if H.verify h then never_returns (found h)
              | H.Abstract -> failwiths "BUG: Did not fill in all holes." h H.sexp_of_t);
          search (cost + 1)
        end
    in
    search initial_cost
end  

module Conflict_search = struct
  module H = Hypothesis
    
  let rec get parent hole spec cost =
    List.concat_map (L2_Generalizer.No_lambdas.generalize hole spec) ~f:(fun (p, p_u) ->
        match H.kind p with
        | H.Concrete -> if H.cost p = cost then [ (p, p_u) ] else []
        | H.Abstract -> if H.cost p >= cost then [] else
            let num_holes = List.length (H.holes p) in
            let all_hole_costs =
              Util.m_partition (cost - H.cost p) num_holes
              |> List.concat_map ~f:Util.permutations
            in
            let parent_hole = hole in
            List.concat_map all_hole_costs ~f:(fun hole_costs ->
                List.fold2_exn (H.holes p) hole_costs ~init:[ (p, p_u) ]
                  ~f:(fun hs (hole, spec) hole_cost ->
                      List.iter hs ~f:(fun (h, u) ->
                          let full_hypo = H.fill_hole parent_hole ~parent ~child:h in
                          begin
                            match Conflict.of_hypothesis full_hypo with
                            | Ok (`Conflict c) ->
                              printf "Found conflict!\n%s\n%s\n%!" (H.to_string_hum full_hypo)
                                (Sexp.to_string_hum (Conflict.sexp_of_t c))
                            | Ok `NoConflict -> printf "No conflict.\n%s\n%!" (H.to_string_hum full_hypo)
                            | Error err -> ()
                              (* printf "Error.\n%s\n%s\n%!" (H.to_string_hum h) (Error.to_string_hum err) *)
                          end;

                        );
                      
                      (* let hs = List.filter_map hs ~f:(fun (h, u) -> *)
                      (*     begin *)
                      (*       match Conflict.of_hypothesis (H.fill_hole parent_hole ~parent ~child:h) with *)
                      (*       | Ok (`Conflict c) -> *)
                      (*         printf "Found conflict!\n%s\n%s\n%!" (H.to_string_hum h) *)
                      (*           (Sexp.to_string_hum (Conflict.sexp_of_t c)) *)
                      (*       | Ok `NoConflict -> printf "No conflict.\n%s\n%!" (H.to_string_hum h) *)
                      (*       | Error err -> *)
                      (*         printf "Error.\n%s\n%s\n%!" (H.to_string_hum h) (Error.to_string_hum err) *)
                      (*     end; *)

                      (*     Option.map (L2_Deduction.push_specifications (H.skeleton h)) ~f:(fun s -> *)
                      (*         L2_Hypothesis.of_skeleton s, u)) *)
                      (* in *)
                      List.concat_map hs ~f:(fun (p, p_u) ->
                          let children = get p hole spec hole_cost in
                          List.map children ~f:(fun (c, c_u) ->
                              let u = Unifier.compose c_u p_u in
                              let h = H.fill_hole hole ~parent:p ~child:c in
                              h, u))))
            |> List.filter ~f:(fun (h, _) ->
                (* let () = Debug.eprintf "Verifying %d %s" h.H.cost (H.to_string_hum h) in *)
                match H.kind h with
                | H.Concrete -> H.verify h
                | H.Abstract -> failwiths "BUG: Did not fill in all holes." h H.sexp_of_t))  

  let search ~check_cost ~found hypo initial_cost =
    let rec search (cost: int) =
      (* If the cost of searching this level exceeds the max cost, end the search. *)
      if check_cost cost then cost else
        (* Otherwise, examine the next row in the search tree. *)
        begin
          let num_holes = List.length (H.holes hypo) in
          List.concat_map (Util.m_partition cost num_holes) ~f:(fun hole_costs ->
              List.fold2_exn (H.holes hypo) hole_costs ~init:[ (hypo, Unifier.empty) ]
                ~f:(fun hs (hole, spec) hole_cost -> List.concat_map hs ~f:(fun (p, p_u) ->
                    let children = get (L2_Hypothesis.hole hole spec) hole spec hole_cost in
                    List.map children ~f:(fun (c, c_u) ->
                        let u = Unifier.compose c_u p_u in
                        let h = H.fill_hole hole ~parent:p ~child:c in
                        h, u))))
          |> List.iter ~f:(fun (h, _) ->
              match H.kind h with
              | H.Concrete -> if H.verify h then never_returns (found h)
              | H.Abstract -> failwiths "BUG: Did not fill in all holes." h H.sexp_of_t);
          search (cost + 1)
        end
    in
    search initial_cost
end

module Make_L2_synthesizer (Search: Search_intf) = struct
  exception SynthesisException of Hypothesis.t

  let total_cost (hypo_cost: int) (enum_cost: int) : int =
    hypo_cost + (Int.of_float (1.5 ** (Float.of_int enum_cost)))

  let synthesize hypo ~cost:max_cost =
    let module H = Hypothesis in
    let fresh_hypos = ref [ (hypo, ref 0) ] in
    let stale_hypos = ref [] in

    try
      for cost = 1 to max_cost do
        (* Search each hypothesis that can be searched at this cost. If
           the search succeeds it will throw an exception. *)
        List.iter (!fresh_hypos @ !stale_hypos) ~f:(fun (hypo, max_search_cost) ->
            if total_cost (H.cost hypo) (!max_search_cost + 1) <= cost then
              let hypo_cost = H.cost hypo in
              max_search_cost :=
                Search.search hypo !max_search_cost
                  ~check_cost:(fun exh_cost -> total_cost hypo_cost exh_cost >= cost)
                  ~found:(fun h -> raise (SynthesisException h)));

        (* Generalize each hypothesis that is cheap enough to generalize. *)
        let (generalizable, remaining) =
          List.partition_tf !fresh_hypos ~f:(fun (h, _) -> H.cost h < cost)
        in
        let children = List.concat_map generalizable ~f:(fun (h, _) ->
            Generalizer.generalize_all L2_Generalizer.No_components.generalize h

            (* After generalizing, push specifications down the
               skeleton and filter skeletons with Bottom
               specifications. *)
            |> List.filter_map ~f:(fun h ->
                Option.map (L2_Deduction.push_specifications (H.skeleton h))
                  L2_Hypothesis.of_skeleton)
              
            |> List.map ~f:(fun h -> (h, ref 0)))
        in
        fresh_hypos := remaining @ children;
        stale_hypos := !stale_hypos @ generalizable;
      done; None
    with SynthesisException s -> Some s

  let initial_hypothesis examples =
    let exs = List.map examples ~f:(function
        | (`Apply (_, args), out) ->
          let ctx = StaticDistance.Map.empty in
          let args = List.map ~f:(Eval.eval (Ctx.empty ())) args in
          let ret = Eval.eval (Ctx.empty ()) out in
          ((ctx, args), ret)
        | ex -> failwiths "Unexpected example type." ex sexp_of_example)
              |> Specification.FunctionExamples.of_list_exn
    in
    let t = Infer.Type.normalize (Example.signature examples) in
    L2_Hypothesis.hole
      (Hole.create StaticDistance.Map.empty t L2_Generalizer.Symbols.lambda)
      (Specification.FunctionExamples exs)
end

module L2_Synthesizer = Make_L2_synthesizer(Conflict_search)
