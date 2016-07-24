open Core.Std

open Synthesis_common

open Ast
open Collections
open Hypothesis
open Infer

let default_cost_model : CostModel.t =
  let module Sk = Skeleton in
  let module C = CostModel in
  {
    C.num = (fun _ -> 1);
    C.bool = (fun _ -> 1);
    C.hole = (fun _ -> 0);
    C.lambda = (fun _ _ -> 1);
    C._let = (fun _ _ -> 1);
    C.list = (fun _ -> 1);
    C.tree = (fun _ -> 1);
    C.apply = (fun _ _ -> 0);
    C.op = (fun op _ -> Expr.Op.cost op);
    C.id = function
      | Sk.Id.Name name -> begin match name with
          | "foldr"
          | "foldl"
          | "foldt" -> 3
          | "map"
          | "mapt"
          | "filter" -> 2
          | _ -> 1
        end
      | Sk.Id.StaticDistance sd -> 1;
  }
  
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

  module type S = sig
    val create : CostModel.t -> Library.t -> Generalizer.t
  end

  module Symbols = struct
    let lambda = Symbol.create "Lambda"
    let combinator = Symbol.create "Combinator"
    let expression = Symbol.create "Expression"
    let constant = Symbol.create "Constant"
    let identifier = Symbol.create "Identifier"
    let base_case = Symbol.create "BaseCase"    
  end
  open Symbols

  module G = Generalizer
  module Sp = Specification
  module H = Hypothesis

  let combinators = [
    "map"; "mapt"; "filter"; "foldl"; "foldr"; "foldt"; "rec"
  ]

  let generate_constants params ctx type_ symbol spec =
    let cost_model = params.G.cost_model in
    let constants = [
      Type.num, [
        H.num cost_model 0 spec;
        H.num cost_model 1 spec;
        H.num cost_model Int.max_value spec;
      ];
      Type.bool, [
        H.bool cost_model true spec;
        H.bool cost_model false spec;
      ];
      Type.list (Type.quant "a") |> instantiate 0, [
        H.list cost_model [] spec;
      ]
    ] in
    List.concat_map constants ~f:(fun (t, xs) ->
        match Infer.Unifier.of_types type_ t with
        | Some u -> List.map xs ~f:(fun x -> (x, u))
        | None -> [])

  let generate_identifiers params ctx type_ symbol spec =
    List.filter_map (StaticDistance.Map.to_alist ctx) ~f:(fun (id, id_t) ->
        Option.map (Unifier.of_types type_ id_t) ~f:(fun u ->
            H.id_sd params.G.cost_model id spec, u))

  let generate_expressions params ctx type_ symbol spec =
    let cost_model = params.G.cost_model in
    let op_exprs = List.filter_map Expr.Op.all ~f:(fun op ->
        let op_t = instantiate 0 (Expr.Op.meta op).Expr.Op.typ in
        match op_t with
        | Arrow_t (args_t, ret_t) ->
          (* Try to unify the return type of the operator with the type of the hole. *)
          Option.map (Unifier.of_types type_ ret_t) ~f:(fun u ->
              (* If unification succeeds, apply the unifier to the rest of the type. *)
              let args_t = List.map args_t ~f:(Unifier.apply u) in
              let arg_holes = List.map args_t ~f:(fun t ->
                  H.hole cost_model (Hole.create ~ctx t expression) Sp.top)
              in
              H.op cost_model op arg_holes spec, u)
        | _ -> None)
    in
    let functions =
      String.Map.filteri params.G.library.Library.type_ctx ~f:(fun ~key:k ~data:_ ->
          not (List.mem ~equal:String.equal combinators k))
      |> String.Map.to_alist
    in
    let apply_exprs = List.filter_map functions ~f:(fun (func, func_t) ->
        let func_t = instantiate 0 func_t in
        match func_t with
        | Arrow_t (args_t, ret_t) ->
          (* Try to unify the return type of the operator with the type of the hole. *)
          Option.map (Unifier.of_types type_ ret_t) ~f:(fun u ->
              (* If unification succeeds, apply the unifier to the rest of the type. *)
              let args_t = List.map args_t ~f:(Unifier.apply u) in
              let arg_holes = List.map args_t ~f:(fun t ->
                  H.hole cost_model (Hole.create ~ctx t expression) Sp.top)
              in
              H.apply cost_model (H.id_name cost_model func Sp.top) arg_holes spec, u)
        | _ -> None)
    in
    op_exprs @ apply_exprs

  let generate_lambdas params ctx type_ symbol spec =
    let cost_model = params.G.cost_model in
    match type_ with
    (* If the hole has an arrow type, generate a lambda expression with
       the right number of arguments and push the specification down. *)
    | Arrow_t (args_t, ret_t) ->
      let num_args = List.length args_t in
      let arg_names = StaticDistance.args num_args in
      let type_ctx =
        List.fold (List.zip_exn arg_names args_t)
          ~init:(StaticDistance.map_increment_scope ctx)
          ~f:(fun ctx (arg, arg_t) -> StaticDistance.Map.add ctx ~key:arg ~data:arg_t)
      in
      let lambda =
        H.lambda cost_model num_args (H.hole cost_model (Hole.create ~ctx:type_ctx ret_t combinator) Sp.top) spec
      in
      [ lambda, Unifier.empty ]
    | _ -> []

  let generate_combinators params ctx type_ symbol spec =
    let cost_model = params.G.cost_model in
    String.Map.to_alist params.G.library.Library.type_ctx
    |> List.filter_map ~f:(fun (func, func_t) ->
        if List.mem ~equal:String.equal combinators func then
          let func_t = instantiate 0 func_t in
          match func_t with
          | Arrow_t (args_t, ret_t) ->
            (* Try to unify the return type of the operator with the type of the hole. *)
            Option.map (Unifier.of_types ret_t type_) ~f:(fun u ->
                (* If unification succeeds, apply the unifier to the rest of the type. *)
                let args_t = List.map args_t ~f:(Infer.Unifier.apply u) in
                let arg_holes = match (func, args_t) with
                  | "map", [ t1; t2 ]
                  | "mapt", [ t1; t2 ]
                  | "filter", [ t1; t2 ] -> [
                      H.hole cost_model (Hole.create ~ctx:ctx t1 identifier) Sp.top;
                      H.hole cost_model (Hole.create ~ctx:ctx t2 lambda) Sp.top;
                    ]
                  | "foldr", [ t1; t2; t3 ]
                  | "foldl", [ t1; t2; t3 ]
                  | "foldt", [ t1; t2; t3 ] -> [
                      H.hole cost_model (Hole.create ~ctx:ctx t1 identifier) Sp.top;
                      H.hole cost_model (Hole.create ~ctx:ctx t2 lambda) Sp.top;
                      H.hole cost_model (Hole.create ~ctx:ctx t3 base_case) Sp.top;
                    ]
                  | name, args -> List.map args ~f:(function
                      | Arrow_t _ as t -> H.hole cost_model (Hole.create ~ctx:ctx t lambda) Sp.top
                      | t -> H.hole cost_model (Hole.create ~ctx:ctx t expression) Sp.top)
                in
                H.apply cost_model (H.id_name cost_model func Sp.top) arg_holes spec, u)
          | _ -> None
        else None)

  let create select cost_model library =
    let params = { G.cost_model; G.library } in
    let generalize ctx type_ symbol spec =
      let generators = select symbol in
      List.concat (List.map generators ~f:(fun g -> g params ctx type_ symbol spec))
    in
    generalize

  module With_components = struct
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

    let create = create select
  end

  module No_components = struct
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

    let create = create select
  end

  module No_lambdas = struct
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

    let create = create select
  end
end

module L2_Synthesizer = struct
  type t = {
    cost_model : CostModel.t;
    gen_no_lambdas : Generalizer.t;
    gen_no_components : Generalizer.t;
    deduce : Deduction.t;
    memoizer : Memoizer.t;
    library : Library.t;
  }
  
  exception SynthesisException of Hypothesis.t

  let create ?(cost_model=default_cost_model) deduce library =
    let gen_no_lambdas = L2_Generalizer.No_lambdas.create cost_model library in
    let gen_no_components = L2_Generalizer.No_components.create cost_model library in
    {
      gen_no_lambdas; gen_no_components; deduce; cost_model; library; 
      memoizer =
        let open Memoizer.Config in
        Memoizer.create {
          library; cost_model;
          deduction = deduce;
          generalize = gen_no_lambdas;
          search_space_out = None;
        };
    }
  
  let search s ~check_cost ~found hypo initial_cost =  
    let module H = Hypothesis in
    let rec search (cost: int) =
      (* If the cost of searching this level exceeds the max cost, end the search. *)
      if check_cost cost then cost else
        match Sequence.hd (Memoizer.fill_holes_in_hypothesis s.memoizer hypo (cost + H.cost hypo)) with
        | Some (sln, _) -> never_returns (found sln)
        | None -> search (cost + 1)
    in
    search initial_cost

  let total_cost (hypo_cost: int) (enum_cost: int) : int =
    hypo_cost + (Int.of_float (1.5 ** (Float.of_int enum_cost)))

  let synthesize ?max_cost s hypo =
    let module H = Hypothesis in
    let fresh_hypos = ref [ (hypo, ref 0) ] in
    let stale_hypos = ref [] in

    let should_continue = match max_cost with
      | Some c -> fun c' -> c' < c
      | None -> fun _ -> true
    in

    let rec loop cost =
      (* Search each hypothesis that can be searched at this cost. If
         the search succeeds it will throw an exception. *)
      List.iter (!fresh_hypos @ !stale_hypos) ~f:(fun (hypo, max_search_cost) ->
          if total_cost (H.cost hypo) (!max_search_cost + 1) <= cost then
            let hypo_cost = H.cost hypo in
            max_search_cost :=
              search s hypo !max_search_cost
                ~check_cost:(fun exh_cost -> total_cost hypo_cost exh_cost >= cost)
                ~found:(fun h -> raise (SynthesisException h)));

      (* Generalize each hypothesis that is cheap enough to generalize. *)
      let (generalizable, remaining) =
        List.partition_tf !fresh_hypos ~f:(fun (h, _) -> H.cost h < cost)
      in
      let children = List.concat_map generalizable ~f:(fun (h, _) ->
          let params = {
            Generalizer.library = s.library;
            Generalizer.cost_model = s.cost_model;
          } in
          Generalizer.generalize_all params s.gen_no_components h

          (* After generalizing, push specifications down the
             skeleton and filter skeletons with Bottom
             specifications. *)
          |> List.filter_map ~f:(fun h ->
              Option.map (s.deduce (H.skeleton h))
                (Hypothesis.of_skeleton s.cost_model))

          |> List.map ~f:(fun h -> (h, ref 0)))
      in
      fresh_hypos := remaining @ children;
      stale_hypos := !stale_hypos @ generalizable;
      if should_continue cost then loop (cost + 1) else ()
    in
    try
      loop 1; Ok None
    with SynthesisException s -> Ok (Some s)

  let initial_hypothesis s examples =
    let spec =
      List.map examples ~f:(function
          | (`Apply (_, args), out) ->
            let ctx = StaticDistance.Map.empty in
            let args = List.map ~f:(Eval.eval (Ctx.empty ())) args in
            let ret = Eval.eval (Ctx.empty ()) out in
            ((ctx, args), ret)
          | ex -> failwiths "Unexpected example type." ex sexp_of_example)
      |> FunctionExamples.of_list_exn
      |> FunctionExamples.to_spec
    in
    let t = Infer.Type.normalize (Example.signature examples) in
    Hypothesis.hole s.cost_model
      (Hole.create t L2_Generalizer.Symbols.lambda)
      spec
end
