open Core
open Synthesis_common
open Ast
open Collections
open Hypothesis
open Infer

let default_cost_model : CostModel.t =
  let module Sk = Skeleton in
  let module C = CostModel in
  { C.num= (fun _ -> 1)
  ; C.bool= (fun _ -> 1)
  ; C.hole= (fun _ -> 0)
  ; C.lambda= (fun _ _ -> 1)
  ; C._let= (fun _ _ -> 1)
  ; C.list= (fun _ -> 1)
  ; C.tree= (fun _ -> 1)
  ; C.apply= (fun _ _ -> 0)
  ; C.op= (fun op _ -> Expr.Op.cost op)
  ; C.id=
      (function
      | Sk.Id.Name name -> (
        match name with
        | "foldr" | "foldl" | "foldt" | "zipWith" -> 3
        | "map" | "mapt" | "filter" -> 2
        | _ -> 1 )
      | Sk.Id.StaticDistance _ -> 1) }

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

  let generate_constants params _ type_ _ spec =
    match type_ with
    | Arrow_t _ -> []
    | _ ->
        let cost_model = params.G.cost_model in
        let constants =
          [ ( Type.num
            , [ H.num cost_model 0 spec
              ; H.num cost_model 1 spec
              ; H.num cost_model Int.max_value spec ] )
          ; (Type.bool, [H.bool cost_model true spec; H.bool cost_model false spec])
          ; ( Type.list (Type.quant "a") |> instantiate 0
            , [H.list cost_model [] spec] ) ]
        in
        List.concat_map constants ~f:(fun (t, xs) ->
            match Infer.Unifier.of_types type_ t with
            | Some u -> List.map xs ~f:(fun x -> (x, u))
            | None -> [] )

  let generate_identifiers params ctx type_ _ spec =
    match type_ with
    | Arrow_t _ -> []
    | _ ->
        List.filter_map (StaticDistance.Map.to_alist ctx) ~f:(fun (id, id_t) ->
            Option.map (Unifier.of_types type_ id_t) ~f:(fun u ->
                (H.id_sd params.G.cost_model id spec, u) ) )

  let generate_expressions params ctx type_ _ spec =
    match type_ with
    | Arrow_t _ -> []
    | _ ->
        let cost_model = params.G.cost_model in
        let op_exprs =
          List.filter_map params.G.library.Library.builtins ~f:(fun op ->
              let op_t = instantiate 0 (Expr.Op.meta op).Expr.Op.typ in
              match op_t with
              | Arrow_t (args_t, ret_t) ->
                  (* Try to unify the return type of the operator with the type of the hole. *)
                  Option.map (Unifier.of_types type_ ret_t) ~f:(fun u ->
                      (* If unification succeeds, apply the unifier to the rest of the type. *)
                      let args_t = List.map args_t ~f:(Unifier.apply u) in
                      let arg_holes =
                        List.map args_t ~f:(fun t ->
                            H.hole cost_model (Hole.create ~ctx t expression) Sp.top
                        )
                      in
                      (H.op cost_model op arg_holes spec, u) )
              | _ -> None )
        in
        let functions = params.G.library.Library.type_ctx |> String.Map.to_alist in
        let apply_exprs =
          List.filter_map functions ~f:(fun (func, func_t) ->
              let func_t = instantiate 0 func_t in
              match func_t with
              | Arrow_t (args_t, ret_t) ->
                  (* Try to unify the return type of the operator with the type of the hole. *)
                  Option.map (Unifier.of_types type_ ret_t) ~f:(fun u ->
                      (* If unification succeeds, apply the unifier to the rest of the type. *)
                      let args_t = List.map args_t ~f:(Unifier.apply u) in
                      let arg_holes =
                        List.map args_t ~f:(fun t ->
                            H.hole cost_model (Hole.create ~ctx t expression) Sp.top
                        )
                      in
                      ( H.apply cost_model
                          (H.id_name cost_model func Sp.top)
                          arg_holes spec
                      , u ) )
              | _ -> None )
        in
        op_exprs @ apply_exprs

  let generate_lambdas params ctx type_ _ spec =
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
            ~f:(fun ctx (arg, arg_t) ->
              StaticDistance.Map.set ctx ~key:arg ~data:arg_t )
        in
        let lambda =
          H.lambda cost_model num_args
            (H.hole cost_model (Hole.create ~ctx:type_ctx ret_t combinator) Sp.top)
            spec
        in
        [(lambda, Unifier.empty)]
    | _ -> []

  let create select cost_model library =
    let params = {G.cost_model; G.library} in
    let generalize ctx type_ symbol spec =
      let generators = select symbol in
      List.concat (List.map generators ~f:(fun g -> g params ctx type_ symbol spec))
    in
    generalize

  module With_components = struct
    let select _ =
      [ generate_constants
      ; generate_identifiers
      ; generate_expressions
      ; generate_lambdas ]

    let create = create select
  end

  module No_components = struct
    let select _ =
      [ generate_constants
      ; generate_identifiers
      ; generate_expressions
      ; generate_lambdas ]

    let create = create select
  end

  module No_lambdas = struct
    let select _ =
      [ generate_constants
      ; generate_identifiers
      ; generate_expressions
      ; generate_lambdas ]

    let create = create select
  end
end

module L2_Synthesizer = struct
  type t =
    { cost_model: CostModel.t
    ; gen_no_lambdas: Generalizer.t
    ; gen_no_components: Generalizer.t
    ; deduce: Deduction.t
    ; memoizer: Memoizer.t
    ; library: Library.t }

  let create ?(cost_model = default_cost_model) deduce library =
    let gen_no_lambdas = L2_Generalizer.No_lambdas.create cost_model library in
    let gen_no_components =
      L2_Generalizer.No_components.create cost_model library
    in
    { gen_no_lambdas
    ; gen_no_components
    ; deduce
    ; cost_model
    ; library
    ; memoizer=
        (let open Memoizer.Config in
        Memoizer.create
          { library
          ; cost_model
          ; deduction= deduce
          ; generalize= gen_no_lambdas
          ; search_space_out= None }) }

  let synthesize ?(max_cost = Int.max_value) s hypo =
    let module H = Hypothesis in
    let rec search (cost : int) =
      (* If the cost of searching this level exceeds the max cost, end the search. *)
      if cost > max_cost then Ok None
      else
        let candidates =
          Memoizer.fill_holes_in_hypothesis s.memoizer hypo (cost + H.cost hypo)
        in
        match Sequence.hd candidates with
        | Some (sln, _) -> Ok (Some sln)
        | None -> search (cost + 1)
    in
    search 0

  let initial_hypothesis s examples =
    let spec =
      List.map examples ~f:(function
        | `Apply (_, args), out ->
            let ctx = StaticDistance.Map.empty in
            let args = List.map ~f:(Eval.eval (Ctx.empty ())) args in
            let ret = Eval.eval (Ctx.empty ()) out in
            ((ctx, args), ret)
        | ex -> failwiths "Unexpected example type." ex sexp_of_example )
      |> FunctionExamples.of_list_exn |> FunctionExamples.to_spec
    in
    let t = Infer.Type.normalize (Example.signature examples) in
    Hypothesis.hole s.cost_model (Hole.create t L2_Generalizer.Symbols.lambda) spec
end
