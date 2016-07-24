open Core.Std

open Collections
open Hypothesis
open Infer
open Synthesis_common
open Util

module Sk = Skeleton
module Sp = Specification
module H = Hypothesis

type config = {
  max_cost : int;
  verbose : bool;
  library : Library.t;
}

type example = ExprValue.t list * ExprValue.t [@@deriving sexp, bin_io]

let cost_model =
  let module CM = CostModel in
  {
    CM.num = (fun x -> 1);
    CM.bool = (fun _ -> 1);
    CM.hole = (fun _ -> 0);
    CM.lambda = (fun _ _ -> 1);
    CM._let = (fun _ _ -> 1);
    CM.list = (fun _ -> 1);
    CM.tree = (fun _ -> 1);
    CM.apply = (fun _ _ -> 1);
    CM.op = (fun _ _ -> 1);
    CM.id = (fun _ -> 1);
  }

module Value_generalizer = struct
  module SD = StaticDistance
  module T = Type
    
  let sym = Symbol.create ""
  
  let generate_bool () = [
    (H.bool cost_model true Sp.top, Unifier.empty);
    (H.bool cost_model false Sp.top, Unifier.empty);
  ]

  let generate_int type_ spec = [
    H.num cost_model 0 spec, Unifier.empty;
    H.apply cost_model
      (H.id_name cost_model "N" Sp.top)
      [H.hole cost_model (Hole.create (T.Const_t T.Num_t) sym) Sp.top] spec, Unifier.empty;
    ]
              
  let generate_var type_ spec = [
    H.apply cost_model
      (H.id_name cost_model "V" Sp.top) [H.num cost_model 0 spec] spec, Unifier.empty;
    H.apply cost_model
      (H.id_name cost_model "V" Sp.top) [H.hole cost_model (Hole.create type_ sym) Sp.top] spec, Unifier.empty;
    ]

  let generate_list type_ spec elem_t = [
    H.list cost_model [] spec, Unifier.empty;
    H.op cost_model Expr.Op.Cons [H.hole cost_model (Hole.create elem_t sym) Sp.top;
                                  H.hole cost_model (Hole.create type_ sym) Sp.top] spec, Unifier.empty;
    ]

  let rec gen ctx type_ symbol spec =
    let open Type in
    let out = match type_ with
      | Const_t Num_t -> generate_int type_ spec
      | Const_t Bool_t -> generate_bool ()
      | App_t ("list", [elem_t]) -> generate_list type_ spec elem_t
      | Var_t { contents = Quant _ } -> generate_var type_ spec
      | Var_t { contents = Link t } -> gen ctx t symbol spec
      | t -> failwiths "Unexpected type." t [%sexp_of:Type.t]
    in
    out

  let of_type : ImmutableType.t -> (Generalizer.t * Hypothesis.t) = fun t ->
    let init = H.hole cost_model (Hole.create (ImmutableType.to_type t) sym) Sp.top in
    (gen, init)
end

let rec convert : 'a Sk.t -> 'a Sk.t =
  let convert_var sk =
    let rec var = function
      | Sk.Num_h (x, _) -> x
      | Sk.Apply_h ((Sk.Id_h (Sk.Id.Name "V", _), [v]), _) -> 1 + (var v)
      | _ -> failwith "Malformed var."
    in
    Sk.Id_h (Sk.Id.Name ("v" ^ (Int.to_string (var sk))), Sp.top)
  in
  let convert_int sk =
    let rec int = function
      | Sk.Num_h (x, _) -> x
      | Sk.Apply_h ((Sk.Id_h (Sk.Id.Name "N", _), [v]), _) -> 1 + (int v)
      | _ -> failwith "Malformed int."
    in
    Sk.Num_h (int sk, Sp.top)
  in
  let convert_list sk =
    let rec list = function
      | Sk.List_h ([], _) -> []
      | Sk.Op_h ((Expr.Op.Cons, [x; xs]), _) -> x::(list xs)
      | _ -> failwith "Malformed list."
    in
    Sk.List_h (list sk, Sp.top)
  in
  function
  | Sk.Hole_h _ 
  | Sk.Id_h _
  | Sk.Num_h _
  | Sk.Bool_h _ as sk -> sk
  | Sk.Apply_h ((Sk.Id_h (Sk.Id.Name "V", _), _), _) as sk -> convert (convert_var sk)
  | Sk.Apply_h ((Sk.Id_h (Sk.Id.Name "N", _), _), _) as sk -> convert (convert_int sk)
  | Sk.Op_h ((Expr.Op.Cons, _), _) as sk -> convert (convert_list sk)
  | Sk.Apply_h ((x, y), s) -> Sk.Apply_h ((convert x, List.map ~f:convert y), s)
  | Sk.Op_h ((x, y), s) -> Sk.Op_h ((x, List.map ~f:convert y), s)
  | Sk.List_h (x, s) -> Sk.List_h (List.map ~f:convert x, s)
  | Sk.Tree_h (x, s) -> Sk.Tree_h (Tree.map ~f:convert x, s)
  | Sk.Let_h ((x, y), s) -> Sk.Let_h ((convert x, convert y), s)
  | Sk.Lambda_h ((x, y), s) -> Sk.Lambda_h ((x, convert y), s)

let generate_examples : config:config -> Expr.t -> Type.t -> example Sequence.t =
  let module IT = ImmutableType in
  fun ~config func type_ ->
    let func_ev = ExprValue.of_expr func in
    match IT.of_type type_ with
    | ImmutableType.Arrow_i (args_t, _) ->
      let gens, inits =
        List.map args_t ~f:Value_generalizer.of_type
        |> List.unzip
      in
      let init = H.list cost_model inits Sp.top in
      let memo =
        let open Memoizer.Config in
        Memoizer.create {
          library = Library.empty;
          generalize = Generalizer.compose_all_exn gens;
          deduction = Deduction.no_op;
          search_space_out = None;
          cost_model;
        } in
      Memoizer.to_flat_sequence memo ~max_cost:config.max_cost init
        
      |> Sequence.map ~f:(fun (args, _) -> match H.skeleton args with
          | Sk.List_h (args_sk, _) -> args_sk
          | sk -> failwiths "Unexpected skeleton." sk [%sexp_of:Sp.t Sk.t])

      |> Sequence.map ~f:(List.map ~f:convert)
        
      |> Sequence.filter_map ~f:(fun args_sk ->
            let args_exprv =
              List.map args_sk ~f:Sk.to_expr
              |> List.map ~f:ExprValue.of_expr
            in
            begin try
                let ret_ev =
                  Eval.partial_eval
                    ~ctx:(ref config.library.Library.exprvalue_ctx) (`Apply (func_ev, args_exprv)) in
                Some (args_exprv, ret_ev)
              with Eval.RuntimeError err -> printf "ERROR: %s\n" (Error.to_string_hum err); None
            end)
        
    | t -> failwiths "Unexpected type." t [%sexp_of:IT.t]

let save_examples : file:string -> example Sequence.t -> unit =
  fun ~file exs ->
    let ch = open_out file in
    Sequence.iter exs ~f:(fun ex ->
        Sexp.output_mach ch ([%sexp_of:example] ex))

let view_sequence : 'a Sequence.t -> f:('a -> string) -> 'a Sequence.t = fun s ~f ->
  Sequence.map s ~f:(fun x -> printf "%s\n" (f x); flush stdout; x)

let generate_for_func : config:config -> file:string -> Expr.t -> Type.t -> unit =
  fun ~config ~file func type_ ->
    let exs = generate_examples ~config func type_ in
    let exs = if config.verbose then 
        view_sequence exs ~f:(fun (ins, out) ->
          sprintf "(%s) -> %s"
            (List.map ins ~f:ExprValue.to_string |> String.concat ~sep:", ")
            (ExprValue.to_string out))
      else exs
    in
    save_examples ~file exs

let spec =
  let open Command.Spec in
  empty
  +> flag "--cost" (required int) ~doc:" the maximum specification cost"
  +> flag "-v" ~aliases:["--verbose"] no_arg ~doc:" print verbose output"
  +> anon ("library" %: file)
  +> anon (sequence ("function" %: string))

let run max_cost verbose library_fn names () =
  let err =
    let module Let_syntax = Or_error.Let_syntax.Let_syntax in
    let%bind library = Library.from_file library_fn in

    let config = { max_cost; verbose; library } in
    
    let functions =
      library.Library.type_ctx |> Map.to_alist |> List.map ~f:(fun (name, type_) ->
          let args_names = List.init (Type.arity type_) ~f:(fun i -> Int.to_string i) in
          let args_ids = List.map args_names ~f:(fun n -> `Id n) in
          (name, type_, `Lambda (args_names, `Apply (`Id name, args_ids))))
    in
    
    let operators = Expr.Op.all |> List.map ~f:(fun op ->
        let name = Expr.Op.to_string op in
        let type_ = Expr.Op.typ op in
        let args_names = List.init (Expr.Op.arity op) ~f:(fun i -> Int.to_string i) in
        let args_ids = List.map args_names ~f:(fun n -> `Id n) in
        (name, type_, `Lambda (args_names, `Op (op, args_ids))))
    in
    
    let selected = 
      List.filter (functions @ operators) ~f:(fun (n, _, _) -> List.mem names n)
    in

    List.iter selected ~f:(fun (name, type_, expr) ->
        let file = name ^ "-examples.sexp" in
        generate_for_func ~config ~file expr type_);

    Ok ()
  in

  match err with
  | Ok () -> ()
  | Error err -> print_string (Error.to_string_hum err)

let cmd = Command.basic ~summary:"Generate specifications for functions." spec run
