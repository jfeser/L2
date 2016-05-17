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
    CM.num = (fun x -> x);
    CM.bool = (fun _ -> 1);
    CM.hole = (fun _ -> 1);
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
    
  let sym = Symbol.create ""
  
  let name_of_int n = "v" ^ (Int.to_string n)

  let spec_of_int x = Sp.Examples (Sp.Examples.singleton (SD.Map.empty, `Num x))
  let int_of_spec = function
    | Sp.Examples exs ->
      let rets =
        Sp.Examples.to_list exs
        |> List.map ~f:Tuple.T2.get2
        |> List.dedup
      in
      begin match rets with
        | [`Num x] -> Some x
        | _ -> None
      end
    | _ -> None

  let generate_bool () = [
    (H.bool cost_model true Sp.Top, Unifier.empty);
    (H.bool cost_model false Sp.Top, Unifier.empty);
  ]

  let generate_int type_ spec =
    match int_of_spec spec with
    | Some x -> [
        H.num cost_model x spec, Unifier.empty;
        H.num cost_model (-x) spec, Unifier.empty;
        H.hole cost_model (Hole.create type_ sym) (spec_of_int (x + 1)), Unifier.empty;
      ]
    | None -> [
        H.num cost_model 0 spec, Unifier.empty;
        H.hole cost_model (Hole.create type_ sym) (spec_of_int 1), Unifier.empty;
      ]
              
  let generate_var type_ spec =
    match int_of_spec spec with
    | Some x -> [
        H.id_name cost_model (name_of_int x) spec, Unifier.empty;
        H.hole cost_model (Hole.create type_ sym) (spec_of_int (x + 1)), Unifier.empty;
      ]
    | None -> [
        H.id_name cost_model "v0" spec, Unifier.empty;
        H.hole cost_model (Hole.create type_ sym) (spec_of_int 1), Unifier.empty;
      ]

  let generate_list type_ spec elem_t = match int_of_spec spec with
    | Some x -> [
        H.list cost_model (List.init x ~f:(fun _ ->
            H.hole cost_model (Hole.create elem_t sym) Sp.Top))
          spec, Unifier.empty;
        H.hole cost_model (Hole.create type_ sym) (spec_of_int (x + 1)), Unifier.empty;
      ]
    | None -> [
        H.list cost_model [] spec, Unifier.empty;
        H.hole cost_model (Hole.create type_ sym) (spec_of_int 1), Unifier.empty;
      ]

  let rec gen ctx type_ symbol spec =
    print_sexp type_ [%sexp_of:Type.t];
    let open Type in
    match type_ with
    | Const_t Num_t -> generate_int type_ spec
    | Const_t Bool_t -> generate_bool ()
    | App_t ("list", [elem_t]) ->
      let out = generate_list type_ spec elem_t in
      print_sexp out [%sexp_of:(H.t * Infer.Unifier.t) list];
      out
    | Var_t { contents = Quant _ } -> generate_var type_ spec
    | Var_t { contents = Link t } -> gen ctx t symbol spec
    | t -> failwiths "Unexpected type." t [%sexp_of:Type.t]

  let of_type : ImmutableType.t -> (Generalizer.t * Hypothesis.t) = fun t ->
    let init = H.hole cost_model (Hole.create (ImmutableType.to_type t) sym) Sp.Top in
    (gen, init)
end

let rename_vars : 'a Sk.t -> int -> ('a Sk.t * int) = fun s init_i ->
  let i = ref init_i in
  let rec rename = function
    | Sk.Num_h _
    | Sk.Bool_h _ as sk -> sk
    | Sk.Id_h (Sk.Id.Name name, s) ->
      let name' = name ^ (Int.to_string !i) in
      incr i;
      Sk.Id_h (Sk.Id.Name name', s)
    | Sk.Id_h (name, s) -> Sk.Id_h (name, s)
    | Sk.Hole_h (h, s) -> Sk.Hole_h (h, s)
    | Sk.List_h (x, s) -> Sk.List_h (List.map ~f:rename x, s)
    | Sk.Tree_h (x, s) -> Sk.Tree_h (Tree.map ~f:rename x, s)
    | Sk.Let_h ((x, y), s) -> Sk.Let_h ((rename x, rename y), s)
    | Sk.Lambda_h ((x, y), s) -> Sk.Lambda_h ((x, rename y), s)
    | Sk.Apply_h ((x, y), s) -> Sk.Apply_h ((rename x, List.map ~f:rename y), s)
    | Sk.Op_h ((x, y), s) -> Sk.Op_h ((x, List.map ~f:rename y), s)
  in
  (rename s, !i)

let rename_args_vars : 'a Sk.t list -> 'a Sk.t list = fun args ->
  let (_, args') = List.fold_left args ~init:(0, []) ~f:(fun (i, args) arg ->
      let (arg', i') = rename_vars arg i in
      (i', arg'::args))
  in
  List.rev args'

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
      let init = H.list cost_model inits Sp.Top in
      let memo =
        let open Memoizer.Config in
        Memoizer.create {
          library = Library.empty;
          generalize = Generalizer.compose_all_exn gens;
          deduction = Deduction.no_op;
          cost_model;
        } in
      Memoizer.to_flat_sequence memo ~max_cost:config.max_cost init
        
      |> Sequence.map ~f:(fun (args, _) -> match H.skeleton args with
          | Sk.List_h (args_sk, _) -> args_sk
          | sk -> failwiths "Unexpected skeleton." sk [%sexp_of:Sp.t Sk.t])

      |> Sequence.map ~f:rename_args_vars
        
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
