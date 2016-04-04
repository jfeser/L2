open Core.Std

open Collections
open Hypothesis
open Infer
open Synthesis_common

module Sk = Skeleton
module Sp = Specification
module H = Hypothesis

type example = ExprValue.t list * ExprValue.t [@@deriving sexp, bin_io]

let print_sexp x s = print_endline (Sexp.to_string_hum (s x))

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
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list

  module Symbols = struct
    let num = Symbol.create "num"
    let bool = Symbol.create "bool"
    let var = Symbol.create "var"
    let list_var = Symbol.create "list[var]"
  end
  
  module Schema = struct
    type t = Symbol.t KTree.t [@@deriving sexp]

    let rec of_type : ImmutableType.t -> t =
      let module IT = ImmutableType in
      let module T = Type in
      function
      | IT.Const_i (T.Num_t) -> KTree.Leaf Symbols.num
      | IT.Const_i (T.Bool_t) -> KTree.Leaf Symbols.bool
      | IT.Quant_i _ -> KTree.Leaf Symbols.var
      | IT.App_i ("list", [IT.Quant_i _]) -> KTree.Leaf Symbols.list_var
      | IT.App_i (name, args) -> KTree.Node (Symbol.create name, List.map args ~f:of_type)
      | t -> failwiths "Unexpected type." t [%sexp_of:IT.t]

    let rec args_of : t -> Symbol.t -> Symbol.t list option = fun schema sym ->
      match schema with
      | KTree.Leaf sym' ->
        if Symbol.equal sym sym' then Some [] else None
      | KTree.Node (sym', ch) ->
        if Symbol.equal sym sym' then Some (List.map ch ~f:KTree.value) else
          List.find_map ch ~f:(fun s -> args_of s sym)
  end
  
  module SD = StaticDistance

  let name_of_int n = "v" ^ (Int.to_string n)

  let generate_bool hole spec = [
    (H.bool cost_model true spec, Unifier.empty);
    (H.bool cost_model false spec, Unifier.empty);
  ]

  let generate_int hole spec =
    List.init 20 ~f:(fun x -> H.num cost_model x spec, Unifier.empty)

  let generate_var hole spec =
    [H.id_name cost_model "v" spec, Unifier.empty]

  let generate_list_var hole spec =
    let max_length = 50 in
    let vars =
      List.repeat max_length (H.id_name cost_model "v" spec)
    in
    List.init (max_length + 1) ~f:(fun i -> (H.list cost_model (List.take vars i) spec, Unifier.empty))
  
  let generate_list list_sym elem_sym hole spec = [
    (H.op cost_model Expr.Op.Cons [
        H.hole cost_model (Hole.create ~ctx:hole.Hole.ctx (Type.free 0 0) elem_sym) Sp.Top;
        H.hole cost_model (Hole.create ~ctx:hole.Hole.ctx (Type.free 0 0) list_sym) Sp.Top;
    ] Sp.Top, Unifier.empty);
    (H.list cost_model [] Sp.Top, Unifier.empty);
  ]

  let of_type : ImmutableType.t -> (t * Hypothesis.t) = fun t ->
    let schema = Schema.of_type t in
    print_sexp schema [%sexp_of:Schema.t];
    let gen = fun hole spec ->
      if hole.Hole.symbol = Symbols.num then
        generate_int hole spec
      else if hole.Hole.symbol = Symbols.bool then
        generate_bool hole spec
      else if hole.Hole.symbol = Symbols.var then
        generate_var hole spec
      else if hole.Hole.symbol = Symbols.list_var then
        generate_list_var hole spec
      else if (Symbol.to_string hole.Hole.symbol) = "list" then
        match Schema.args_of schema hole.Hole.symbol with
        | Some [elem_sym] -> generate_list hole.Hole.symbol elem_sym hole spec
        | _ -> (* failwiths "Bad schema." schema [%sexp_of:Schema.t] *) []
      else (* failwiths "Unknown symbol." hole.Hole.symbol [%sexp_of:Symbol.t] *) []
    in
    let init = H.hole cost_model (Hole.create (Type.free 0 0) (KTree.value schema)) Sp.Top in
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

let generate_examples : max_cost:int -> Expr.t -> Type.t -> example Sequence.t =
  let module IT = ImmutableType in
  fun ~max_cost func type_ ->
    let func_ev = ExprValue.of_expr func in
    match IT.of_type type_ with
    | ImmutableType.Arrow_i (args_t, _) ->
      let gens, inits =
        List.map args_t ~f:Value_generalizer.of_type
        |> List.unzip
      in
      let gen = Generalizer.compose_all_exn gens in
      let init = H.list cost_model inits Sp.Top in
      let memo = Memoizer.create gen cost_model in
      Memoizer.to_flat_sequence memo ~max_cost init
        
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
                let ret_ev = Eval.partial_eval ~ctx:Eval.stdlib_evctx (`Apply (func_ev, args_exprv)) in
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

let generate_for_func : max_cost:int -> file:string -> verbose:bool -> Expr.t -> Type.t -> unit =
  fun ~max_cost ~file ~verbose func type_ ->
    let exs = generate_examples ~max_cost func type_ in
    let exs = if verbose then 
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
  +> anon (maybe ("function" %: string))

let run max_cost m_function () =
  let func_names = match m_function with
    | Some fn -> [fn]
    | None -> Eval.stdlib |> List.unzip |> Tuple.T2.get1
  in
  let excluded = ["map"; "foldl"; "foldr"; "foldt"; "filter"; "inf"; "mapt"; "dedup"] in
  List.iter func_names ~f:(fun name ->
      if not (List.mem excluded name) then
        let m_func =
          List.find_map Eval.stdlib ~f:(fun (name', expr) -> if name = name' then Some expr else None)
        in
        match m_func with
        | Some func ->
          let type_ = Ctx.lookup_exn Infer.stdlib_tctx name in
          let file = name ^ "-examples.sexp" in
          generate_for_func ~max_cost ~file ~verbose:true func type_
        | None -> failwiths "Failed to look up function." name [%sexp_of:string])

let cmd = Command.basic ~summary:"Generate specifications for functions." spec run
    
let () = Command.run cmd
