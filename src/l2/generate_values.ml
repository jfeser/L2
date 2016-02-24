open Core.Std

open Collections
open Hypothesis
open Infer
open Synthesis_common

module Sk = Skeleton
module Sp = Specification
module H = Hypothesis

let print_sexp x s = print_endline (Sexp.to_string_hum (s x))

let cost_model =
  let module CM = CostModel in
  {
    CM.num = (fun x -> x);
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
    List.init 50 ~f:(fun x -> H.num cost_model x spec, Unifier.empty)

  let generate_var hole spec =
    List.init 1 ~f:(fun x -> H.id_name cost_model ("v" ^ Int.to_string x) spec, Unifier.empty)

  let generate_list_var hole spec =
    let max_length = 20 in
    let vars =
      List.init max_length ~f:(fun x -> H.id_name cost_model ("v" ^ Int.to_string x) spec)
    in
    List.init max_length ~f:(fun i -> (H.list cost_model (List.take vars i) spec, Unifier.empty))
  
  let generate_list list_sym elem_sym hole spec = [
    (H.op cost_model Expr.Op.Cons [
        H.hole cost_model (Hole.create ~ctx:hole.Hole.ctx (Type.free 0 0) elem_sym) Sp.Top;
        H.hole cost_model (Hole.create ~ctx:hole.Hole.ctx (Type.list (Type.free 0 0)) list_sym) Sp.Top;
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

let generate_examples : max_cost:int -> Expr.t -> Type.t -> (Value.ExprValue.t list * Value.ExprValue.t) Sequence.t =
  let module IT = ImmutableType in
  fun ~max_cost func type_ ->
    let func_ev = Value.ExprValue.of_expr func in
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
      |> Sequence.filter_map ~f:(fun (args, _) -> match H.skeleton args with
          | Sk.List_h (args_sk, _) ->
            let args_exprv =
              List.map args_sk ~f:Sk.to_expr
              |> List.map ~f:Value.ExprValue.of_expr
            in
            begin try
                let ret_ev = Eval.partial_eval ~ctx:Eval.stdlib_evctx (`Apply (func_ev, args_exprv)) in
                Some (args_exprv, ret_ev)
              with Eval.RuntimeError _ -> None
            end
          | sk -> failwiths "Unexpected skeleton." sk [%sexp_of:Sp.t Sk.t])
    | t -> failwiths "Unexpected type." t [%sexp_of:IT.t]

let save_examples : file:string -> (Value.ExprValue.t list * Value.ExprValue.t) list -> unit =
  fun ~file exs ->
    [%sexp_of:(Value.ExprValue.t list * Value.ExprValue.t) list] exs
    |> Sexp.save_mach file 

let load_examples : file:string -> (Value.ExprValue.t list * Value.ExprValue.t) list =
  fun ~file ->
    Sexp.load_sexp file
    |> [%of_sexp:(Value.ExprValue.t list * Value.ExprValue.t) list]

let generate_for_func : max_cost:int -> file:string -> verbose:bool -> Expr.t -> Type.t -> unit =
  fun ~max_cost ~file ~verbose func type_ ->
    let exs = generate_examples ~max_cost func type_ in
    if verbose then begin
      printf "Generating %s\n" file;
      Sequence.iter exs ~f:(fun (ins, out) ->
          printf "(%s) -> %s\n"
            (List.map ins ~f:Value.ExprValue.to_string |> String.concat ~sep:", ")
            (Value.ExprValue.to_string out));
      print_newline ()
    end;
    save_examples ~file (Sequence.to_list exs)

let () =
  let max_cost = Sys.argv.(1) |> Int.of_string in
  let excluded = ["map"; "foldl"; "foldr"; "foldt"; "filter"; "inf"; "mapt"; "dedup"] in
  List.iter Eval.stdlib ~f:(fun (name, func) ->
      if not (List.mem excluded name) then
        let type_ = Ctx.lookup_exn Infer.stdlib_tctx name in
        let file = name ^ "-examples.sexp" in
        generate_for_func ~max_cost ~file ~verbose:true func type_)
