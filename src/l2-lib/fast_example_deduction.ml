open Core.Std
open Core_extended.Std

open Collections
open Hypothesis
open Infer

module Sp = Specification
module Sk = Skeleton

let timer =
  let t = Timer.empty () in
  let n = Timer.add_zero t in
  n "lookup" "Total time spent scanning abstract example lists.";
  n "eval" "Total time spent evaluating exprs.";
  n "total" "Total time spent in this deduction routine.";
  t
let run_with_time = fun name f -> Timer.run_with_time timer name f

let counter =
  let t = Counter.empty () in
  let n = Counter.add_zero t in
  n "abstract_specs" "Number of specs pushed to Top for being abstract.";
  t
let cincr = Counter.incr counter 

module Abstract_value = struct
  module T = struct
    type t = 
      | Top
      | Value of ExprValue.t
      | Bottom
      [@@deriving compare, sexp, variants]
  end
  include T

  let to_string = function
    | Top -> "⊤"
    | Bottom -> "⊥"
    | Value v -> ExprValue.to_string v
end

module Abstract_example = struct
  module T = struct
    type t = Abstract_value.t list * Abstract_value.t [@@deriving compare, sexp]
    let hash = Hashtbl.hash
  end
  include T
  include Hashable.Make(T)

  let to_string (ins, out) =
    let ins_str =
      List.map ins ~f:Abstract_value.to_string
      |> String.concat ~sep:", "
    in
    let out_str = Abstract_value.to_string out in
    "(" ^ ins_str ^ ") -> " ^ out_str

  let lift : Type.t -> t -> (t * string ExprValue.Map.t) =
    let open Abstract_value in
    let open Type in
    fun type_ (ins, out) ->
      let ctx = ref ExprValue.Map.empty in
      let ctr = ref 0 in
      
      let rec normalize_value = function
        | Const_t _ -> Fn.id
        | Var_t _ -> fun v ->
          let id = sprintf "v%d" !ctr in
          ctx := Map.add !ctx ~key:v ~data:id;
          incr ctr;
          `Id id
        | App_t ("list", [val_t]) -> begin function
            | `List l -> `List (List.map ~f:(normalize_value val_t) l)
            | v -> v
          end
        | App_t _ -> Fn.id
        | Arrow_t _ as t -> fun v ->
          failwiths "Higher-order values are not supported."
            (t, v) [%sexp_of:Type.t * ExprValue.t]
      in

      let normalize t = function
        | Top 
        | Bottom as e -> e
        | Value v -> Value (normalize_value t v)
      in
      
      let rec sub_value = fun e ->
        match Map.find !ctx e with
        | Some id -> `Id id
        | None -> begin match e with
            | `Unit
            | `Num _
            | `Bool _ 
            | `Id _ as e -> e
            | `List l -> `List (List.map l ~f:sub_value)
            | _ -> failwith "Unexpected case."
          end
      in

      let sub = function
        | Top | Bottom as e -> e
        | Value v -> Value (sub_value v)
      in

      let ret_type = match type_ with
        | Arrow_t (_, t) -> t
        | t -> t
      in
      let out' = normalize ret_type out in
      let ins' = List.map ins ~f:sub in
      ((ins', out'), !ctx)

  let lower : t -> string ExprValue.Map.t -> t =
    let open Abstract_value in
    fun (ins, out) map ->
      let rec sub_value ctx = function
        | `Unit
        | `Num _
        | `Bool _ as e -> e 
        | `Id id as e -> begin match Map.find ctx id with
            | Some e' -> e'
            | None -> e
          end
        | `List l -> `List (List.map l ~f:(sub_value ctx))
        | _ -> failwith "Unexpected case."
      in

      let sub ctx = function
        | Top | Bottom as e -> e
        | Value v -> Value (sub_value ctx v)
      in

      let inverse_map =
        Map.to_alist map
        |> List.map ~f:Tuple.T2.swap
        |> String.Map.of_alist_exn
      in
      (List.map ins ~f:(sub inverse_map), sub inverse_map out)

  let normalize : t -> t =
    let open Abstract_value in
    fun (ins, out) ->
      let ctx = ref String.Map.empty in
      let ctr = ref 0 in
      
      let rec normalize_value = function
        | `Unit
        | `Num _
        | `Bool _ as e -> e
        | `Id id -> begin
            let id' = sprintf "v%d" !ctr in
            ctx := String.Map.add !ctx ~key:id ~data:id';
            incr ctr;
            `Id id'
          end
        | `List l -> `List (List.map l ~f:normalize_value)
        | _ -> failwith "Unexpected case."
      in
      
      let normalize = function
        | Top 
        | Bottom as e -> e
        | Value v -> Value (normalize_value v)
      in
      
      let rec sub_value = function
        | `Unit
        | `Num _
        | `Bool _ as e -> e
        | `Id id -> begin match String.Map.find !ctx id with
            | Some id' -> `Id id'
            | None -> `Id id
          end
        | `List l -> `List (List.map l ~f:sub_value)
        | v -> failwiths "Unexpected case." v [%sexp_of:ExprValue.t]
      in

      let sub = function
        | Top | Bottom as e -> e
        | Value v -> Value (sub_value v)
      in
                       
      let out' = normalize out in
      let ins' = List.map ins ~f:sub in
      (ins', out')

  let of_example : ExprValue.t list * ExprValue.t -> t =
    let open Abstract_value in
    fun (ins, out) -> (List.map ~f:value ins, value out)

  let join : t -> t -> t =
    fun e1 e2 ->
    let fresh_int = Util.Fresh.mk_fresh_int_fun () in
    let fresh_var = fun () -> `Id (sprintf "T%d" (fresh_int ())) in
    
    let rec join_val = fun v1 v2 -> match v1, v2 with
      | `Unit, `Unit -> `Unit
      | `Num _, `Num _
      | `Bool _, `Bool _
      | `Id _, `Id _ ->
        if v1 = v2 then v1 else fresh_var ()
      | (`Id _ as v), _ | _, (`Id _ as v) -> v
      | `List l1, `List l2 ->
        if List.length l1 = List.length l2 then
          `List (List.map2_exn l1 l2 ~f:join_val)
        else fresh_var ()
      | _ -> failwiths "Unexpected case." (v1, v2) [%sexp_of:ExprValue.t * ExprValue.t]
    in

    let join_av =
      let open Abstract_value in
      fun v1 v2 -> match v1, v2 with
      | Top, _ | _, Top -> Top
      | Bottom, v | v, Bottom -> v
      | Value x1, Value x2 -> Value (join_val x1 x2)
    in

    let (i1, o1) = e1 in
    let (i2, o2) = e2 in
    (List.map2_exn i1 i2 ~f:join_av, join_av o1 o2)
  
  let join_many : t list -> t = List.fold_left1 ~f:join

  let of_spec_and_args : library:Library.t -> args:Sp.t Sk.t list -> Examples.example -> t =
    let module AV = Abstract_value in
    fun ~library ~args spec ->
      let (ctx, ret) = spec in
      let arity = List.length args in
      let expr_ctx = StaticDistance.Map.map ctx ~f:Expr.of_value in
      let arg_values = try
          List.map args ~f:(fun a ->
              let m_e = Or_error.try_with (fun () -> Sk.to_expr ~ctx:expr_ctx a) in
              match m_e with
              | Ok e -> begin
                  try
                    let v =
                      let vctx = ref library.Library.value_ctx in
                      run_with_time "eval" (fun () -> Eval.eval ~recursion_limit:100 vctx e)
                      |> ExprValue.of_value
                    in
                    AV.Value v
                  with Eval.HitRecursionLimit -> AV.Top
                end
              | Error _ -> AV.Top)
        with Eval.RuntimeError _ -> List.repeat arity AV.Bottom
      in
      arg_values, AV.Value (ExprValue.of_value ret)

  let to_arg_specs : Value.t StaticDistance.Map.t -> t -> Sp.t list =
    let module AV = Abstract_value in
    fun ctx (ins, _) ->
      List.map ins ~f:(function
          | AV.Top -> Sp.top
          | AV.Bottom -> Sp.bottom
          | AV.Value ev -> begin match ExprValue.to_value ev with
              | Ok v -> Examples.singleton (ctx, v) |> Examples.to_spec
              | Error _ -> cincr "abstract_specs"; Sp.top
            end)
end

module Function_spec = struct
  type t = Abstract_example.t Abstract_example.Table.t

  let of_examples : (ExprValue.t list * ExprValue.t) list -> t =
    let module Seq = Sequence in
    let module AE = Abstract_example in
    let module AV = Abstract_value in
    fun exs ->
      let exs =
        List.map exs ~f:(fun ex -> AE.of_example ex |> AE.normalize)
      in

      let num_args =
        List.hd_exn exs
        |> Tuple.T2.get1
        |> List.length
      in

      let table = AE.Table.create () in
      
      Seq.cartesian_product (Seq.range 0 num_args) (Seq.of_list exs)
      |> Seq.iter ~f:(fun (n, ex) ->
          let (ins, out) = ex in
          let key = List.take ins n @ List.repeat (num_args - n) AV.Top, out in
          Hashtbl.add_multi table ~key ~data:ex);

      let table = Hashtbl.map table ~f:(fun exs -> AE.join_many (List.dedup exs)) in
      table

  let of_file : string -> t = fun fn ->
    Sexp.load_sexps fn
    |> List.map ~f:[%of_sexp:ExprValue.t list * ExprValue.t]
    |> of_examples

  let find : t -> Abstract_example.t -> Abstract_example.t =
    let module AV = Abstract_value in
    fun t ex ->
      match run_with_time "lookup" (fun () -> Hashtbl.find t ex) with
      | Some ex' -> ex'
      | None ->
        let (ins, out) = ex in
        List.repeat (List.length ins) AV.Top, out
end

let infer_examples :
  library:Library.t
  -> specs:Function_spec.t String.Map.t
  -> op:[`Builtin of Expr.Op.t | `Func of string]
  -> args:Sp.t Sk.t list
  -> Examples.t
  -> Sp.t list =
  fun ~library ~specs ~op ~args exs ->
    let arity = List.length args in
    let op_type = match op with
      | `Builtin op -> Expr.Op.typ op
      | `Func op -> Map.find_exn library.Library.type_ctx op
    in
    let op_str = match op with
      | `Builtin op -> Expr.Op.to_string op
      | `Func op -> op
    in
    match Map.find specs op_str with
    | Some op_specs -> begin
        let exs = Examples.to_list exs in
        let ctxs = List.map exs ~f:Tuple.T2.get1 in
        
        let abstract_exs = List.map exs ~f:(fun ex ->
            let (ax, m) =
              Abstract_example.lift
                op_type
                (Abstract_example.of_spec_and_args ~library ~args ex)
            in
            Abstract_example.lower (Function_spec.find op_specs ax) m)
        in
        let arg_specs = List.map2_exn ctxs abstract_exs ~f:Abstract_example.to_arg_specs in
        let per_arg_specs = List.transpose_exn arg_specs in

        let arg_examples = List.map per_arg_specs ~f:(fun arg_spec ->
              if List.exists arg_spec ~f:(Sp.equal Sp.bottom) then Sp.bottom else
                let arg_exs =
                  List.filter_map arg_spec ~f:(fun sp -> match Sp.spec sp with
                      | Sp.Top -> None
                      | Examples.Examples exs -> Some (Examples.to_list exs)
                      | _ -> failwith "BUG: Unexpected specification.")
                  |> List.concat
                in
                match arg_exs with
                | [] -> Sp.top
                | _ -> begin match Examples.of_list arg_exs with
                    | Ok sp -> Examples.to_spec sp
                    | Error _ -> Sp.bottom
                  end)
        in
        arg_examples
      end
    | None -> List.repeat arity Sp.top

let push_specs_exn' :
  specs:Function_spec.t String.Map.t
  -> library:Library.t
  -> Sp.t Sk.t
  -> Sp.t Sk.t
  = fun ~specs ~library sk ->
    let rec push_specs_exn sk = 
      match sk with
      | Sk.Num_h (_, s)
      | Sk.Bool_h (_, s)
      | Sk.Id_h (_, s)
      | Sk.Hole_h (_, s) as sk -> sk
      | Sk.List_h (l, s) -> Sk.List_h (List.map l ~f:push_specs_exn, s)
      | Sk.Tree_h (t, s) -> Sk.Tree_h (Tree.map t ~f:push_specs_exn, s)
      | Sk.Let_h ((bound, body), s) -> Sk.Let_h ((push_specs_exn bound, push_specs_exn body), s)
      | Sk.Lambda_h ((num_args, body), s) -> Sk.Lambda_h ((num_args, push_specs_exn body), s)
      | Sk.Op_h ((op, args), s) ->
        begin match Sp.spec s with
          | Examples.Examples exs ->
            let (arg_specs, runtime) = Util.with_runtime (fun () ->
                infer_examples ~library ~specs ~op:(`Builtin op) ~args exs)
            in
            let args = List.map2_exn args arg_specs ~f:(fun arg sp ->
                Sk.map_annotation arg ~f:(fun _ -> sp))
            in
            Sk.Op_h ((op, List.map args ~f:push_specs_exn), s)
          | _ -> Sk.Op_h ((op, List.map args ~f:push_specs_exn), s)
        end
      | Sk.Apply_h ((func, args), s) ->
        begin match Sp.spec s, func with
          | Examples.Examples exs, Sk.Id_h (Sk.Id.Name name, _) ->
            let (arg_specs, runtime) = Util.with_runtime (fun () ->
                infer_examples ~library ~specs ~op:(`Func name) ~args exs)
            in
            let args = List.map2_exn args arg_specs ~f:(fun arg sp ->
                Sk.map_annotation arg ~f:(fun _ -> sp))
            in

            (* printf "Runtime %s.\n" (Time.Span.to_string_hum runtime); *)
            (* printf "Pushing specifications for %s.\n" name; *)
            (* print_endline "Args:"; *)
            (* Util.print_sexp args [%sexp_of:Sp.t Sk.t list]; *)
            (* print_endline "Parent spec:"; *)
            (* Util.print_sexp s [%sexp_of:Sp.t]; *)
            (* print_endline "Arg specs:"; *)
            (* Util.print_sexp arg_specs [%sexp_of:Sp.t list]; *)
            (* print_newline (); *)

            Sk.Apply_h ((func, List.map ~f:push_specs_exn args), s)
          | _ -> Sk.Apply_h ((push_specs_exn func, List.map ~f:push_specs_exn args), s)
        end
    in
    run_with_time "total" (fun () -> push_specs_exn sk)    

let create spec_dir library =
  let specs =
    if Sys.is_directory spec_dir = `Yes then
      let spec_files =
        Sys.ls_dir spec_dir
        |> List.map ~f:(fun f -> spec_dir ^ "/" ^ f)
      in
      List.map spec_files ~f:(fun sf ->
          let exs = Example_deduction.examples_of_file sf in
          let name = Filename.chop_suffix (Filename.basename sf) "-examples.sexp" in
          (name, Function_spec.of_examples exs))
      |> String.Map.of_alist_exn
    else
      failwith "Could not load component specifications."
  in

  fun sk -> Some (push_specs_exn' ~specs ~library sk)
