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
  n "lifting" "Total time spent lifting concrete expressions.";
  n "lowering" "Total time spent lowering abstract expressions.";
  n "eval" "Total time spent evaluating exprs.";
  n "infer" "Time spent inferring new examples.";
  n "total" "Total time spent in this deduction routine.";
  t
let run_with_time = fun name f -> Timer.run_with_time timer name f

let counter =
  let t = Counter.empty () in
  let n = Counter.add_zero t in
  n "eval_calls" "";
  n "eval_failure" "";
  n "eval_success" "";
  n "recursionlimit_failure" "";
  n "conversion_failure" "";
  n "no_match" "No matching example in table.";
  n "have_examples" "Number of hypotheses where we have examples and can deduce.";
  n "no_examples" "Number of hypotheses where we have no examples.";
  n "abstract_specs" "Number of specs pushed to Top for being abstract.";
  t
let cincr = Counter.incr counter 

module Seq = Sequence

module Abstract_int = struct
  type value =
    | Int of int
    | Omega
  [@@deriving compare, sexp]
  
  type domain = { lower: int; upper : int }

  let enumerate : domain -> value Seq.t =
    fun { lower; upper } ->
      Seq.range ~start:`inclusive ~stop:`inclusive lower upper
      |> Seq.map ~f:(fun x -> Int x)
      |> Seq.append (Seq.singleton Omega)

  let lift0 : domain -> int -> value =
    fun { lower; upper } x ->
      if x >= lower && x <= upper then Int x else Omega

  let lift1 : domain -> (int -> int) -> (value -> value) =
    fun d f ->
      function
      | Int x -> lift0 d (f x)
      | Omega -> Omega

  let lift2 : domain -> (int -> int -> int) -> (value -> value -> value) =
    fun d f ->
      function
      | Int x -> lift1 d (f x)
      | Omega -> fun _ -> Omega
end

module Abstract_eq = struct
  type value =
    | List of int list
    | Elem of int
    | Omega
  [@@deriving compare, sexp]
  
  type 'a domain = {
    max_length : int;
    max_distinct : int;
  }

  let enumerate_lists : 'a domain -> value Seq.t =
    fun { max_length } ->
      (* Enumerate all list lengths. *)
      Seq.range ~start:`inclusive ~stop:`inclusive 0 max_length
      (* Enumerate all numbers of distinct elements. *)
      |> Seq.concat_map ~f:(fun len ->
          Seq.zip (Seq.repeat len) (Seq.range ~start:`inclusive ~stop:`inclusive 1 len))
      (* For each length and number of distinct elements, enumerate all sets. *)
      |> Seq.concat_map ~f:(fun (len, num_distinct) ->
          Combinat.m_partition len num_distinct
          |> Seq.map ~f:(fun counts ->
              let elems = Array.create ~len:num_distinct (-1) in
              let fill_pos = ref 0 in
              for i = 0 to num_distinct - 1 do
                Array.fill elems ~pos:!fill_pos ~len:counts.(i) i;
                fill_pos := !fill_pos + counts.(i);
              done;
              elems))
      (* For each set, enumerate all permutations. *)
      |> Seq.concat_map ~f:Combinat.permutations
      |> Seq.map ~f:(fun a -> List (Array.to_list a))

  let enumerate_elems : 'a domain -> value Seq.t =
    fun { max_length } ->
      Seq.range ~start:`inclusive ~stop:`exclusive 0 max_length
      |> Seq.map ~f:(fun x -> Elem x)
end

module Abstract_value = struct
  type t = [
    | `AbsInt of Abstract_int.value
    | `AbsEq of Abstract_eq.value
    | `Bool of bool
    | `List of t list
    | `Tree of t Tree.t
    | `Closure of Expr.t * (t Ctx.t)
    | `Bottom
    | `Top
  ] [@@deriving compare, sexp]

  exception HitRecursionLimit

  let to_string _ = failwith "Implement me!"
  
  let rec of_value : int_domain:Abstract_int.domain -> Value.t -> t =
    fun ~int_domain -> function
      | `Num x -> `AbsInt (Abstract_int.lift0 int_domain x)
      | `Bool x -> `Bool x
      | `List x -> `List (List.map x ~f:(of_value ~int_domain))
      | `Tree x -> `Tree (Tree.map x ~f:(of_value ~int_domain))
      | `Closure (expr, ctx) ->
        `Closure (expr, Ctx.map ctx ~f:(of_value ~int_domain))
      | `Unit -> `Bottom
  
  let eval :
    ?recursion_limit:int
    -> ?ctx:t Ctx.t
    -> int_domain:Abstract_int.domain
    -> Expr.t
    -> t =
    fun ?recursion_limit:(limit = (-1)) ?(ctx = Ctx.empty ()) ~int_domain expr ->
      let rec ev ctx lim expr =
        if lim = 0 then raise HitRecursionLimit
        else match expr with
          | `Num x -> `AbsInt (Abstract_int.lift0 int_domain x)
          | `Bool x -> `Bool x
          | `List x -> `List (List.map x ~f:(ev ctx lim))
          | `Tree x -> `Tree (Tree.map x ~f:(ev ctx lim))
          | `Lambda _ as lambda -> `Closure (lambda, ctx)
          | `Id id -> (match Ctx.lookup ctx id with
              | Some v -> v
              | None -> `Bottom)
          | `Let (name, bound, body) ->
            let ctx' = ref (Ctx.to_string_map ctx) in
            Ctx.update ctx' name (ev ctx' lim bound);
            ev ctx' lim body

          | `Apply (func, raw_args) ->
            let args = List.map ~f:(ev ctx lim) raw_args in
            begin match ev ctx lim func with
              | `Closure (`Lambda (arg_names, body), enclosed_ctx) ->
                begin match List.zip arg_names args with
                  | Some bindings ->
                    let ctx' = List.fold bindings ~init:(enclosed_ctx)
                        ~f:(fun ctx' (arg_name, value) -> Ctx.bind ctx' arg_name value)
                    in
                    ev ctx' (lim - 1) body
                  | None -> `Bottom
                end
              | _ -> `Top
            end

          | `Op (op, raw_args) ->
            let args = lazy (List.map ~f:(ev ctx lim) raw_args) in
            begin
              let open Expr.Op in
              match op with
              | Plus -> (match Lazy.force args with
                  | [`AbsInt x; `AbsInt y] -> `AbsInt (Abstract_int.lift2 int_domain (+) x y)
                  | _ -> `Top)
              | Minus -> (match Lazy.force args with
                  | [`AbsInt x; `AbsInt y] -> `AbsInt (Abstract_int.lift2 int_domain (-) x y)
                  | _ -> `Top)
              | Mul -> (match Lazy.force args with
                  | [`AbsInt x; `AbsInt y] -> `AbsInt (Abstract_int.lift2 int_domain (fun x y -> x * y) x y)
                  | _ -> `Top)
              | Div -> (match Lazy.force args with
                  | [`AbsInt x; `AbsInt y] -> `AbsInt (Abstract_int.lift2 int_domain (/) x y)
                  | _ -> `Top)
              | Mod -> (match Lazy.force args with
                  | [`AbsInt x; `AbsInt y] -> `AbsInt (Abstract_int.lift2 int_domain (%) x y)
                  | _ -> `Top)
              | Eq -> (match Lazy.force args with
                  | [`AbsInt (Int x); `AbsInt (Int y)] -> `Bool (x = y)
                  | [`Bool x; `Bool y] -> `Bool (x = y)
                  | _ -> `Top)
              | Neq -> (match Lazy.force args with
                  | [`AbsInt (Int x); `AbsInt (Int y)] -> `Bool (x <> y)
                  | [`Bool x; `Bool y] -> `Bool (x <> y)
                  | _ -> `Top)
              | Lt -> (match Lazy.force args with
                  | [`AbsInt (Int x); `AbsInt (Int y)] -> `Bool (x < y)
                  | _ -> `Top)
              | Gt -> (match Lazy.force args with
                  | [`AbsInt (Int x); `AbsInt (Int y)] -> `Bool (x > y)
                  | _ -> `Top)
              | Leq -> (match Lazy.force args with
                  | [`AbsInt (Int x); `AbsInt (Int y)] -> `Bool (x <= y)
                  | _ -> `Top)
              | Geq -> (match Lazy.force args with
                  | [`AbsInt (Int x); `AbsInt (Int y)] -> `Bool (x >= y)
                  | _ -> `Top)
              | And -> (match Lazy.force args with
                  | [`Bool x; `Bool y] -> `Bool (x && y)
                  | [`Bool true; x] | [x; `Bool true] -> x
                  | [`Bool false; _] | [_; `Bool false] -> `Bool false
                  | _ -> `Top)
              | Or -> (match Lazy.force args with
                  | [`Bool x; `Bool y] -> `Bool (x || y)
                  | [`Bool false; x] | [x; `Bool false] -> x
                  | [`Bool true; _] | [_; `Bool true] -> `Bool true
                  | _ -> `Top)
              | Not -> (match Lazy.force args with
                  | [`Bool x] -> `Bool (not x)
                  | _ -> `Top)
              | Cons -> (match Lazy.force args with
                  | [`AbsEq (Abstract_eq.Elem x); `AbsEq (Abstract_eq.List xs)] -> `AbsEq (Abstract_eq.List (x::xs))
                  | [x; `List y] -> `List (x :: y)
                  | _ -> `Top)
              | RCons -> (match Lazy.force args with
                  | [`AbsEq (Abstract_eq.Elem x); `AbsEq (Abstract_eq.List xs)] -> `AbsEq (Abstract_eq.List (x::xs))
                  | [x; `List y] -> `List (x :: y)
                  | _ -> `Top)
              | Car -> (match Lazy.force args with
                  | [`AbsEq (Abstract_eq.List (x::_))] -> `AbsEq (Abstract_eq.Elem x)
                  | [`List (x::_)] -> x
                  | _ -> `Top)
              | Cdr -> (match Lazy.force args with
                  | [`AbsEq (Abstract_eq.List (_::xs))] -> `AbsEq (Abstract_eq.List xs)
                  | [`List (_::xs)] -> `List xs
                  | _ -> `Top)
              | If -> (match raw_args with
                  | [ux; uy; uz] -> (match ev ctx lim ux with
                      | `Bool x -> if x then ev ctx lim uy else ev ctx lim uz
                      | _ -> `Top)
                  | _ -> `Bottom)
              | Value -> (match Lazy.force args with
                  | [`Tree Tree.Empty] -> `Bottom
                  | [`Tree (Tree.Node (x, _))] -> x
                  | _ -> `Top)
              | Children -> (match Lazy.force args with
                  | [`Tree Tree.Empty] -> `List []
                  | [`Tree (Tree.Node (_, x))] -> `List (List.map x ~f:(fun e -> `Tree e))
                  | _ -> `Top)
              | Tree -> (match Lazy.force args with
                  | [x; `List y] ->
                    let y' =
                      List.map y ~f:(fun e -> match e with
                          | `Tree t -> t
                          | _ -> Tree.Node (e, []))
                    in
                    `Tree (Tree.Node (x, y'))
                  | _ -> `Top)
            end
      in ev ctx limit expr
end

(* module Abstract_value = struct *)
(*   module T = struct *)
(*     type t = *)
(*       | Top *)
(*       | Value of ExprValue.t *)
(*       | Bottom *)
(*       [@@deriving compare, sexp, variants] *)
(*   end *)
(*   include T *)

(*   let to_string = function *)
(*     | Top -> "⊤" *)
(*     | Bottom -> "⊥" *)
(*     | Value v -> ExprValue.to_string v *)
(* end *)

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
  let lift x y = Timer.run_with_time timer "lifting" (fun () -> lift x y)
  
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
  let lower x y = Timer.run_with_time timer "lowering" (fun () -> lower x y)

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

  module V = struct
    module T = struct
      type t = Expr.t * Value.t String.Map.t [@@deriving sexp,compare]
      let hash = Hashtbl.hash
    end
    include T
    include Hashable.Make(T)
  end
  let eval =
    let table = V.Table.create () in
    Counter.add_func counter "eval_distinct_args" "" (fun () -> Hashtbl.length table);
    fun ctx expr ->
      cincr "eval_calls";
      match Hashtbl.find table (expr, ctx) with
      | Some v -> v
      | None ->
        let vctx = ref ctx in
        let v = Eval.eval ~recursion_limit:100 vctx expr in
        ignore (Hashtbl.add table ~key:(expr, ctx) ~data:v);
        v
  
  let of_spec_and_args : library:Library.t -> args:Sk.t list -> Examples.example -> t =
    let module AV = Abstract_value in
    fun ~library ~args spec ->
      let (ctx, ret) = spec in
      let arity = List.length args in
      let expr_ctx = StaticDistance.Map.map ctx ~f:Expr.of_value in
      let arg_values = try
          List.map args ~f:(fun a ->
              let m_e = Or_error.try_with (fun () -> Sk.to_expr ~ctx:expr_ctx a) in
              match m_e with
              | Ok e -> begin try
                    let v =
                      run_with_time "eval" (fun () -> eval library.Library.value_ctx e)
                      |> ExprValue.of_value
                    in
                    cincr "eval_success";
                    AV.Value v
                  with Eval.HitRecursionLimit ->
                    cincr "recursionlimit_failure"; AV.Top
                end
              | Error _ -> cincr "conversion_failure"; AV.Top)
        with Eval.RuntimeError _ ->
          cincr "eval_failure";
          List.repeat arity AV.Bottom
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
        cincr "no_match";
        let (ins, out) = ex in
        List.repeat (List.length ins) AV.Top, out
end

let infer_examples :
  library:Library.t
  -> specs:Function_spec.t String.Map.t
  -> op:[`Builtin of Expr.Op.t | `Func of string]
  -> args:Sk.t list
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
                  List.filter_map arg_spec ~f:(fun sp -> match Sp.data sp with
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
  -> Sk.t
  -> Sk.t
  = fun ~specs ~library sk ->
    let rec push sk =
      let spec = Sk.spec sk in
      match Sk.ast sk with
      | Sk.Num _
      | Sk.Bool _
      | Sk.Id _
      | Sk.Hole _ -> sk
      | Sk.List l -> Sk.list (List.map l ~f:push) spec
      | Sk.Tree t -> Sk.tree (Tree.map t ~f:push) spec
      | Sk.Let {bound; body} -> Sk.let_ (push bound) (push body) spec
      | Sk.Lambda {num_args; body} -> Sk.lambda num_args (push body) spec
      | Sk.Op {op; args} ->
        begin match Sp.data spec with
          | Examples.Examples exs ->
            cincr "have_examples";
            let arg_specs = run_with_time "infer" (fun () ->
                infer_examples ~library ~specs ~op:(`Builtin op) ~args exs)
            in
            let args = List.map2_exn args arg_specs ~f:Sk.replace_spec in
            Sk.op op (List.map args ~f:push) spec
          | _ ->
            cincr "no_examples";
            Sk.op op (List.map args ~f:push) spec
        end
      | Sk.Apply {func; args} ->
        begin match Sp.data spec, Sk.ast func with
          | Examples.Examples exs, Sk.Id (Sk.Id.Name name) ->
            cincr "have_examples";
            let arg_specs = run_with_time "infer" (fun () ->
                infer_examples ~library ~specs ~op:(`Func name) ~args exs)
            in
            let args = List.map2_exn args arg_specs ~f:Sk.replace_spec in

            (* printf "Runtime %s.\n" (Time.Span.to_string_hum runtime); *)
            (* printf "Pushing specifications for %s.\n" name; *)
            (* print_endline "Args:"; *)
            (* Util.print_sexp args [%sexp_of:Sp.t Sk.t list]; *)
            (* print_endline "Parent spec:"; *)
            (* Util.print_sexp s [%sexp_of:Sp.t]; *)
            (* print_endline "Arg specs:"; *)
            (* Util.print_sexp arg_specs [%sexp_of:Sp.t list]; *)
            (* print_newline (); *)

            Sk.apply func (List.map ~f:push args) spec
          | _ ->
            cincr "no_examples";
            Sk.apply func (List.map ~f:push args) spec
        end
    in
    run_with_time "total" (fun () -> push sk)    

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
