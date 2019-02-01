open Core
open Collections
open Hypothesis

(* module UnificationContext = struct *)
(* end *)

(* type unify_error = [ *)
(*   | `FailedOccursCheck *)
(*   | `NonUnifiable *)
(* ] *)

(* exception UnifyError of unify_error *)

(* type term = *)
(*   | Variable of int *)
(*   | Constant of int *)
(*   | Apply of int * term list *)

(* let rec occurs var t = match t with *)
(*   | Variable x -> var = x *)
(*   | Apply (f, a) -> List.exists a ~f:(occurs var) *)
(*   | Constant _ -> false *)

(* let rec apply sub t = match t with *)
(*   | Variable x -> Option.value (Int.Map.find sub x) ~default:t *)
(*   | Apply (f, a) -> Apply (f, List.map a ~f:(apply sub)) *)
(*   | Constant _ -> t *)

(* let rec unify t1 t2 = *)
(*   match t1, t2 with *)
(*   | Variable x, Variable y -> if x = y then Int.Map.empty else Int.Map.singleton x t2 *)
(*   | Constant x, Constant y -> if x = y then Int.Map.empty else raise (UnifyError `NonUnifiable) *)
(*   | Apply (f1, a1), Apply (f2, a2) -> *)
(*     if f1 = f2 then match List.zip a1 a2 with *)
(*       | Some a -> List.fold_left a ~init:Int.Map.empty ~f:(fun sub (a1, a2) -> *)
(*           let sub' = unify a1 a2 in *)
(*           Int.Map.merge sub sub' ~f:(function *)
(*               | `Both (x1, x2) -> )) *)
(*       | None -> raise (UnifyError `NonUnifiable) *)
(*     else raise (UnifyError `NonUnifiable) *)

(* type variable = *)
(*   | Free of int *)
(*   | Input of int *)
(*   | Output *)

(* type constant = *)
(*   | Bool of bool *)
(*   | Int of int *)
(*   | Nil *)
(*   | Bottom *)

(* type term = *)
(*   | Constant of constant *)
(*   | Variable of variable *)
(*   | Apply of string * term list *)

(* type binary_operator = *)
(*   | Eq *)

(* type predicate = *)
(*   | Binary of binary_operator * term * term *)

(* type specification = (predicate list) list *)

(* module Context = struct *)
(*   include Map.Make(struct type t = variable with sexp, compare end) *)

(*   let of_args args = *)
(*     List.foldi args ~f:(fun i ctx a -> add ctx ~key:(Input i) ~data:a) ~init:empty *)

(*   let rec apply ctx t = match t with *)
(*     | Constant _ | Variable (Input _) -> t *)
(*     | Variable (Free _ as v) | Variable (Output as v) -> begin *)
(*         match find ctx v with *)
(*         | Some t' -> t' *)
(*         | None -> t *)
(*       end *)
(*     | Apply (f, args) -> Apply (f, List.map args ~f:(apply ctx)) *)

(*   let compose s1 s2 = *)
(*     let merge outer inner = *)
(*       fold ~f:(fun ~key:name ~data:typ m -> add ~key:name ~data:typ m) ~init:outer inner *)
(*     in *)
(*     merge s1 (map ~f:(fun t -> apply s1 t) s2) *)
(* end *)

(* module Component = struct *)
(*   type t = { *)
(*     specification : specification; *)
(*   } *)
(* end *)

(* let (plus: specification) = [ *)
(*   [ Binary (Eq, Variable (Input 0), Constant (Int 0)); *)
(*     Binary (Eq, Variable Output, Variable (Input 1)); ]; *)
(*   [ Binary (Eq, Variable (Input 1), Constant (Int 0)); *)
(*     Binary (Eq, Variable Output, Variable (Input 0)); ]; *)
(*   [ Binary (Eq, Variable (Input 0), Apply ("minus", [ Variable (Free 0); Variable (Free 1) ])); *)
(*     Binary (Eq, Variable (Input 1), Variable (Free 1)); *)
(*     Binary (Eq, Variable Output, Variable (Free 0)); ]; *)
(*   [ Binary (Eq, Variable (Input 1), Apply ("minus", [ Variable (Free 0); Variable (Free 1) ])); *)
(*     Binary (Eq, Variable (Input 0), Variable (Free 1)); *)
(*     Binary (Eq, Variable Output, Variable (Free 0)); ]; *)
(* ] *)

(* | [x; `Num 0] -> x *)
(* | [`Op (Plus, [x; y]); z] when x = z -> y *)
(* | [`Op (Plus, [x; y]); z] when y = z -> x *)
(* | [z; `Op (Plus, [x; y])] when x = z -> `Op (Minus, [`Num 0; y]) *)
(* | [z; `Op (Plus, [x; y])] when y = z -> `Op (Minus, [`Num 0; x]) *)
(* | [x; y] when x = y -> `Num 0 *)

(* "(i1 = 0 ^ o = i0) v (i0 = plus(x, y) ^ i1 = x ^ o = y) v (i0 = plus(x, y) ^ i1 = y ^ o = x)" *)
(* "minus(x, 0) = x" *)
(* "minus(plus(x, y), x) = y" *)

(* let minus = [ *)
(*   [ Binary (Eq, Variable (Input 1), Constant (Int 0)); Binary (Eq, Variable Output, Variable (Input 0)) ]; *)
(*   [ Binary (Eq, Variable (Free 0), Constant (Int 0)); Binary (Eq, Variable Output, Variable (Free 0)) ]; *)
(* ] *)

(* let rec occurs var term = match term with *)
(*   | Constant _ | Variable (Input _) -> raise (UnifyError `FailedOccursCheck) *)
(*   | Variable var' -> if var' = var then raise (UnifyError `FailedOccursCheck) *)
(*   | Apply (_, terms) -> List.iter terms ~f:(occurs var) *)

(* let rec unify_exn ctx t1 t2 = match t1, t2 with *)
(*   | Constant _, Constant _ -> if t1 = t2 then ctx else raise (UnifyError `Nonunifiable) *)
(*   | (Variable (Input _ as v)), t | t, (Variable (Input _ as v)) -> begin *)
(*       match Context.find ctx v with *)
(*       | Some t' -> unify_exn ctx t t' *)
(*       | None -> raise (UnifyError `UnboundVariable) *)
(*     end *)
(*   | (Variable (Output as v)), t | t, (Variable (Output as v)) *)
(*   | (Variable (Free _ as v)), t | t, (Variable (Free _ as v)) -> *)
(*     occurs v t; Context.add ctx ~key:Output ~data:t *)
(*   | Apply (f1, args1), Apply (f2, args2) -> *)
(*     if f1 <> f2 then raise (UnifyError `Nonunifiable) else begin *)
(*       match List.zip args1 args2 with *)
(*       | Some args -> List.fold args ~f:(fun ctx (t1, t2) -> Context.compose ctx (unify_exn ctx t1 t2)) ~init:ctx *)
(*       | None -> raise (UnifyError `Nonunifiable) *)
(*     end *)
(*   | Apply _, Constant _ | Constant _, Apply _ -> *)
(*     raise (UnifyError `Nonunifiable) *)

(* let output_of relation args = *)
(*   let ctx = Context.of_args args in *)
(*   let m_ctx = List.find_map relation ~f:(List.fold_left ~f:(fun m_ctx pr -> *)
(*       Option.bind m_ctx (fun ctx -> match pr with *)
(*       | Binary (Eq, t1, t2) -> try Some (unify_exn ctx t1 t2) with *)
(*         | UnifyError _ -> None)) *)
(*       ~init:(Some ctx)) *)
(*   in *)
(*   Option.bind m_ctx (fun ctx -> Context.find ctx Output) *)

type error =
  [ `HitRecursionLimit
  | `DivideByZero
  | `BadFunctionArguments
  | `WrongNumberOfArguments
  | `CarOfEmptyList
  | `CdrOfEmptyList
  | `ValueOfEmptyTree
  | `UnhandledConditional ]

exception EvalError of error

type result =
  | Num_r of int
  | Bool_r of bool
  | List_r of result list
  | Tree_r of result Tree.t
  | Id_r of Skeleton.Id.t
  | Apply_r of result * result list
  | Op_r of Expr.Op.t * result list
  | Symbol_r of int
  | Closure_r of Skeleton.t * result StaticDistance.Map.t ref
[@@deriving compare, sexp]

let rec result_of_value = function
  | `Bool x -> Bool_r x
  | `Closure (body, ctx) -> failwith "Cannot convert closures."
  | `Tree x -> Tree_r (Tree.map x ~f:result_of_value)
  | `List x -> List_r (List.map x ~f:result_of_value)
  | `Unit -> failwith "Cannot convert unit."
  | `Num x -> Num_r x

exception ConversionError

let skeleton_of_result r =
  let module S = Skeleton in
  let hole = Hole.create Infer.Type.num (Symbol.create "TEST") in
  let rec skeleton_of_result r =
    match r with
    | Num_r x -> num (x, ())
    | Bool_r x -> S.Bool_h (x, ())
    | List_r x -> S.List_h (List.map x ~f:skeleton_of_result, ())
    | Tree_r x -> S.Tree_h (Tree.map x ~f:skeleton_of_result, ())
    | Id_r x -> S.Id_h (x, ())
    | Apply_r (func, args) ->
        S.Apply_h
          ((skeleton_of_result func, List.map args ~f:skeleton_of_result), ())
    | Op_r (op, args) -> S.Op_h ((op, List.map args ~f:skeleton_of_result), ())
    | Symbol_r _ -> S.Hole_h (hole, ())
    | Closure_r (_, _) -> raise ConversionError
  in
  try Some (skeleton_of_result r) with ConversionError -> None

module PathContext = struct
  module PathConditionMap = Map.Make (struct
    type t = result list [@@deriving compare, sexp]
  end)

  type t = result StaticDistance.Map.t PathConditionMap.t

  let find map pc id =
    Option.bind (PathConditionMap.find map pc) (fun ctx ->
        StaticDistance.Map.find ctx id )

  let add map pc id data =
    PathConditionMap.change map pc (fun m_ctx ->
        match m_ctx with
        | Some ctx -> Some (StaticDistance.Map.add ctx ~key:id ~data)
        | None -> Some (StaticDistance.Map.singleton id data) )

  let empty = PathConditionMap.empty
end

(* let evaluate ?recursion_limit ?(ctx = StaticDistance.Map.empty) skeleton = *)
(*   let stdlib = String.Map.empty in (\* TODO: fill in stdlib *\) *)
(*   let open Result.Monad_infix in *)
(*   let rec eval limit ctx path_condition res = *)
(*     if limit = 0 then raise (EvalError `HitRecursionLimit) else *)
(*       let limit = limit - 1 in *)
(*       let eval_all = List.map ~f:(eval limit ctx) in *)
(*       let module S = Skeleton in *)
(*       let module O = Ast in *)
(*       match res with *)
(*       | S.Num_h (x, _) -> [Num_r x, path_condition] *)
(*       | S.Bool_h (x, _) -> [Bool_r x, path_condition] *)
(*       | S.Hole_h (x, _) -> [Symbol_r x.Hole.id, path_condition] *)
(*       | S.List_h (l, _) -> *)
(*         List.fold_left l ~init:[[], []] ~f:(fun all_paths elem -> *)
(*             List.concat_map all_paths ~f:(fun (list, list_path) -> *)
(*                 let elem_paths = eval limit ctx list_path elem in *)
(*                 List.map elem_paths ~f:(fun (elem, elem_path) -> *)
(*                     elem::list, elem_path @ list_path))) *)
(*         |> List.map ~f:(fun (r, p) -> List_r r, p) *)
(*       | S.Tree_h (x, _) -> Tree_r (Tree.map x ~f:(eval limit ctx)) *)
(*       | S.Lambda_h _ -> [Closure_r (res, ctx), path_condition] *)
(*       | S.Id_h (S.StaticDistance sd as id, _) -> *)
(*         [Option.value (PathContext.find !ctx path_condition sd) ~default:(Id_r id), path_condition] *)
(*       | S.Id_h (S.Name name as id, _) -> *)
(*         [Option.value (String.Map.find stdlib name) ~default:(Id_r id), path_condition] *)
(*       | S.Let_h ((bound, body), _) -> *)
(*         let ctx = ref (StaticDistance.map_increment_scope !ctx) in *)
(*         let bound_paths = eval limit ctx bound in *)

(*         ctx := StaticDistance.Map.add !ctx *)
(*             ~key:(StaticDistance.create ~index:1 ~distance:1) *)
(*             ~data:(eval limit ctx bound); *)
(*         eval limit ctx body *)
(*       | S.Apply_h ((func, args), _) -> *)
(*         let args = eval_all args in *)
(*         begin match eval limit ctx func with *)
(*           | Closure_r (S.Lambda_h ((num_args, body), _), ctx) -> begin *)
(*               match List.zip (StaticDistance.args num_args) args with *)
(*               | Some bindings -> *)
(*                 let ctx = ref (List.fold bindings ~init:!ctx ~f:(fun ctx (name, value) -> *)
(*                     StaticDistance.Map.add ctx ~key:name ~data:value)) *)
(*                 in *)
(*                 eval limit ctx body *)
(*               | None -> raise (EvalError `WrongNumberOfArguments) *)
(*             end *)
(*           | r -> Apply_r (r, args) *)
(*         end *)
(*       | S.Op_h ((O.If, args), _) -> begin *)
(*           match args with *)
(*           | [cond; body1; body2] -> (match eval limit ctx cond with *)
(*               | Bool_r true -> eval limit ctx body1 *)
(*               | Bool_r false -> eval limit ctx body2 *)
(*               | cond -> *)
(*                 let paths1 = eval limit ctx body1 in *)
(*                 let paths2 = eval limit ctx body2 in *)
(*                 paths1 @ paths2) *)
(*           | _ -> expr *)
(*         end *)

(*       | S.Op_h ((op, args), _) -> *)
(*         let args = eval_all args in *)
(*         try *)
(*           match op with *)
(*           | O.If -> failwith "Handled in earlier case." *)
(*           | O.Plus -> (match args with *)
(*               | [Num_r x; Num_r y] -> Num_r (x + y) *)
(*               | [Num_r 0; x] | [x; Num_r 0] -> x *)
(*               | [Op_r (O.Minus, [x; y]); z] *)
(*               | [z; Op_r (O.Minus, [x; y])] when y = z -> x *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Minus -> (match args with *)
(*               | [Num_r x; Num_r y] -> Num_r (x - y) *)
(*               | [x; Num_r 0] -> x *)
(*               | [Op_r (O.Plus, [x; y]); z] when x = z -> y *)
(*               | [Op_r (O.Plus, [x; y]); z] when y = z -> x *)
(*               | [z; Op_r (O.Plus, [x; y])] when x = z -> Op_r (O.Minus, [Num_r 0; y]) *)
(*               | [z; Op_r (O.Plus, [x; y])] when y = z -> Op_r (O.Minus, [Num_r 0; x]) *)
(*               | [x; y] when x = y -> Num_r 0 *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Mul -> (match args with *)
(*               | [Num_r x; Num_r y] -> Num_r (x * y) *)
(*               | [Num_r 0; _] | [_; Num_r 0] -> Num_r 0 *)
(*               | [Num_r 1; x] | [x; Num_r 1] -> x *)
(*               | [x; Op_r (O.Div, [y; z])] *)
(*               | [Op_r (O.Div, [y; z]); x] when x = z -> y *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Div -> (match args with *)
(*               | [_; Num_r 0] -> raise (EvalError `DivideByZero) *)
(*               | [Num_r x; Num_r y] -> Num_r (x / y) *)
(*               | [Num_r 0; _] -> Num_r 0 *)
(*               | [x; Num_r 1] -> x *)
(*               | [x; y] when x = y -> Num_r 1 *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Mod -> (match args with *)
(*               | [_; Num_r 0] -> raise (EvalError `DivideByZero) *)
(*               | [Num_r x; Num_r y] -> Num_r (x mod y) *)
(*               | [Num_r 0; _] | [_; Num_r 1] -> Num_r 0 *)
(*               | [x; y] when x = y -> Num_r 0 *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Eq -> (match args with *)
(*               | [Bool_r true; x] | [x; Bool_r true] -> x *)
(*               | [Bool_r false; x] | [x; Bool_r false] -> Op_r (O.Not, [x]) *)
(*               | [x; Op_r (O.Cdr, [y])] | [Op_r (O.Cdr, [y]); x] when x = y -> Bool_r false *)
(*               | [x; y] -> Bool_r (x = y) *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Neq -> (match args with *)
(*               | [Bool_r true; x] | [x; Bool_r true] -> Op_r (O.Not, [x]) *)
(*               | [Bool_r false; x] | [x; Bool_r false] -> x *)
(*               | [x; Op_r (O.Cdr, [y])] | [Op_r (O.Cdr, [y]); x] when x = y -> Bool_r true *)
(*               | [x; y] -> Bool_r (x <> y) *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Lt -> (match args with *)
(*               | [Num_r x; Num_r y] -> Bool_r (x < y) *)
(*               | [x; y] when x = y -> Bool_r false *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Gt -> (match args with *)
(*               | [Num_r x; Num_r y] -> Bool_r (x > y) *)
(*               | [x; y] when x = y -> Bool_r false *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Leq -> (match args with *)
(*               | [Num_r x; Num_r y] -> Bool_r (x <= y) *)
(*               | [x; y] when x = y -> Bool_r true *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Geq -> (match args with *)
(*               | [Num_r x; Num_r y] -> Bool_r (x >= y) *)
(*               | [x; y] when x = y -> Bool_r true *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.And -> (match args with *)
(*               | [Bool_r x; Bool_r y] -> Bool_r (x && y) *)
(*               | [Bool_r true; x] | [x; Bool_r true] -> x *)
(*               | [Bool_r false; _] | [_; Bool_r false] -> Bool_r false *)
(*               | [x; Op_r (O.And, [y; z])] when x = y -> Op_r (O.And, [x; z]) *)
(*               | [x; Op_r (O.And, [y; z])] when x = z -> Op_r (O.And, [x; y]) *)
(*               | [x; Op_r (O.Not, [y])] *)
(*               | [Op_r (O.Not, [y]); x] when x = y -> Bool_r false *)
(*               (\* DeMorgan's law. *\) *)
(*               | [Op_r (O.Not, [x]); Op_r (O.Not, [y])] -> Op_r (O.Not, [Op_r (O.Or, [x; y])]) *)
(*               (\* Distributivity. *\) *)
(*               | [Op_r (O.Or, [a; b]); Op_r (O.Or, [c; d])] when a = c -> *)
(*                 Op_r (O.Or, [a; Op_r (O.And, [b; d])]) *)
(*               | [x; y] when x = y -> x *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Or -> (match args with *)
(*               | [Bool_r x; Bool_r y] -> Bool_r (x || y) *)
(*               | [Bool_r false; x] | [x; Bool_r false] -> x *)
(*               | [Bool_r true; _] | [_; Bool_r true] -> Bool_r true *)
(*               | [x; Op_r (O.Or, [y; z])] when x = y -> Op_r (O.Or, [x; z]) *)
(*               | [x; Op_r (O.Or, [y; z])] when x = z -> Op_r (O.Or, [x; y]) *)
(*               | [x; Op_r (O.Not, [y])] *)
(*               | [Op_r (O.Not, [y]); x] when x = y -> Bool_r true *)
(*               (\* DeMorgan's law. *\) *)
(*               | [Op_r (O.Not, [x]); Op_r (O.Not, [y])] -> *)
(*                 Op_r (O.Not, [Op_r (O.And, [x; y])]) *)
(*               (\* Distributivity. *\) *)
(*               | [Op_r (O.And, [a; b]); Op_r (O.And, [c; d])] when a = c -> *)
(*                 Op_r (O.And, [a; Op_r (O.Or, [b; d])]) *)
(*               | [x; y] when x = y -> x *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Not -> (match args with *)
(*               | [Bool_r x] -> Bool_r (not x) *)
(*               | [Op_r (O.Not, [x])] -> x *)
(*               | [Op_r (O.Lt, [x; y])] -> Op_r (O.Geq, [x; y]) *)
(*               | [Op_r (O.Gt, [x; y])] -> Op_r (O.Leq, [x; y]) *)
(*               | [Op_r (O.Leq, [x; y])] -> Op_r (O.Gt, [x; y]) *)
(*               | [Op_r (O.Geq, [x; y])] -> Op_r (O.Lt, [x; y]) *)
(*               | [Op_r (O.Eq, [x; y])] -> Op_r (O.Neq, [x; y]) *)
(*               | [Op_r (O.Neq, [x; y])] -> Op_r (O.Eq, [x; y]) *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Cons -> (match args with *)
(*               | [x; List_r y] -> List_r (x :: y) *)
(*               | [Op_r (O.Car, [x]); Op_r (O.Cdr, [y])] when x = y -> x *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.RCons -> (match args with *)
(*               | [List_r y; x] -> List_r (x :: y) *)
(*               | [Op_r (O.Cdr, [y]); Op_r (O.Car, [x])] when x = y -> x *)
(*               | _ -> Op_r (O.RCons, args)) *)
(*           | O.Car -> (match args with *)
(*               | [List_r (x::_)] -> x *)
(*               | [List_r []] -> raise (EvalError `CarOfEmptyList) *)
(*               | [Op_r (O.Cons, [x; _])] -> x *)
(*               | [Op_r (O.RCons, [_; x])] -> x *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Cdr -> (match args with *)
(*               | [List_r (_::xs)] -> List_r xs *)
(*               | [List_r []] -> raise (EvalError `CdrOfEmptyList) *)
(*               | [Op_r (O.Cons, [_; x])] *)
(*               | [Op_r (O.RCons, [x; _])] -> x *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Value -> (match args with *)
(*               | [Tree_r Tree.Empty] -> raise (EvalError `ValueOfEmptyTree) *)
(*               | [Tree_r (Tree.Node (x, _))] -> x *)
(*               | [Op_r (O.Tree, [x; _])] -> x *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Children -> (match args with *)
(*               | [Tree_r Tree.Empty] -> List_r [] *)
(*               | [Tree_r (Tree.Node (_, x))] -> List_r (List.map x ~f:(fun e -> Tree_r e)) *)
(*               | [Op_r (O.Tree, [_; x])] -> x *)
(*               | _ -> Op_r (op, args)) *)
(*           | O.Tree -> (match args with *)
(*               | [x; List_r y] -> *)
(*                 let y' = List.map y ~f:(fun e -> match e with *)
(*                     | Tree_r t -> t *)
(*                     | _ -> Tree.Node (e, [])) *)
(*                 in *)
(*                 Tree_r (Tree.Node (x, y')) *)
(*               | _ -> Op_r (op, args)) *)

(*         (\* Invalid_argument is thrown when comparing functional values (closures). *\) *)
(*         with Invalid_argument _ -> Op_r (op, args) *)
(*   in *)
(*   eval (Option.value recursion_limit ~default:(-1)) (ref ctx) skeleton *)

let partially_evaluate ?recursion_limit ?(ctx = StaticDistance.Map.empty) skeleton =
  let stdlib = String.Map.empty in
  (* TODO: fill in stdlib *)
  let open Result.Monad_infix in
  let rec eval limit ctx res =
    if limit = 0 then raise (EvalError `HitRecursionLimit)
    else
      let limit = limit - 1 in
      let eval_all = List.map ~f:(eval limit ctx) in
      let module S = Skeleton in
      let module O = Ast in
      match res with
      | S.Num_h (x, _) -> Num_r x
      | S.Bool_h (x, _) -> Bool_r x
      | S.Hole_h (x, _) -> Symbol_r x.Hole.id
      | S.List_h (l, _) -> List_r (eval_all l)
      | S.Tree_h (x, _) -> Tree_r (Tree.map x ~f:(eval limit ctx))
      | S.Lambda_h _ -> Closure_r (res, ctx)
      | S.Id_h ((S.Id.StaticDistance sd as id), _) ->
          Option.value (StaticDistance.Map.find !ctx sd) ~default:(Id_r id)
      | S.Id_h ((S.Id.Name name as id), _) ->
          Option.value (String.Map.find stdlib name) ~default:(Id_r id)
      | S.Let_h ((bound, body), _) ->
          let ctx = ref (StaticDistance.map_increment_scope !ctx) in
          ctx :=
            StaticDistance.Map.add !ctx
              ~key:(StaticDistance.create ~index:1 ~distance:1)
              ~data:(eval limit ctx bound) ;
          eval limit ctx body
      | S.Apply_h ((func, args), _) -> (
          let args = eval_all args in
          let func = eval limit ctx func in
          try
            match func with
            (* | Closure_r (S.Lambda_h ((num_args, body), _), ctx) -> begin *)
            (*     match List.zip (StaticDistance.args num_args) args with *)
            (*     | Some bindings -> *)
            (*       let ctx = ref (List.fold bindings ~init:!ctx ~f:(fun ctx (name, value) -> *)
            (*           StaticDistance.Map.add ctx ~key:name ~data:value)) *)
            (*       in *)
            (*       eval limit ctx body *)
            (*     | None -> raise (EvalError `WrongNumberOfArguments) *)
            (*   end *)
            | Id_r (S.Id.Name "intersperse") as f -> (
              match args with
              | [List_r []; _] -> List_r []
              | [List_r [x]; _] -> List_r [x]
              | [List_r [x; y]; a] -> List_r [x; a; y]
              | [List_r [x; y; z]; a] -> List_r [x; a; y; a; z]
              | [List_r [x; y; z; w]; a] -> List_r [x; a; y; a; z; a; w]
              | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "sort") as f -> (
              match args with
              | [List_r []] -> List_r []
              | [List_r [x]] -> List_r [x]
              | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "reverse") as f -> (
              match args with
              | [List_r []] -> List_r []
              | [List_r [x]] -> List_r [x]
              | [List_r [x; y]] -> List_r [y; x]
              | [List_r [x; y; z]] -> List_r [z; y; x]
              | [List_r [x; y; z; w]] -> List_r [w; z; y; x]
              | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "append") as f -> (
              match args with
              | [List_r []; x] | [x; List_r []] -> x
              | [List_r [x]; y] -> Op_r (O.Cons, [x; y])
              | [List_r [x; y]; z] -> Op_r (O.Cons, [x; Op_r (O.Cons, [y; z])])
              | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "merge") as f -> (
              match args with
              | [List_r []; x] | [x; List_r []] -> x
              | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "dedup") as f -> (
              match args with
              | [List_r []] -> List_r []
              | [List_r [x]] -> List_r [x]
              | [List_r [x; y]] -> if x = y then List_r [x] else List_r [x; y]
              | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "zip") as f -> (
              match args with
              | [_; List_r []] | [List_r []; _] -> List_r []
              | [List_r [x]; List_r [y]] -> List_r [List_r [x; y]]
              | [List_r [x; y]; List_r [z]] -> List_r [List_r [x; z]]
              | [List_r [x; y; _]; List_r [z]] -> List_r [List_r [x; z]]
              | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "take") as f -> (
              match args with [List_r []; _] -> List_r [] | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "drop") as f -> (
              match args with [List_r []; _] -> List_r [] | _ -> Apply_r (f, args) )
            | Id_r (S.Id.Name "concat") as f -> (
              match args with [List_r []] -> List_r [] | _ -> Apply_r (f, args) )
            | r -> Apply_r (r, args)
          with Invalid_argument _ -> Apply_r (func, args) )
      | S.Op_h ((O.If, args), _) -> (
        match args with
        | [cond; body1; body2] -> (
          match eval limit ctx cond with
          | Bool_r true -> eval limit ctx body1
          | Bool_r false -> eval limit ctx body2
          | cond -> raise (EvalError `UnhandledConditional) )
        | _ -> raise (EvalError `WrongNumberOfArguments) )
      | S.Op_h ((op, args), _) -> (
          let args = eval_all args in
          try
            match op with
            | O.If -> failwith "Handled in earlier case."
            | O.Plus -> (
              match args with
              | [Num_r x; Num_r y] -> Num_r (x + y)
              | [Num_r 0; x] | [x; Num_r 0] -> x
              | ([Op_r (O.Minus, [x; y]); z] | [z; Op_r (O.Minus, [x; y])])
                when y = z ->
                  x
              | _ -> Op_r (op, args) )
            | O.Minus -> (
              match args with
              | [Num_r x; Num_r y] -> Num_r (x - y)
              | [x; Num_r 0] -> x
              | [Op_r (O.Plus, [x; y]); z] when x = z -> y
              | [Op_r (O.Plus, [x; y]); z] when y = z -> x
              | [z; Op_r (O.Plus, [x; y])] when x = z -> Op_r (O.Minus, [Num_r 0; y])
              | [z; Op_r (O.Plus, [x; y])] when y = z -> Op_r (O.Minus, [Num_r 0; x])
              | [x; y] when x = y -> Num_r 0
              | _ -> Op_r (op, args) )
            | O.Mul -> (
              match args with
              | [Num_r x; Num_r y] -> Num_r (x * y)
              | [Num_r 0; _] | [_; Num_r 0] -> Num_r 0
              | [Num_r 1; x] | [x; Num_r 1] -> x
              | ([x; Op_r (O.Div, [y; z])] | [Op_r (O.Div, [y; z]); x]) when x = z
                ->
                  y
              | _ -> Op_r (op, args) )
            | O.Div -> (
              match args with
              | [_; Num_r 0] -> raise (EvalError `DivideByZero)
              | [Num_r x; Num_r y] -> Num_r (x / y)
              | [Num_r 0; _] -> Num_r 0
              | [x; Num_r 1] -> x
              | [x; y] when x = y -> Num_r 1
              | _ -> Op_r (op, args) )
            | O.Mod -> (
              match args with
              | [_; Num_r 0] -> raise (EvalError `DivideByZero)
              | [Num_r x; Num_r y] -> Num_r (x mod y)
              | [Num_r 0; _] | [_; Num_r 1] -> Num_r 0
              | [x; y] when x = y -> Num_r 0
              | _ -> Op_r (op, args) )
            | O.Eq -> (
              match args with
              | [Bool_r true; x] | [x; Bool_r true] -> x
              | [Bool_r false; x] | [x; Bool_r false] -> Op_r (O.Not, [x])
              | ([x; Op_r (O.Cdr, [y])] | [Op_r (O.Cdr, [y]); x]) when x = y ->
                  Bool_r false
              | [x; y] -> Bool_r (x = y)
              | _ -> Op_r (op, args) )
            | O.Neq -> (
              match args with
              | [Bool_r true; x] | [x; Bool_r true] -> Op_r (O.Not, [x])
              | [Bool_r false; x] | [x; Bool_r false] -> x
              | ([x; Op_r (O.Cdr, [y])] | [Op_r (O.Cdr, [y]); x]) when x = y ->
                  Bool_r true
              | [x; y] -> Bool_r (x <> y)
              | _ -> Op_r (op, args) )
            | O.Lt -> (
              match args with
              | [Num_r x; Num_r y] -> Bool_r (x < y)
              | [x; y] when x = y -> Bool_r false
              | _ -> Op_r (op, args) )
            | O.Gt -> (
              match args with
              | [Num_r x; Num_r y] -> Bool_r (x > y)
              | [x; y] when x = y -> Bool_r false
              | _ -> Op_r (op, args) )
            | O.Leq -> (
              match args with
              | [Num_r x; Num_r y] -> Bool_r (x <= y)
              | [x; y] when x = y -> Bool_r true
              | _ -> Op_r (op, args) )
            | O.Geq -> (
              match args with
              | [Num_r x; Num_r y] -> Bool_r (x >= y)
              | [x; y] when x = y -> Bool_r true
              | _ -> Op_r (op, args) )
            | O.And -> (
              match args with
              | [Bool_r x; Bool_r y] -> Bool_r (x && y)
              | [Bool_r true; x] | [x; Bool_r true] -> x
              | [Bool_r false; _] | [_; Bool_r false] -> Bool_r false
              | [x; Op_r (O.And, [y; z])] when x = y -> Op_r (O.And, [x; z])
              | [x; Op_r (O.And, [y; z])] when x = z -> Op_r (O.And, [x; y])
              | ([x; Op_r (O.Not, [y])] | [Op_r (O.Not, [y]); x]) when x = y ->
                  Bool_r false
              (* DeMorgan's law. *)
              | [Op_r (O.Not, [x]); Op_r (O.Not, [y])] ->
                  Op_r (O.Not, [Op_r (O.Or, [x; y])])
              (* Distributivity. *)
              | [Op_r (O.Or, [a; b]); Op_r (O.Or, [c; d])] when a = c ->
                  Op_r (O.Or, [a; Op_r (O.And, [b; d])])
              | [x; y] when x = y -> x
              | _ -> Op_r (op, args) )
            | O.Or -> (
              match args with
              | [Bool_r x; Bool_r y] -> Bool_r (x || y)
              | [Bool_r false; x] | [x; Bool_r false] -> x
              | [Bool_r true; _] | [_; Bool_r true] -> Bool_r true
              | [x; Op_r (O.Or, [y; z])] when x = y -> Op_r (O.Or, [x; z])
              | [x; Op_r (O.Or, [y; z])] when x = z -> Op_r (O.Or, [x; y])
              | ([x; Op_r (O.Not, [y])] | [Op_r (O.Not, [y]); x]) when x = y ->
                  Bool_r true
              (* DeMorgan's law. *)
              | [Op_r (O.Not, [x]); Op_r (O.Not, [y])] ->
                  Op_r (O.Not, [Op_r (O.And, [x; y])])
              (* Distributivity. *)
              | [Op_r (O.And, [a; b]); Op_r (O.And, [c; d])] when a = c ->
                  Op_r (O.And, [a; Op_r (O.Or, [b; d])])
              | [x; y] when x = y -> x
              | _ -> Op_r (op, args) )
            | O.Not -> (
              match args with
              | [Bool_r x] -> Bool_r (not x)
              | [Op_r (O.Not, [x])] -> x
              | [Op_r (O.Lt, [x; y])] -> Op_r (O.Geq, [x; y])
              | [Op_r (O.Gt, [x; y])] -> Op_r (O.Leq, [x; y])
              | [Op_r (O.Leq, [x; y])] -> Op_r (O.Gt, [x; y])
              | [Op_r (O.Geq, [x; y])] -> Op_r (O.Lt, [x; y])
              | [Op_r (O.Eq, [x; y])] -> Op_r (O.Neq, [x; y])
              | [Op_r (O.Neq, [x; y])] -> Op_r (O.Eq, [x; y])
              | _ -> Op_r (op, args) )
            | O.Cons -> (
              match args with
              | [x; List_r y] -> List_r (x :: y)
              | [Op_r (O.Car, [x]); Op_r (O.Cdr, [y])] when x = y -> x
              | _ -> Op_r (op, args) )
            | O.RCons -> (
              match args with
              | [List_r y; x] -> List_r (x :: y)
              | [Op_r (O.Cdr, [y]); Op_r (O.Car, [x])] when x = y -> x
              | _ -> Op_r (O.RCons, args) )
            | O.Car -> (
              match args with
              | [List_r (x :: _)] -> x
              | [List_r []] -> raise (EvalError `CarOfEmptyList)
              | [Op_r (O.Cons, [x; _])] -> x
              | [Op_r (O.RCons, [_; x])] -> x
              | _ -> Op_r (op, args) )
            | O.Cdr -> (
              match args with
              | [List_r (_ :: xs)] -> List_r xs
              | [List_r []] -> raise (EvalError `CdrOfEmptyList)
              | [Op_r (O.Cons, [_; x])] | [Op_r (O.RCons, [x; _])] -> x
              | _ -> Op_r (op, args) )
            | O.Value -> (
              match args with
              | [Tree_r Tree.Empty] -> raise (EvalError `ValueOfEmptyTree)
              | [Tree_r (Tree.Node (x, _))] -> x
              | [Op_r (O.Tree, [x; _])] -> x
              | _ -> Op_r (op, args) )
            | O.Children -> (
              match args with
              | [Tree_r Tree.Empty] -> List_r []
              | [Tree_r (Tree.Node (_, x))] ->
                  List_r (List.map x ~f:(fun e -> Tree_r e))
              | [Op_r (O.Tree, [_; x])] -> x
              | _ -> Op_r (op, args) )
            | O.Tree -> (
              match args with
              | [x; List_r y] ->
                  let y' =
                    List.map y ~f:(fun e ->
                        match e with Tree_r t -> t | _ -> Tree.Node (e, []) )
                  in
                  Tree_r (Tree.Node (x, y'))
              | _ -> Op_r (op, args) )
            (* Invalid_argument is thrown when comparing functional values (closures). *)
          with Invalid_argument _ -> Op_r (op, args) )
  in
  eval (Option.value recursion_limit ~default:(-1)) (ref ctx) skeleton
