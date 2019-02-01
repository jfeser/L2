open Core
open Option
open Ast
open Collections
open Hypothesis

exception BadExpression

let rec is_constant (expr : expr) : bool =
  match expr with
  | `Id _ | `Let _ | `Lambda _ | `Apply _ | `Op _ -> false
  | `Num _ | `Bool _ -> true
  | `List [] -> true
  | `List (x :: xs) -> is_constant x && is_constant (`List xs)
  | `Tree Tree.Empty -> true
  | `Tree (Tree.Node (x, xs)) ->
      is_constant x && List.for_all xs ~f:(fun x' -> is_constant (`Tree x'))

let rec sequence = function
  | [] -> Some []
  | Some x :: xs -> (
    match sequence xs with Some xs' -> Some (x :: xs') | None -> None )
  | None :: _ -> None

let is_base (base_terms : expr list) (expr : expr) : expr option =
  let rec is_base_r (expr : expr) : bool =
    match expr with
    | `Id _ -> true
    | `Num _ | `Bool _ | `List _ | `Tree _ -> List.mem ~equal:( = ) base_terms expr
    | `Let (_, v, e) -> is_base_r v && is_base_r e
    | `Lambda (_, e) -> is_base_r e
    | `Apply (f, a) -> is_base_r f && List.for_all a ~f:is_base_r
    | `Op (_, args) -> List.for_all args ~f:is_base_r
  in
  if is_base_r expr then Some expr else None

let fold_constants (expr : expr) : expr option =
  let rec fold (expr : expr) : expr =
    let fold_all l = List.map l ~f:fold in
    match expr with
    | `Id _ | `Num _ | `Bool _ -> expr
    | `List l -> `List (fold_all l)
    | `Tree t -> `Tree (Tree.map t ~f:fold)
    | `Let (id, v, e) ->
        let fe = fold e in
        if is_constant fe then fe else `Let (id, fold v, fe)
    | `Lambda (a, e) ->
        let fe = fold e in
        if is_constant fe then fe else `Lambda (a, fe)
    | `Apply (f, a) -> `Apply (fold f, fold_all a)
    | `Op (op, args) ->
        let rec value_to_const (value : value) : expr option =
          match value with
          | `Num x -> Some (`Num x)
          | `Bool x -> Some (`Bool x)
          | `List x -> (
            match sequence (List.map ~f:value_to_const x) with
            | Some x' -> Some (`List x')
            | None -> None )
          | `Tree t -> (
            try
              Some
                (`Tree
                  (Tree.map t ~f:(fun x ->
                       match value_to_const x with
                       | Some x' -> x'
                       | None -> raise BadExpression )))
            with BadExpression -> None )
          | `Closure _ | `Unit -> None
        in
        let folded_args = fold_all args in
        let new_op = `Op (op, folded_args) in
        if List.for_all ~f:is_constant folded_args then
          try
            let value = Eval.eval (Ctx.empty ()) new_op in
            match value_to_const value with Some const -> const | None -> new_op
          with Eval.RuntimeError _ -> raise BadExpression
        else new_op
  in
  try Some (fold expr) with BadExpression -> None

let rewrite _ = failwith "Implement me."

(*   let top = Specification.top in *)
(*   let rec rewrite h = *)
(*     let rewrite_all l = List.map l ~f:rewrite in *)
(*     let open Skeleton in *)
(*     match h with *)
(*     | Id_h _ | Num_h _ | Bool_h _ | Hole_h _ -> h *)
(*     | List_h (l, s) -> List_h (rewrite_all l, s) *)
(*     | Tree_h (t, s) -> Tree_h (Tree.map t ~f:rewrite, s) *)
(*     | Lambda_h ((num_args, body), s) -> Lambda_h ((num_args, rewrite body), s) *)
(*     | Let_h ((bound, body), s) -> Let_h ((rewrite bound, rewrite body), s) *)
(*     | Apply_h ((func, args), s) -> *)
(*       let func = rewrite func in *)
(*       let args = rewrite_all args in *)
(*       (match func with *)
(*        | Id_h (Id.Name "concat", s) -> (match args with *)
(*            | [List_h ([], s)] -> List_h ([], s) *)
(*            | [List_h (l, s)] -> List_h (List.filter l ~f:(function *)
(*                | List_h ([], _) -> false *)
(*                | _ -> true), s) *)
(*            | _ -> Apply_h ((func, args), s)) *)

(*        | Id_h (Id.Name "append", s) -> (match args with *)
(*            | [List_h ([], s); x] | [x; List_h ([], s)] -> x *)
(*            | _ -> Apply_h ((func, args), s)) *)

(*        | Id_h (Id.Name "reverse", s) -> (match args with *)
(*            | [List_h ([], s)] -> List_h ([], s) *)
(*            | [Apply_h ((Id_h (Id.Name "reverse", _), [x]), _)] -> x *)
(*            | _ -> Apply_h ((func, args), s)) *)

(*        | Id_h (Id.Name "intersperse", s) -> (match args with *)
(*            | [List_h ([], s); _] -> List_h ([], s) *)
(*            | _ -> Apply_h ((func, args), s)) *)

(*        | Id_h (Id.Name "merge", s) -> (match args with *)
(*            | [List_h ([], s); _] | [_; List_h ([], s)] -> List_h ([], s) *)
(*            | _ -> Apply_h ((func, args), s)) *)

(*        | _ -> Apply_h ((func, args), s)) *)

(*     | Op_h ((op, raw_args), s) -> *)
(*       let args = rewrite_all raw_args in *)
(*       (match op with *)
(*        | Plus -> (match args with *)
(*            | [Num_h (0, _); x] | [x; Num_h (0, _)] -> x *)
(*            | [Op_h ((Minus, [x; y]), _); z] | [z; Op_h ((Minus, [x; y]), _)] when y = z -> x *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Minus -> (match args with *)
(*            | [x; Num_h (0, _)] -> x *)
(*            | [Op_h ((Plus, [x; y]), _); z] when x = z -> y *)
(*            | [Op_h ((Plus, [x; y]), _); z] when y = z -> x *)
(*            | [z; Op_h ((Plus, [x; y]), _)] when x = z -> Op_h ((Minus, [Num_h (0, top); y]), s) *)
(*            | [z; Op_h ((Plus, [x; y]), _)] when y = z -> Op_h ((Minus, [Num_h (0, top); x]), s) *)
(*            | [x; y] when x = y -> Num_h (0, s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Mul -> (match args with *)
(*            | [Num_h (0, _); _] | [_; Num_h (0, _)] -> Num_h (0, s) *)
(*            | [Num_h (1, _); x] | [x; Num_h (1, _)] -> x *)
(*            | [x; Op_h ((Div, [y; z]), _)] | [Op_h ((Div, [y; z]), _); x] when x = z -> y *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Div -> (match args with *)
(*            | [Num_h (0, s); _] -> Num_h (0, s) *)
(*            | [_; Num_h (0, s)] -> raise BadExpression *)
(*            | [x; Num_h (1, s)] -> x *)
(*            | [x; y] when x = y -> Num_h (1, s) *)
(*            (\* Remember that we use integer division. *\) *)
(*            | [Num_h (x, _); Num_h (y, s)] when x < y -> Num_h (0, s)  *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Mod -> (match args with *)
(*            | [Num_h (0, s); _] | [_; Num_h (1, s)] -> Num_h (0, s) *)
(*            | [_; Num_h (0, s)] -> raise BadExpression *)
(*            | [x; y] when x = y -> Num_h (0, s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Eq -> (match args with *)
(*            | [x; y] when x = y -> Bool_h (true, s) *)
(*            | [Bool_h (true, s); x] | [x; Bool_h (true, s)] -> x *)
(*            | [Bool_h (false, s); x] *)
(*            | [x; Bool_h (false, s)] -> rewrite (Op_h ((Not, [x]), s)) *)
(*            | [x; Op_h ((Cdr, [y]), _)] | [Op_h ((Cdr, [y]), _); x] when x = y -> Bool_h (false, s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Neq -> (match args with *)
(*            | [x; y] when x = y -> Bool_h (false, s) *)
(*            | [Bool_h (true, _); x] *)
(*            | [x; Bool_h (true, _)] -> rewrite (Op_h ((Not, [x]), s)) *)
(*            | [Bool_h (false, _); x] | [x; Bool_h (false, _)] -> x *)
(*            | [x; Op_h ((Cdr, [y]), _)] | [Op_h ((Cdr, [y]), _); x] when x = y -> Bool_h (true, s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Lt -> (match args with *)
(*            | [Num_h (x, _); Num_h (y, _)] when x = Int.max_value && y <> Int.max_value -> Bool_h (false, s) *)
(*            | [Num_h (x, _); Num_h (y, _)] when x <> Int.max_value && y = Int.max_value -> Bool_h (true, s) *)
(*            | [x; y] when x = y -> Bool_h (false, s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Gt -> (match args with *)
(*            | [Num_h (x, _); Num_h (y, _)] when x = Int.max_value && y <> Int.max_value -> Bool_h (true, s) *)
(*            | [Num_h (x, _); Num_h (y, _)] when x <> Int.max_value && y = Int.max_value -> Bool_h (false, s) *)
(*            | [x; y] when x = y -> Bool_h (false, s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Leq -> (match args with *)
(*            | [Num_h (x, _); Num_h (y, _)] when y = Int.max_value -> Bool_h (true, s) *)
(*            | [_; Num_h _] -> Bool_h (true, s) *)
(*            | [x; y] when x = y -> Bool_h (true, s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Geq -> (match args with *)
(*            | [x; y] when x = y -> Bool_h (true, s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | And -> (match args with *)
(*            | [x; y] when x = y -> x *)
(*            | [Bool_h (true, s); x] | [x; Bool_h (true, s)] -> x *)
(*            | [Bool_h (false, s); _] | [_; Bool_h (false, s)] -> Bool_h (false, s) *)
(*            | [x; Op_h ((And, [y; z]), _)] when x = y -> Op_h ((And, [x; z]), s) *)
(*            | [x; Op_h ((And, [y; z]), _)] when x = z -> Op_h ((And, [x; y]), s) *)
(*            | [x; Op_h ((Not, [y]), _)] | [Op_h ((Not, [y]), _); x] when x = y -> Bool_h (false, s) *)
(*            (\* DeMorgan's law. *\) *)
(*            | [Op_h ((Not, [x]), _); Op_h ((Not, [y]), _)] -> Op_h ((Not, [Op_h ((Or, [x; y]), top)]), s) *)
(*            (\* Distributivity. *\) *)
(*            | [Op_h ((Or, [a; b]), _); Op_h ((Or, [c; d]), _)] when a = c -> Op_h ((Or, [a; Op_h ((And, [b; d]), top)]), s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Or -> (match args with *)
(*            | [x; y] when x = y -> x *)
(*            | [Bool_h (false, s); x] | [x; Bool_h (false, s)] -> x *)
(*            | [Bool_h (true, s); _] | [_; Bool_h (true, s)] -> Bool_h (true, s) *)
(*            | [x; Op_h ((Or, [y; z]), _)] when x = y -> Op_h ((Or, [x; z]), s) *)
(*            | [x; Op_h ((Or, [y; z]), _)] when x = z -> Op_h ((Or, [x; y]), s) *)
(*            | [x; Op_h ((Not, [y]), _)] | [Op_h ((Not, [y]), _); x] when x = y -> Bool_h (true, s) *)
(*            | [Op_h ((Not, [x]), _); Op_h ((Not, [y]), _)] -> Op_h ((Not, [Op_h ((And, [x; y]), top)]), s) *)
(*            | [Op_h ((And, [a; b]), _); Op_h ((And, [c; d]), _)] when a = c -> Op_h ((And, [a; Op_h ((Or, [b; d]), top)]), s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Not -> (match args with *)
(*            | [Bool_h (true, s)] -> Bool_h (false, s) *)
(*            | [Bool_h (false, s)] -> Bool_h (true, s) *)
(*            | [Op_h ((Not, [x]), _)] -> x *)
(*            | [Op_h ((Lt, [x; y]), _)] -> Op_h ((Geq, [x; y]), s) *)
(*            | [Op_h ((Gt, [x; y]), _)] -> Op_h ((Leq, [x; y]), s) *)
(*            | [Op_h ((Leq, [x; y]), _)] -> Op_h ((Gt, [x; y]), s) *)
(*            | [Op_h ((Geq, [x; y]), _)] -> Op_h ((Lt, [x; y]), s) *)
(*            | [Op_h ((Eq, [x; y]), _)] -> Op_h ((Neq, [x; y]), s) *)
(*            | [Op_h ((Neq, [x; y]), _)] -> Op_h ((Eq, [x; y]), s) *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Cons -> (match args with *)
(*            | [Op_h ((Car, [x]), _); Op_h ((Cdr, [y]), _)] when x = y -> x *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | RCons -> (match args with *)
(*            | [Op_h ((Cdr, [y]), _); Op_h ((Car, [x]), _)] when x = y -> x *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Car -> (match args with *)
(*            | [List_h ([], _)] -> raise BadExpression *)
(*            | [Op_h ((Cons, [x; _]), _)] -> x *)
(*            | [Op_h ((RCons, [_; x]), _)] -> x *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Cdr -> (match args with *)
(*            | [List_h ([], s)] -> raise BadExpression *)
(*            | [Op_h ((Cons, [_; x]), _)] *)
(*            | [Op_h ((RCons, [x; _]), _)] -> x *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | If -> (match args with *)
(*            | [Bool_h (true, s); x; _] -> x *)
(*            | [Bool_h (false, s); _; x] -> x *)
(*            | [x; Bool_h (true, _); Bool_h (false, _)] -> x *)
(*            | [x; Bool_h (false, _); Bool_h (true, _)] -> Op_h ((Not, [x]), s) *)
(*            | [_; x; y] when x = y -> x *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Value -> (match args with *)
(*            | [Op_h ((Tree, [x; _]), _)] -> x *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Children -> (match args with *)
(*            | [Op_h ((Tree, [_; x]), _)] -> x *)
(*            | _ -> Op_h ((op, args), s)) *)
(*        | Tree -> (match args with *)
(*            | _ -> Op_h ((op, args), s))) *)
(*   in try Some (rewrite h) with BadExpression -> None *)

let rewrite_e (_ : Expr.t) = failwith "Implement me."

(* Option.map (rewrite (Skeleton.of_expr Specification.top e)) (fun h -> Skeleton.to_expr_exn h) *)

let simplify base_terms expr =
  match
    expr |> fold_constants >>= rewrite_e >>= fold_constants >>= is_base base_terms
  with
  | Some expr -> Some expr
  | None -> rewrite_e expr

let is_rewritable h =
  match rewrite h with Some h' -> Skeleton.equal h h' | None -> true
