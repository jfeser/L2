open Core.Std
open Core.Option

open Ast
open Collections

exception BadExpression

let rec is_constant (expr: expr) : bool =
  match expr with
  | `Id _ | `Let _ | `Lambda _ | `Apply _ | `Op _ -> false
  | `Num _ | `Bool _ -> true
  | `List [] -> true
  | `List (x::xs) -> (is_constant x) && (is_constant (`List xs))
  | `Tree Tree.Empty -> true
  | `Tree (Tree.Node (x, xs)) ->
    (is_constant x) && (List.for_all xs ~f:(fun x' -> is_constant (`Tree x')))

let rec sequence = function
  | [] -> Some []
  | (Some x)::xs -> (match sequence xs with
      | Some xs' -> Some (x::xs')
      | None -> None)
  | None::_ -> None

let is_base (base_terms: expr list) (expr: expr) : expr option =
  let rec is_base_r (expr: expr) : bool = match expr with
    | `Id _ -> true
    | `Num _  | `Bool _ | `List _ | `Tree _ -> List.mem base_terms expr
    | `Let (_, v, e) -> (is_base_r v) && (is_base_r e)
    | `Lambda (_, e)  -> is_base_r e
    | `Apply (f, a)   -> (is_base_r f) && (List.for_all a ~f:is_base_r)
    | `Op (_, args)  -> List.for_all args ~f:is_base_r
  in if is_base_r expr then Some expr else None

let fold_constants (expr: expr) : expr option =
  let rec fold (expr: expr) : expr =
    let fold_all l = List.map l ~f:fold in
    match expr with
    | `Id _
    | `Num _
    | `Bool _         -> expr
    | `List l         -> `List (fold_all l)
    | `Tree t         -> `Tree (Tree.map t ~f:fold)
    | `Let (id, v, e) -> let fe = fold e in if is_constant fe then fe else `Let (id, fold v, fe)
    | `Lambda (a, e)  -> let fe = fold e in if is_constant fe then fe else `Lambda (a, fe)
    | `Apply (f, a)   -> `Apply (fold f, fold_all a)
    | `Op (op, args)  ->
      let rec value_to_const (value: Eval.value) : expr option =
        match value with
        | `Num x -> Some (`Num x)
        | `Bool x -> Some (`Bool x)
        | `List x -> (match sequence (List.map ~f:value_to_const x) with
            | Some x' -> Some (`List x')
            | None -> None)
        | `Tree t ->
          (try
             Some (`Tree (Tree.map t ~f:(fun x ->
                 match value_to_const x with
                 | Some x' -> x'
                 | None -> raise BadExpression)))
           with BadExpression -> None)
        | `Closure _
        | `Unit -> None
      in
      let folded_args = fold_all args in
      let new_op = `Op (op, folded_args) in
      if List.for_all ~f:is_constant folded_args then
        try
          let value = Eval.eval (Ctx.empty ()) new_op in
          match value_to_const value with
          | Some const -> const
          | None -> new_op
        with Eval.RuntimeError _ -> raise BadExpression
      else new_op
  in try Some (fold expr) with BadExpression -> None

let rewrite (expr: expr) : expr option =
  let rec rewrite_r (expr: expr) : expr =
    let rewrite_all l = List.map l ~f:rewrite_r in
    match expr with
    | `Id _ | `Num _ | `Bool _ -> expr
    | `List l -> `List (List.map l ~f:rewrite_r)
    | `Tree t -> `Tree (Tree.map t ~f:rewrite_r)
    | `Lambda (a, e)  -> `Lambda (a, rewrite_r e)
    | `Let (id, v, e) -> `Let (id, rewrite_r v, rewrite_r e)
    | `Apply (f, raw_args)   ->
      let func = rewrite_r f in
      let args = rewrite_all raw_args in
      (match func with
       | `Id "concat" -> (match args with
           | [`List []] -> `List []
           | [`List l] -> `List (List.filter l ~f:(fun l' -> match l' with
               | `List [] -> false
               | _ -> true))
           | _ -> `Apply (func, args))

       | `Id "append" -> (match args with
           | [`List []; x] | [x; `List []] -> x
           | _ -> `Apply (func, args))

       | `Id "reverse" -> (match args with
           | [`List []] -> `List []
           | [`Apply (`Id "reverse", [x])] -> x
           | _ -> `Apply (func, args))

       | `Id "intersperse" -> (match args with
           | [`List []; _] -> `List []
           | _ -> `Apply (func, args))

       | _ -> `Apply (func, args))

    | `Op (op, raw_args) ->
      let args = rewrite_all raw_args in
      (match op with
       | Plus -> (match args with
           | [`Num 0; x] | [x; `Num 0] -> x
           | [`Op (Minus, [x; y]); z]
           | [z; `Op (Minus, [x; y])] when y = z -> x
           | _ -> `Op (op, args))
       | Minus -> (match args with
           | [x; `Num 0] -> x
           | [`Op (Plus, [x; y]); z] when x = z -> y
           | [`Op (Plus, [x; y]); z] when y = z -> x
           | [z; `Op (Plus, [x; y])] when x = z -> `Op (Minus, [`Num 0; y])
           | [z; `Op (Plus, [x; y])] when y = z -> `Op (Minus, [`Num 0; x])
           | [x; y] when x = y -> `Num 0
           | _ -> `Op (op, args))
       | Mul -> (match args with
           | [`Num 0; _] | [_; `Num 0] -> `Num 0
           | [`Num 1; x] | [x; `Num 1] -> x
           | [x; `Op (Div, [y; z])]
           | [`Op (Div, [y; z]); x] when x = z -> y
           | _ -> `Op (op, args))
       | Div -> (match args with
           | [`Num 0; _] -> `Num 0
           | [_; `Num 0] -> raise BadExpression
           | [x; `Num 1] -> x
           | [x; y] when x = y -> `Num 1
           | [`Num x; `Num y] when x < y -> `Num 0 (* Remember that we use integer division. *)
           | _ -> `Op (op, args))
       | Mod -> (match args with
           | [`Num 0; _] | [_; `Num 1] -> `Num 0
           | [_; `Num 0] -> raise BadExpression
           | [x; y] when x = y -> `Num 0
           | _ -> `Op (op, args))
       | Eq -> (match args with
           | [x; y] when x = y -> `Bool true
           | [`Bool true; x] | [x; `Bool true] -> x
           | [`Bool false; x]
           | [x; `Bool false] -> rewrite_r (`Op (Not, [x]))
           | [x; `Op (Cdr, [y])] | [`Op (Cdr, [y]); x] when x = y -> `Bool false
           | _ -> `Op (op, args))
       | Neq -> (match args with
           | [x; y] when x = y -> `Bool false
           | [`Bool true; x]
           | [x; `Bool true] -> rewrite_r (`Op (Not, [x]))
           | [`Bool false; x] | [x; `Bool false] -> x
           | [x; `Op (Cdr, [y])] | [`Op (Cdr, [y]); x] when x = y -> `Bool true
           | _ -> `Op (op, args))
       | Lt -> (match args with
           | [`Id "inf"; _] -> `Bool false
           | [x; y] when x = y -> `Bool false
           | _ -> `Op (op, args))
       | Gt -> (match args with
           | [_; `Id "inf"] -> `Bool false
           | [x; y] when x = y -> `Bool false
           | _ -> `Op (op, args))
       | Leq -> (match args with
           | [`Id "inf"; x] when x <> (`Id "inf") -> `Bool true
           | [_; `Id "inf"] -> `Bool true
           | [x; y] when x = y -> `Bool true
           | _ -> `Op (op, args))
       | Geq -> (match args with
           | [`Id "inf"; x] when x <> (`Id "inf") -> `Bool false
           | [`Id "inf"; _] -> `Bool true
           | [x; y] when x = y -> `Bool true
           | _ -> `Op (op, args))
       | And -> (match args with
           | [x; y] when x = y -> x
           | [`Bool true; x] | [x; `Bool true] -> x
           | [`Bool false; _] | [_; `Bool false] -> `Bool false
           | [x; `Op (And, [y; z])] when x = y -> `Op (And, [x; z])
           | [x; `Op (And, [y; z])] when x = z -> `Op (And, [x; y])
           | [x; `Op (Not, [y])] | [`Op (Not, [y]); x] when x = y -> `Bool false
           (* DeMorgan's law. *)
           | [`Op (Not, [x]); `Op (Not, [y])] -> `Op (Not, [`Op (Or, [x; y])])
           (* Distributivity. *)
           | [`Op (Or, [a; b]); `Op (Or, [c; d])] when a = c -> `Op (Or, [a; `Op (And, [b; d])])
           | _ -> `Op (op, args))
       | Or -> (match args with
           | [x; y] when x = y -> x
           | [`Bool false; x] | [x; `Bool false] -> x
           | [`Bool true; _] | [_; `Bool true] -> `Bool true
           | [x; `Op (Or, [y; z])] when x = y -> `Op (Or, [x; z])
           | [x; `Op (Or, [y; z])] when x = z -> `Op (Or, [x; y])
           | [x; `Op (Not, [y])] | [`Op (Not, [y]); x] when x = y -> `Bool true
           | [`Op (Not, [x]); `Op (Not, [y])] -> `Op (Not, [`Op (And, [x; y])])
           | [`Op (And, [a; b]); `Op (And, [c; d])] when a = c -> `Op (And, [a; `Op (Or, [b; d])])
           | _ -> `Op (op, args))
       | Not -> (match args with
           | [`Bool true] -> `Bool false
           | [`Bool false] -> `Bool true
           | [`Op (Not, [x])] -> x
           | [`Op (Lt, [x; y])] -> `Op (Geq, [x; y])
           | [`Op (Gt, [x; y])] -> `Op (Leq, [x; y])
           | [`Op (Leq, [x; y])] -> `Op (Gt, [x; y])
           | [`Op (Geq, [x; y])] -> `Op (Lt, [x; y])
           | [`Op (Eq, [x; y])] -> `Op (Neq, [x; y])
           | [`Op (Neq, [x; y])] -> `Op (Eq, [x; y])
           | _ -> `Op (op, args))
       | Cons -> (match args with
           | [`Op (Car, [x]); `Op (Cdr, [y])] when x = y -> x
           | _ -> `Op (op, args))
       | RCons -> (match args with
           | [`Op (Cdr, [y]); `Op (Car, [x])] when x = y -> x
           | _ -> `Op (op, args))
       | Car -> (match args with
           | [`List []] -> raise BadExpression
           | [`Op (Cons, [x; _])] -> x
           | [`Op (RCons, [_; x])] -> x
           | _ -> `Op (op, args))
       | Cdr -> (match args with
           | [`List []] -> raise BadExpression
           | [`Op (Cons, [_; x])]
           | [`Op (RCons, [x; _])] -> x
           | _ -> `Op (op, args))
       | If -> (match args with
           | [`Bool true; x; _] -> x
           | [`Bool false; _; x] -> x
           | [x; `Bool true; `Bool false] -> x
           | [x; `Bool false; `Bool true] -> `Op (Not, [x])
           | [_; x; y] when x = y -> x
           | _ -> `Op (op, args))
       | Value -> (match args with
           | [`Op (Tree, [x; _])] -> x
           | _ -> `Op (op, args))
       | Children -> (match args with
           | [`Op (Tree, [_; x])] -> x
           | _ -> `Op (op, args))
       | Tree -> (match args with
           | _ -> `Op (op, args)))
  in try Some (rewrite_r expr) with BadExpression -> None

let simplify base_terms expr =
  match expr |> fold_constants >>= rewrite >>= fold_constants >>= (is_base base_terms) with
  | Some expr -> Some expr
  | None -> rewrite expr

let is_redundant (base_terms: expr list) (expr: expr) : bool =
  let result = match rewrite expr with
    | Some expr' -> Expr.cost expr' < Expr.cost expr
    | None -> true
  in
  (if result then
     let msg = sprintf "Redundant %s = %B\n" (Expr.to_string expr) result in
     LOG msg NAME "l2.search" LEVEL INFO);
  result
