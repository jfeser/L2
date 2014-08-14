open Core.Std
open Core.Option
open Ast

exception BadExpression

let is_constant (expr: expr) : bool =
  match expr with
  | `Id _ | `Let _ | `Define _ | `Lambda _ | `Apply _ | `Op _ -> false
  | `Num _ | `Bool _ | `List _ -> true

let expr_to_const (expr: expr) : const option =
  match expr with
  | `Num x -> Some (`Num x)
  | `Bool x -> Some (`Bool x)
  | `List x -> Some (`List x)
  | `Id _
  | `Let _
  | `Lambda _
  | `Define _
  | `Apply _
  | `Op _ -> None

let rec normalize (expr: expr) : expr =
  let normalize_all l = List.map l ~f:normalize in
  match expr with
  | `Num _
  | `Bool _
  | `List _
  | `Id _           -> expr
  | `Let (id, v, e) -> `Let (id, normalize v, normalize e)
  | `Lambda (a, r, e)  -> `Lambda (a, r, normalize e)
  | `Define (id, e) -> `Define (id, normalize e)
  | `Apply (f, a)   -> `Apply (normalize f, normalize_all a)
  | `Op (op, args)  ->
     let op_data = operator_data op in
     let unsorted_args =
       normalize_all args |>
         List.fold_right ~init:[]
                         ~f:(fun e a -> match e with
                                        | `Op (cop, cargs) -> if (op = cop) && (op_data.assoc)
                                                              then cargs @ a else e::a
                                        | _ -> e::a) in
     if op_data.commut
     then `Op (op, List.sort ~cmp:compare_expr unsorted_args)
     else `Op (op, unsorted_args)

let rec denormalize (expr: expr) : expr =
  let denormalize_all l = List.map l ~f:denormalize in
  match expr with
  | `Id _
  | `Num _
  | `Bool _
  | `List _         -> expr
  | `Let (id, v, e) -> `Let (id, denormalize v, denormalize e)
  | `Lambda (a, r, e)  -> `Lambda (a, r, denormalize e)
  | `Define (id, e) -> `Define (id, denormalize e)
  | `Apply (f, a)   -> `Apply (denormalize f, denormalize_all a)
  | `Op (op, args)  ->
     let arity = (operator_data op).arity in
     let new_args = if (List.length args) > arity
                    then let a1, a2 = List.split_n args (arity - 1) in a1 @ [`Op (op, a2)]
                    else args in
     `Op (op, denormalize_all new_args)

let fold_constants (expr: expr) : expr option =
  let rec fold (expr: expr) : expr =
    let fold_all l = List.map l ~f:fold in
    match expr with
    | `Id _
    | `Num _
    | `Bool _
    | `List _         -> expr
    | `Let (id, v, e) -> let fe = fold e in if is_constant fe then fe else `Let (id, fold v, fe)
    | `Lambda (a, r, e)  -> let fe = fold e in if is_constant fe then fe else `Lambda (a, r, fe)
    | `Define (id, e) -> `Define (id, fold e)
    | `Apply (f, a)   -> `Apply (fold f, fold_all a)
    | `Op (op, args)  -> let folded_args = fold_all args in
                         let new_op = `Op (op, folded_args) in
                         if List.for_all ~f:is_constant folded_args then
                           (try ((Eval.value_to_const (Eval.eval (Ctx.empty ()) new_op)) :> expr) with
                            | Eval.RuntimeError _ -> new_op)
                         else new_op
  in try Some (fold expr) with Eval.RuntimeError _ -> None

let rewrite (expr: expr) : expr option =
  let rec rewrite_r (expr: expr) : expr =
    let rewrite_all l = List.map l ~f:rewrite_r in
    match expr with
    | `Id _
    | `Num _
    | `Bool _
    | `List _ -> expr
    | `Lambda (a, r, e)  -> `Lambda (a, r, rewrite_r e)
    | `Let (id, v, e) -> `Let (id, rewrite_r v, rewrite_r e)
    | `Define (id, e) -> `Define (id, rewrite_r e)
    | `Apply (f, a)   -> `Apply (rewrite_r f, rewrite_all a)
    | `Op (op, raw_args)  -> let args = rewrite_all raw_args in
                             (match op with
                              | Plus -> (match args with
                                         | [`Num 0; x] | [x; `Num 0] -> x
                                         | [`Op (Minus, [x; y]); z] when y = z -> x
                                         | _ -> `Op (op, args))
                              | Minus -> (match args with
                                          | [x; `Num 0] -> x
                                          | [`Op (Plus, [x; y]); z] when y = z -> x
                                          | [`Op (Plus, [x; y]); z] when x = z -> y
                                          | [x; y] when x = y -> `Num 0
                                          | _ -> `Op (op, args))
                              | Mul -> (match args with
                                        | [`Num 0; _] | [_; `Num 0] -> `Num 0
                                        | [`Num 1; x] | [x; `Num 1] -> x
                                        | _ -> `Op (op, args))
                              | Div -> (match args with
                                        | [`Num 0; _] -> `Num 0
                                        | [_; `Num 0] -> raise BadExpression
                                        | [x; `Num 1] -> x
                                        | [x; y] when x = y -> `Num 1
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
                                       | _ -> `Op (op, args))
                              | Neq -> (match args with
                                        | [x; y] when x = y -> `Bool false
                                        | [`Bool true; x]
                                        | [x; `Bool true] -> rewrite_r (`Op (Not, [x]))
                                        | [`Bool false; x] | [x; `Bool false] -> x
                                        | _ -> `Op (op, args))
                              | Lt
                              | Gt -> (match args with
                                       | [x; y] when x = y -> `Bool false
                                       | _ -> `Op (op, args))
                              | Leq
                              | Geq -> (match args with
                                        | [x; y] when x = y -> `Bool true
                                        | _ -> `Op (op, args))
                              | And -> (match args with
                                        | [`Bool true; x] | [x; `Bool true] -> x
                                        | [`Bool false; _] | [_; `Bool false] -> `Bool false
                                        | _ -> `Op (op, args))
                              | Or -> (match args with
                                       | [`Bool false; x] | [x; `Bool false] -> x
                                       | [`Bool true; _] | [_; `Bool true] -> `Bool true
                                       | _ -> `Op (op, args))
                              | Not -> (match args with
                                        | [`Op (Not, [x])] -> x
                                        | [`Op (Lt, [x; y])] -> `Op (Geq, [x; y])
                                        | [`Op (Gt, [x; y])] -> `Op (Leq, [x; y])
                                        | [`Op (Leq, [x; y])] -> `Op (Gt, [x; y])
                                        | [`Op (Geq, [x; y])] -> `Op (Lt, [x; y])
                                        | [`Op (Eq, [x; y])] -> `Op (Neq, [x; y])
                                        | [`Op (Neq, [x; y])] -> `Op (Eq, [x; y])
                                        | _ -> `Op (op, args))
                              | Cons -> (match args with
                                         | [x; `List ([], t)] -> (match expr_to_const x with
                                                                  | Some cx -> `List ([cx], t)
                                                                  | None -> `Op (op, args))
                                         | [x; `List (xs, t)] -> (match expr_to_const x with
                                                                  | Some cx -> `List (cx::xs, t)
                                                                  | None -> `Op (op, args))
                                         | _ -> `Op (op, args))
                              | Car
                              | Cdr -> `Op (op, args)
                              | If -> (match args with
                                       | [`Bool true; x; _] -> x
                                       | [`Bool false; _; x] -> x
                                       | [x; `Bool true; `Bool false] -> x
                                       | [x; `Bool false; `Bool true] -> `Op (Not, [x])
                                       | [_; x; y] when x = y -> x
                                       | _ -> `Op (op, args))
                              | Fold
                              | Foldl -> (match args with
                                          | [`List ([], _); _; x] -> x
                                          | _ -> `Op (op, args))
                              | Map -> (match args with
                                        | [`List ([], t); _] -> `List ([], t)
                                        | _ -> `Op (op, args))
                              | Filter -> (match args with
                                           | [`List ([], t); _] -> `List ([], t)
                                           | _ -> `Op (op, args)))
  in try Some (rewrite_r expr) with BadExpression -> None

let simplify expr = expr |> fold_constants >>= rewrite >>= fold_constants >>| normalize
let complicate = denormalize
