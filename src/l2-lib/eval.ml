open Core
open Collections

(** Exceptions that can be thrown by the evaluation and type-checking functions. *)
exception RuntimeError of Error.t
  [@@deriving sexp]

exception HitRecursionLimit

(** Raise a bad argument error. *)
let arg_error expr =
  let err = Error.create "Bad function arguments." expr Expr.sexp_of_t in
  raise (RuntimeError err)

(** Raise a wrong # of arguments error. *)
let argn_error expr sexp =
  let err = Error.create "Wrong number of arguments." expr sexp in
  raise (RuntimeError err)

let divide_by_zero_error () =
  raise (RuntimeError (Error.of_string "Divide by zero."))

(** Evaluate an expression in the provided context. *)
let eval ?recursion_limit ctx expr =
  let rec eval limit ctx expr =
    if limit = 0 then
      match recursion_limit with
      | Some l ->
          let err =
            Error.create "Exceeded recursion limit." (l, expr)
              [%sexp_of: int * Expr.t]
          in
          raise (RuntimeError err)
      | None -> failwith "BUG: No recursion limit specified but limit = 0."
    else
      let limit = limit - 1 in
      let eval_all es = List.map ~f:(fun e -> eval limit ctx e) es in
      match expr with
      | `Num x -> `Num x
      | `Bool x -> `Bool x
      | `List x -> `List (eval_all x)
      | `Tree x -> `Tree (Tree.map x ~f:(eval limit ctx))
      | `Id id -> (
        match Ctx.lookup ctx id with
        | Some x -> x
        | None ->
            raise
            @@ RuntimeError
                 (Error.create "Unbound lookup."
                    (id, Ctx.keys ctx)
                    [%sexp_of: Expr.id * string list]) )
      | `Let (name, bound, body) ->
          let ctx = Ctx.bind ctx name `Unit in
          Ctx.update ctx name (eval limit ctx bound) ;
          eval limit ctx body
      | `Lambda _ as lambda -> `Closure (lambda, ctx)
      | `Apply (func, args) -> (
        match eval limit ctx func with
        | `Closure (`Lambda (arg_names, body), enclosed_ctx) -> (
          match List.zip arg_names (eval_all args) with
          | Some bindings ->
              let ctx =
                List.fold bindings ~init:enclosed_ctx
                  ~f:(fun ctx (arg_name, value) -> Ctx.bind ctx arg_name value )
              in
              eval limit ctx body
          | None -> argn_error expr Expr.sexp_of_t )
        | _ ->
            raise
            @@ RuntimeError
                 (Error.create "Tried to apply a non-function." expr Expr.sexp_of_t)
        )
      | `Op (op, args) -> (
          let open Expr.Op in
          match op with
          | Not -> (
            match eval_all args with
            | [`Bool x] -> `Bool (not x)
            | _ -> arg_error expr )
          | Car -> (
            match eval_all args with [`List (x :: _)] -> x | _ -> arg_error expr )
          | Cdr -> (
            match eval_all args with
            | [`List (_ :: xs)] -> `List xs
            | _ -> arg_error expr )
          | Plus -> (
            match eval_all args with
            | [`Num x; `Num y] -> `Num (x + y)
            | _ -> arg_error expr )
          | Minus -> (
            match eval_all args with
            | [`Num x; `Num y] -> `Num (x - y)
            | _ -> arg_error expr )
          | Mul -> (
            match eval_all args with
            | [`Num x; `Num y] -> `Num (x * y)
            | _ -> arg_error expr )
          | Div -> (
            match eval_all args with
            | [`Num x; `Num y] ->
                if y = 0 then divide_by_zero_error () else `Num (x / y)
            | _ -> arg_error expr )
          | Mod -> (
            match eval_all args with
            | [`Num x; `Num y] ->
                if y = 0 then divide_by_zero_error () else `Num (x mod y)
            | _ -> arg_error expr )
          | Eq -> (
            match eval_all args with
            | [x; y] -> (
              try `Bool (x = y) with Invalid_argument _ -> arg_error expr )
            | _ -> arg_error expr )
          | Neq -> (
            match eval_all args with
            | [x; y] -> (
              try `Bool (x <> y) with Invalid_argument _ -> arg_error expr )
            | _ -> arg_error expr )
          | Lt -> (
            match eval_all args with
            | [`Num x; `Num y] -> `Bool (x < y)
            | _ -> arg_error expr )
          | Leq -> (
            match eval_all args with
            | [`Num x; `Num y] -> `Bool (x <= y)
            | _ -> arg_error expr )
          | Gt -> (
            match eval_all args with
            | [`Num x; `Num y] -> `Bool (x > y)
            | _ -> arg_error expr )
          | Geq -> (
            match eval_all args with
            | [`Num x; `Num y] -> `Bool (x >= y)
            | _ -> arg_error expr )
          | And -> (
            match eval_all args with
            | [`Bool x; `Bool y] -> `Bool (x && y)
            | _ -> arg_error expr )
          | Or -> (
            match eval_all args with
            | [`Bool x; `Bool y] -> `Bool (x || y)
            | _ -> arg_error expr )
          | RCons -> (
            match eval_all args with
            | [`List y; x] -> `List (x :: y)
            | _ -> arg_error expr )
          | Cons -> (
            match eval_all args with
            | [x; `List y] -> `List (x :: y)
            | _ -> arg_error expr )
          | Tree -> (
            match eval_all args with
            | [x; `List y] ->
                let y =
                  List.map y ~f:(function `Tree t -> t | _ -> arg_error expr)
                in
                `Tree (Tree.Node (x, y))
            | _ -> arg_error expr )
          | Value -> (
            match eval_all args with
            | [`Tree (Tree.Node (x, _))] -> x
            | _ -> arg_error expr )
          | Children -> (
            match eval_all args with
            | [`Tree Tree.Empty] -> `List []
            | [`Tree (Tree.Node (_, x))] -> `List (List.map x ~f:(fun e -> `Tree e))
            | _ -> arg_error expr )
          | If -> (
            match args with
            | [ux; uy; uz] -> (
              match eval limit ctx ux with
              | `Bool x -> if x then eval limit ctx uy else eval limit ctx uz
              | _ -> arg_error expr )
            | _ -> arg_error expr ) )
  in
  match recursion_limit with
  | Some limit -> eval limit ctx expr
  | None -> eval (-1) ctx expr

let partial_eval :
    ?recursion_limit:int -> ?ctx:ExprValue.t Ctx.t -> ExprValue.t -> ExprValue.t =
 fun ?recursion_limit:(limit = -1) ?(ctx = Ctx.empty ()) expr ->
  let rec ev ctx lim expr =
    let ev_all = List.map ~f:(ev ctx lim) in
    if lim = 0 then raise HitRecursionLimit
    else
      match expr with
      | `Unit | `Closure _ | `Num _ | `Bool _ -> expr
      | `List x -> `List (List.map x ~f:(ev ctx lim))
      | `Tree x -> `Tree (Tree.map x ~f:(ev ctx lim))
      | `Lambda _ as lambda -> `Closure (lambda, ctx)
      | `Id id -> ( match Ctx.lookup ctx id with Some e -> e | None -> expr )
      | `Let (name, bound, body) ->
          let ctx' = Ctx.bind ctx name `Unit in
          Ctx.update ctx' name (ev ctx' lim bound) ;
          ev ctx' lim body
      | `Apply (func, raw_args) -> (
          let args = ev_all raw_args in
          match ev ctx lim func with
          | `Closure (`Lambda (arg_names, body), enclosed_ctx) -> (
            match List.zip arg_names args with
            | Some bindings ->
                let ctx' =
                  List.fold bindings ~init:enclosed_ctx
                    ~f:(fun ctx' (arg_name, value) -> Ctx.bind ctx' arg_name value
                  )
                in
                ev ctx' (lim - 1) body
            | None -> argn_error expr [%sexp_of: ExprValue.t] )
          | e -> `Apply (e, args) )
      | `Op (op, raw_args) -> (
          let args = lazy (List.map ~f:(ev ctx lim) raw_args) in
          try
            let open Expr.Op in
            match op with
            | Plus -> (
              match Lazy.force args with
              | [`Num x; `Num y] -> `Num (x + y)
              | [`Num 0; x] | [x; `Num 0] -> x
              | [`Op (Minus, [x; y]); z] when y = z -> x
              | [z; `Op (Minus, [x; y])] when y = z -> x
              | _ -> `Op (op, Lazy.force args) )
            | Minus -> (
              match Lazy.force args with
              | [`Num x; `Num y] -> `Num (x - y)
              | [x; `Num 0] -> x
              | [`Op (Plus, [x; y]); z] when x = z -> y
              | [`Op (Plus, [x; y]); z] when y = z -> x
              | [z; `Op (Plus, [x; y])] when x = z -> `Op (Minus, [`Num 0; y])
              | [z; `Op (Plus, [x; y])] when y = z -> `Op (Minus, [`Num 0; x])
              | [x; y] when x = y -> `Num 0
              | _ -> `Op (op, Lazy.force args) )
            | Mul -> (
              match Lazy.force args with
              | [`Num x; `Num y] -> `Num (x * y)
              | [`Num 0; _] | [_; `Num 0] -> `Num 0
              | [`Num 1; x] | [x; `Num 1] -> x
              | [x; `Op (Div, [y; z])] when x = z -> y
              | [`Op (Div, [y; z]); x] when x = z -> y
              | _ -> `Op (op, Lazy.force args) )
            | Div -> (
              match Lazy.force args with
              | [_; `Num 0] -> divide_by_zero_error ()
              | [`Num x; `Num y] -> `Num (x / y)
              | [`Num 0; _] -> `Num 0
              | [x; `Num 1] -> x
              | [x; y] when x = y -> `Num 1
              | _ -> `Op (op, Lazy.force args) )
            | Mod -> (
              match Lazy.force args with
              | [_; `Num 0] -> divide_by_zero_error ()
              | [`Num x; `Num y] -> `Num (x mod y)
              | [`Num 0; _] | [_; `Num 1] -> `Num 0
              | [x; y] when x = y -> `Num 0
              | _ -> `Op (op, Lazy.force args) )
            | Eq -> (
              match Lazy.force args with
              | [`Bool true; x] | [x; `Bool true] -> x
              | [`Bool false; x] | [x; `Bool false] ->
                  ev ctx (lim - 1) (`Op (Not, [x]))
              | [x; `Op (Cdr, [y])] when x = y -> `Bool false
              | [`Op (Cdr, [y]); x] when x = y -> `Bool false
              | [x; y] -> `Bool (x = y)
              | _ -> `Op (op, Lazy.force args) )
            | Neq -> (
              match Lazy.force args with
              | [`Bool true; x] | [x; `Bool true] ->
                  ev ctx (lim - 1) (`Op (Not, [x]))
              | [`Bool false; x] | [x; `Bool false] -> x
              | [x; `Op (Cdr, [y])] when x = y -> `Bool true
              | [`Op (Cdr, [y]); x] when x = y -> `Bool true
              | [x; y] -> `Bool (x <> y)
              | _ -> `Op (op, Lazy.force args) )
            | Lt -> (
              match Lazy.force args with
              | [`Num x; `Num y] -> `Bool (x < y)
              | [`Id "inf"; _] -> `Bool false
              | [x; y] when x = y -> `Bool false
              | _ -> `Op (op, Lazy.force args) )
            | Gt -> (
              match Lazy.force args with
              | [`Num x; `Num y] -> `Bool (x > y)
              | [_; `Id "inf"] -> `Bool false
              | [x; y] when x = y -> `Bool false
              | _ -> `Op (op, Lazy.force args) )
            | Leq -> (
              match Lazy.force args with
              | [`Num x; `Num y] -> `Bool (x <= y)
              | [_; `Id "inf"] -> `Bool true
              | [x; y] when x = y -> `Bool true
              | _ -> `Op (op, Lazy.force args) )
            | Geq -> (
              match Lazy.force args with
              | [`Num x; `Num y] -> `Bool (x >= y)
              | [`Id "inf"; _] -> `Bool true
              | [x; y] when x = y -> `Bool true
              | _ -> `Op (op, Lazy.force args) )
            | And -> (
              match Lazy.force args with
              | [`Bool x; `Bool y] -> `Bool (x && y)
              | [`Bool true; x] | [x; `Bool true] -> x
              | [`Bool false; _] | [_; `Bool false] -> `Bool false
              | [x; `Op (And, [y; z])] when x = y -> `Op (And, [x; z])
              | [x; `Op (And, [y; z])] when x = z -> `Op (And, [x; y])
              | [x; `Op (Not, [y])] when x = y -> `Bool false
              | [`Op (Not, [y]); x] when x = y -> `Bool false
              (* DeMorgan's law. *)
              | [`Op (Not, [x]); `Op (Not, [y])] -> `Op (Not, [`Op (Or, [x; y])])
              (* Distributivity. *)
              | [`Op (Or, [a; b]); `Op (Or, [c; d])] when a = c ->
                  `Op (Or, [a; `Op (And, [b; d])])
              | [x; y] when x = y -> x
              | _ -> `Op (op, Lazy.force args) )
            | Or -> (
              match Lazy.force args with
              | [`Bool x; `Bool y] -> `Bool (x || y)
              | [`Bool false; x] | [x; `Bool false] -> x
              | [`Bool true; _] | [_; `Bool true] -> `Bool true
              | [x; `Op (Or, [y; z])] when x = y -> `Op (Or, [x; z])
              | [x; `Op (Or, [y; z])] when x = z -> `Op (Or, [x; y])
              | [x; `Op (Not, [y])] when x = y -> `Bool true
              | [`Op (Not, [y]); x] when x = y -> `Bool true
              (* DeMorgan's law. *)
              | [`Op (Not, [x]); `Op (Not, [y])] -> `Op (Not, [`Op (And, [x; y])])
              (* Distributivity. *)
              | [`Op (And, [a; b]); `Op (And, [c; d])] when a = c ->
                  `Op (And, [a; `Op (Or, [b; d])])
              | [x; y] when x = y -> x
              | _ -> `Op (op, Lazy.force args) )
            | Not -> (
              match Lazy.force args with
              | [`Bool x] -> `Bool (not x)
              | [`Op (Not, [x])] -> x
              | [`Op (Lt, [x; y])] -> `Op (Geq, [x; y])
              | [`Op (Gt, [x; y])] -> `Op (Leq, [x; y])
              | [`Op (Leq, [x; y])] -> `Op (Gt, [x; y])
              | [`Op (Geq, [x; y])] -> `Op (Lt, [x; y])
              | [`Op (Eq, [x; y])] -> `Op (Neq, [x; y])
              | [`Op (Neq, [x; y])] -> `Op (Eq, [x; y])
              | _ -> `Op (op, Lazy.force args) )
            | Cons -> (
              match Lazy.force args with
              | [x; `List y] -> `List (x :: y)
              | [`Op (Car, [x]); `Op (Cdr, [y])] when x = y -> x
              | _ -> `Op (op, Lazy.force args) )
            | RCons -> (
              match Lazy.force args with
              | [`List y; x] -> `List (x :: y)
              | [`Op (Cdr, [y]); `Op (Car, [x])] when x = y -> x
              | _ -> `Op (RCons, Lazy.force args) )
            | Car -> (
              match Lazy.force args with
              | [`List (x :: _)] -> x
              | [`List []] ->
                  raise (RuntimeError (Error.of_string "Car of empty list."))
              | [`Op (Cons, [x; _])] -> x
              | [`Op (RCons, [_; x])] -> x
              | _ -> `Op (op, Lazy.force args) )
            | Cdr -> (
              match Lazy.force args with
              | [`List (_ :: xs)] -> `List xs
              | [`List []] ->
                  raise (RuntimeError (Error.of_string "Cdr of empty list."))
              | [`Op (Cons, [_; x])] | [`Op (RCons, [x; _])] -> x
              | _ -> `Op (op, Lazy.force args) )
            | If -> (
              match raw_args with
              | [ux; uy; uz] -> (
                match ev ctx lim ux with
                | `Bool x -> if x then ev ctx lim uy else ev ctx lim uz
                | `Op (Not, [x]) -> `Op (If, [x; uz; uy])
                | x -> `Op (If, [x; uy; uz]) )
              | _ -> expr )
            | Value -> (
              match Lazy.force args with
              | [`Tree Tree.Empty] ->
                  raise (RuntimeError (Error.of_string "Value of empty tree."))
              | [`Tree (Tree.Node (x, _))] -> x
              | [`Op (Tree, [x; _])] -> x
              | _ -> `Op (op, Lazy.force args) )
            | Children -> (
              match Lazy.force args with
              | [`Tree Tree.Empty] -> `List []
              | [`Tree (Tree.Node (_, x))] ->
                  `List (List.map x ~f:(fun e -> `Tree e))
              | [`Op (Tree, [_; x])] -> x
              | _ -> `Op (op, Lazy.force args) )
            | Tree -> (
              match Lazy.force args with
              | [x; `List y] ->
                  let y' =
                    List.map y ~f:(fun e ->
                        match e with `Tree t -> t | _ -> Tree.Node (e, []) )
                  in
                  `Tree (Tree.Node (x, y'))
              | _ -> `Op (op, Lazy.force args) )
            (* Invalid_argument is thrown when comparing functional values (closures). *)
          with Invalid_argument _ -> `Op (op, Lazy.force args) )
  in
  ev ctx limit expr
