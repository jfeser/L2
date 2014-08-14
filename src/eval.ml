open Core.Std
open Ast

(** Exceptions that can be thrown by the evaluation and typechecking
functions. *)
exception RuntimeError of string
exception TypeError of string

(** Raise a bad argument error. *)
let arg_error op args =
  raise (RuntimeError (Printf.sprintf "Bad arguments to %s %s."
                                      (Ast.operator_to_str op)
                                      (sexp "(" (List.map ~f:expr_to_string args) ")")))

let type_error op args =
  raise (RuntimeError (Printf.sprintf "Bad arguments to %s %s."
                                      (Ast.operator_to_str op)
                                      (sexp "(" (List.map ~f:typ_to_string args) ")")))

(** Raise a wrong # of arguments error. *)
let argn_error id = raise (RuntimeError ("Wrong # of arguments to " ^ id))

(** Convert a value to a constant, raising an error if v is a type
that cannot be converted. *)
let value_to_const (v: value) : const =
  match v with
  | `Num x -> `Num x
  | `Bool x -> `Bool x
  | `List x -> `List x
  | `Closure _
  | `Unit -> raise (RuntimeError ((value_to_string v) ^ " is not a constant."))

let rec typeof_const (const: const) : typ =
  match const with
  | `Num _ -> Num_t
  | `Bool _ -> Bool_t
  | `List ([], t) -> List_t t
  | `List (_, Unit_t)
  | `List (_, Arrow_t _) -> raise (TypeError "List tagged with non-constant type.")
  | `List (x::xs, tag_t) ->
     let t = typeof_const x in
     let ts = List.map ~f:typeof_const xs in
     if List.for_all ~f:((=) t) ts
     then if t = tag_t then List_t t
          else raise (TypeError "List tagged with incorrect type.")
     else raise (TypeError "List contains multiple types.")

(** Get the type of an expression given a type context. *)
let rec typeof_expr ctx (expr: expr) : typ =
  let typeof_all es = List.map ~f:(typeof_expr ctx) es in
  match expr with
  | `Num x  -> typeof_const (`Num x)
  | `Bool x -> typeof_const (`Bool x)
  | `List x -> typeof_const (`List x)
  | `Op (op, untyped_args) ->
     (let args = typeof_all untyped_args in
      match op with
      | Not -> (match args with [Bool_t] -> Bool_t     | _ -> type_error op args)
      | Car -> (match args with [List_t e] -> e        | _ -> type_error op args)
      | Cdr -> (match args with [List_t e] -> List_t e | _ -> type_error op args)
      | Mod
      | Div
      | Mul
      | Minus
      | Plus -> (match args with [Num_t; Num_t] -> Num_t | _ -> type_error op args)
      | Eq
      | Neq -> (match args with [_; _] -> Bool_t | _ -> type_error op args)
      | Geq
      | Gt
      | Leq
      | Lt -> (match args with [Num_t; Num_t] -> Bool_t  | _ -> type_error op args)
      | Or
      | And -> (match args with [Bool_t; Bool_t] -> Bool_t | _ -> type_error op args)
      | Cons -> (match args with
                 | [t1; List_t t2] when t1 = t2 -> List_t t1
                 | _ -> type_error op args)
      | If -> (match args with
               | [Bool_t; t1; t2] when t1 = t2 -> t1
               | _ -> type_error op args)
      | Map -> (match args with
                | [List_t it1; Arrow_t ([it2], ot)] when it1 = it2 -> List_t ot
                | _ -> type_error op args)
      | Fold
      | Foldl -> (match args with
                  | [List_t et2; Arrow_t ([at1; et1], at2); at3]
                      when (Util.all_equal ~eq:(=) [at1; at2; at3]) && (et1 = et2) -> at2
                  | _ -> type_error op args)
      | Filter -> (match args with
                   | [List_t et1; Arrow_t ([et2], Bool_t)] when et1 = et2 -> List_t et1
                   | _ -> type_error op args))
  | `Id name -> Ctx.lookup_exn ctx name
  | `Let (name, e1, e2) ->
     let ctx' = Ctx.bind ctx name (typeof_expr ctx e1) in
     typeof_expr ctx' e2
  | `Define _ -> Unit_t
  | `Lambda (args, ret_typ, _) ->
     let arg_typs = List.map args ~f:(fun (_, typ) -> typ) in
     Arrow_t (arg_typs, ret_typ)
  | `Apply (e, args) ->
     (match typeof_expr ctx e with
      | Arrow_t (its, ot) ->
         if its = (typeof_all args) then ot
         else raise @@ RuntimeError ("Bad argument to " ^ (expr_to_string e))
      | _ -> raise @@ RuntimeError "Tried to apply non-lambda.")

let rec tctx_of_vctx vctx =
  ref (String.Map.map !vctx ~f:(typeof_value))

(** Get the type of a value. No type context is necessary, since ids
are not values. *)
and typeof_value (value: value) : typ =
  match value with
  | `Num x  -> typeof_const (`Num x)
  | `Bool x -> typeof_const (`Bool x)
  | `List x -> typeof_const (`List x)
  | `Unit -> Unit_t
  | `Closure (`Lambda (args, ret_typ, _), _) ->
     let arg_typs = List.map args ~f:(fun (_, typ) -> typ) in
     Arrow_t (arg_typs, ret_typ)

(** Evaluate an expression in the provided context. *)
let rec eval env (expr: expr) : value =
  let eval_all l = List.map l ~f:(eval env) in
  match expr with
  | `Num x  -> `Num x
  | `Bool x -> `Bool x
  | `List x -> `List x
  | `Id id  -> Ctx.lookup_exn env id
  | `Let (id, v, e) -> let env' = Ctx.bind env id `Unit in
                       Ctx.update env' id (eval env' v);
                       eval env' e
  | `Define _ ->
     raise (RuntimeError "Define is not allowed in eval (use eval_prog).")
  | `Lambda lambda -> `Closure (`Lambda lambda, env)
  | `Apply (func, args) ->
     (match eval env func with
      | `Closure (`Lambda (arg_names, _, e), enclosed_env) ->
         (match List.zip arg_names (eval_all args) with
          | Some bindings ->
             let new_env = List.fold_left bindings
                                          ~init:(enclosed_env)
                                          ~f:(fun nv ((id, _), v) -> Ctx.bind nv id v) in
             eval new_env e
          | None -> argn_error @@ expr_to_string e)
      | _ -> raise (RuntimeError "Tried to apply a non-function."))
  | `Op (op, args) ->
     (match op with
      | Not -> (match eval_all args with
                | [`Bool x] -> `Bool (not x)
                | _ -> arg_error op args)
      | Car -> (match eval_all args with
                | [`List ((x::_), _)] -> (x :> value)
                | _ -> arg_error op args)
      | Cdr -> (match eval_all args with
                | [`List ((_::xs), t)] -> ((`List (xs, t)) :> value)
                | _ -> arg_error op args)
      | Plus -> (match eval_all args with
                 | [`Num x; `Num y] -> `Num (x + y)
                 | _ -> arg_error op args)
      | Minus -> (match eval_all args with
                  | [`Num x; `Num y] -> `Num (x - y)
                  | _ -> arg_error op args)
      | Mul -> (match eval_all args with
                | [`Num x; `Num y] -> `Num (x * y)
                | _ -> arg_error op args)
      | Div -> (match eval_all args with
                | [`Num x; `Num y] -> if y = 0 then raise (RuntimeError "Divide by zero.")
                                      else `Num (x / y)
                | _ -> arg_error op args)
      | Mod -> (match eval_all args with
                | [`Num x; `Num y] -> if y = 0 then raise (RuntimeError "Divide by zero.")
                                      else `Num (x mod y)
                | _ -> arg_error op args)
      | Eq -> (match eval_all args with
               | [x; y] -> `Bool (x = y)
               | _ -> arg_error op args)
      | Neq -> (match eval_all args with
                | [x; y] -> `Bool (x <> y)
                | _ -> arg_error op args)
      | Lt -> (match eval_all args with
               | [`Num x; `Num y] -> `Bool (x < y)
               | _ -> arg_error op args)
      | Leq -> (match eval_all args with
                | [`Num x; `Num y] -> `Bool (x <= y)
                | _ -> arg_error op args)
      | Gt -> (match eval_all args with
               | [`Num x; `Num y] -> `Bool (x > y)
               | _ -> arg_error op args)
      | Geq -> (match eval_all args with
                | [`Num x; `Num y] -> `Bool (x >= y)
                | _ -> arg_error op args)
      | And -> (match eval_all args with
                | [`Bool x; `Bool y] -> `Bool (x && y)
                | _ -> arg_error op args)
      | Or -> (match eval_all args with
               | [`Bool x; `Bool y] -> `Bool (x || y)
               | _ -> arg_error op args)
      | Cons -> (match eval_all args with
                 | [x; `List (y, t)] -> `List (((value_to_const x) :: y), t)
                 | _ -> arg_error op args)
      | If -> (match args with
               | [ux; uy; uz] -> (match eval env ux with
                                  | `Bool x -> if x then eval env uy
                                               else eval env uz
                                  | _ -> arg_error op args)
               | _ -> arg_error op args)
      | Fold -> (match args with
                 | [ul; uf; ui] -> (match eval env ul with
                                    | `List ([], _) -> eval env ui
                                    | `List (x::xs, t) ->
                                       let x_expr = (x :> expr) in
                                       let xs_expr = ((`List (xs, t)) :> expr) in
                                       eval env (`Apply (uf, [`Op (Fold, [xs_expr; uf; ui]); x_expr]))
                                    | _ -> arg_error op args)
                 | _ -> arg_error op args)
      | Filter -> (match args with
                   | [ul; uf] ->
                      (match eval env ul with
                       | `List ([], t) -> `List ([], t)
                       | `List (x::xs, t) ->
                          let x_expr = (x :> expr) in
                          let xs_expr = ((`List (xs, t)) :> expr) in
                          eval env (`Op (If, [`Apply (uf, [x_expr]);
                                              `Op (Cons, [x_expr; `Op (Filter, [xs_expr; uf])]);
                                              `Op (Filter, [xs_expr; uf])]))
                       | _ -> arg_error op args)
                   | _ -> arg_error op args)
      | Map -> (match args with
                | [ul; uf] -> (match (eval env ul), (typeof_value (eval env uf)) with
                               | (`List (x, _)), (Arrow_t (_, ret_t)) ->
                                  let x' = List.map x ~f:(fun elem -> eval env (`Apply (uf, [(elem :> expr)]))
                                                                      |> value_to_const) in
                                  `List (x', ret_t)
                               | _ -> arg_error op args)
                | _ -> arg_error op args)
      | Foldl -> (match args with
                  | [ul; uf; ui] -> (match eval env ul with
                                     | `List ([], _) -> eval env ui
                                     | `List (x::xs, t) ->
                                        let x_expr = (x :> expr) in
                                        let xs_expr = ((`List (xs, t)) :> expr) in
                                        eval env (`Op (Foldl, [xs_expr; uf; `Apply (uf, [ui; x_expr]);]))
                                     | _ -> arg_error op args)
                  | _ -> arg_error op args))

(** Evaluate a "program," or a list of expressions. This creates an
eval context which contains bindings for each define in the
program. It then evaluates the last non-define expression and returns
the result. *)
let prog_eval prog =
  let env = prog |> List.fold_left ~init:(Ctx.empty ())
                                   ~f:(fun nv def ->
                                       match def with
                                       | `Define (id, ex) ->
                                          let env' = Ctx.bind nv id `Unit in
                                          Ctx.update env' id (eval env' ex);
                                          env'
                                       | _ -> nv) in
  match (prog
         |> List.rev_filter ~f:(fun e -> match e with
                                         | `Define _ -> false
                                         | _ -> true)
         |> List.hd) with
  | Some exp -> eval env exp
  | None -> `Unit
