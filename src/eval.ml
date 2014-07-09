open Core.Std
open Ast

(** Exceptions that can be thrown by the evaluation and typechecking
functions. *)
exception RuntimeError of string
exception TypeError of string

(** Raise an unbound variable error. *)
let unbound_error id = raise (RuntimeError ("Unbound variable " ^ id))

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

(** Look up an id in the provided context. Works for type and eval
contexts. *)
let lookup id ctx =
  match String.Map.find !ctx id with
  | Some v -> v
  | None -> unbound_error id

(** Bind a type or value to an id, returning a new context. *)
let bind ctx ~key:k ~data:v = ref (String.Map.add !ctx ~key:k ~data:v)

(** Bind a type or value to an id, updating the context in place. *)
let update ctx ~key:k ~data:v = ctx := String.Map.add !ctx ~key:k ~data:v

(** Create an empty type or eval context. The type system complains
unless these are separate functions. *)
let empty_type_ctx = fun () -> ref String.Map.empty
let empty_eval_ctx = fun () -> ref String.Map.empty

(** Evaluate an expression in the provided context. *)
let rec eval (env: eval_ctx) expr =
  let eval_all l = List.map l ~f:(eval env) in
  match expr with
  | `Id id               -> lookup id env
  | `Num x               -> `Num x
  | `Bool x              -> `Bool x
  | `Nil                 -> `Nil
  | `List x              -> (match x with | [] -> `Nil | a  -> `List (eval_all a))
  | `Let (id, v, e) -> let env' = bind env ~key:id ~data:`Unit in
                       update env' ~key:id ~data:(eval env' v);
                       eval env' e
  | `Define _ ->
     raise (RuntimeError "Define is not allowed in eval (use eval_prog).")
  | `Lambda (args, e) -> `Closure (`Lambda (args, e), env)
  | `Apply (func, args) ->
     (match eval env func with
      | `Closure (`Lambda (arg_names, e), enclosed_env) ->
         (match List.zip arg_names (eval_all args) with
          | Some bindings ->
             let new_env = List.fold_left bindings ~init:(enclosed_env)
                                          ~f:(fun nv ((id, _), v) ->
                                              bind nv ~key:id ~data:v) in
             eval new_env e
          | None -> argn_error @@ expr_to_string e)
      | _ -> raise (RuntimeError "Tried to apply a non-function."))
  | `Op (op, args) ->
     (match op with
      | Not -> (match eval_all args with 
                | [`Bool x] -> `Bool (not x)
                | _ -> arg_error op args)
      | Car -> (match eval_all args with
                | [`List l] -> (match List.hd l with
                                | Some x -> x
                                | None -> arg_error op args)
                | _ -> arg_error op args)
      | Cdr -> (match eval_all args with
                | [`List l] -> (match List.tl l with
                                | Some x -> (match x with [] -> `Nil | a -> `List a)
                                | None -> arg_error op args)
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
                 | [x; `Nil] -> `List [x]
                 | [x; `List y] -> `List (x :: y)
                 | _ -> arg_error op args)
      | If -> (match args with
               | [ux; uy; uz] -> (match eval env ux with
                                  | `Bool x -> if x then eval env uy
                                               else eval env uz
                                  | _ -> arg_error op args)
               | _ -> arg_error op args)
      | Fold -> (match args with
                 | [l; f; i] ->
                    eval env
                         (`Op (If, [`Op (Eq, [`Nil; l]); i;
                                    `Apply (f, [`Op (Fold, [`Op (Cdr, [l]); f; i]); 
                                                `Op (Car, [l])])]))
                 | _ -> arg_error op args)
      | Filter -> (match args with
                   | [l; f] -> 
                      eval env (`Op (If, [`Op (Eq, [`Nil; l]); 
                                          `Nil;
                                          `Op (If, [`Apply (f, [`Op (Car, [l])]);
                                                    `Op (Cons, [`Op (Car, [l]);
                                                                `Op (Filter, [`Op (Cdr, [l]); f])]);
                                                    `Op (Filter, [`Op (Cdr, [l]); f])])]))
                                                      
                   | _ -> arg_error op args)
      | Foldl -> (match args with
                  | [l; f; i] ->
                     eval env 
                          (`Op (If, [`Op (Eq, [`Nil; l]); 
                                     i; 
                                     `Op (Foldl, 
                                          [`Op (Cdr, [l]);
                                           f; 
                                           `Apply (f, [i; `Op (Car, [l])]);])]))
                  | _ -> arg_error op args)
     )
;;

(** Evaluate a "program," or a list of expressions. This creates an
eval context which contains bindings for each define in the
program. It then evaluates the last non-define expression and returns
the result. *)
let prog_eval prog =
  let env = prog |> List.fold_left ~init:(empty_eval_ctx ())
                                   ~f:(fun nv def ->
                                       match def with
                                       | `Define (id, ex) ->
                                          let env' = bind nv ~key:id ~data:`Unit in
                                          update env' ~key:id ~data:(eval env' ex);
                                          env'
                                       | _ -> nv) in
  match (prog
         |> List.rev_filter ~f:(fun e -> match e with 
                                         | `Define _ -> false
                                         | _ -> true)
         |> List.hd) with
  | Some exp -> eval env exp
  | None -> `Nil
;;
  
(** Get the type of an expression given a type context. *)
let rec typeof_expr (ctx: type_ctx) (expr: expr) : typ =
  let typeof_all es = List.map ~f:(typeof_expr ctx) es in
  match expr with
  | `Num _ -> Num_t
  | `Bool _ -> Bool_t
  | `Nil -> Nil_t
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
                 | [t; Nil_t] -> List_t t
                 | [t1; List_t t2] -> if type_equal t1 t2 then List_t t1
                                      else type_error op args
                 | _ -> type_error op args)
      | If -> (match args with
               | [Bool_t; t1; t2] ->
                  if type_equal t1 t2 then t1
                  else raise @@ TypeError "If branches have different types."
               | _ -> type_error op args)
      | Fold 
      | Foldl -> (match args with
                  | [Nil_t; Arrow_t ([at1; _], at2); at3] ->
                     if Util.all_equal ~eq:type_equal [at1; at2; at3]
                     then at2 else type_error op args
                  | [List_t et2; Arrow_t ([at1; et1], at2); at3] ->
                     if (Util.all_equal ~eq:type_equal [at1; at2; at3]) && (type_equal et1 et2)
                     then at2 else type_error op args
                  | _ -> type_error op args)
      | Filter -> (match args with
                   | [Nil_t; Arrow_t ([_], Bool_t)] -> Nil_t
                   | [List_t et1; Arrow_t ([et2], Bool_t)] -> 
                      if type_equal et1 et2 then List_t et1 else type_error op args
                   | _ -> type_error op args))
  | `Id name -> lookup name ctx
  | `Let (name, e1, e2) ->
     let ctx' = bind ctx ~key:name ~data:(typeof_expr ctx e1) in
     typeof_expr ctx' e2
  | `Define _ -> Unit_t
  | `List l ->
     (match typeof_all l with
      | [] -> Nil_t
      | x::xs -> if List.for_all ~f:(type_equal x) xs then List_t x
                 else raise @@ TypeError "List contains multiple types.")
  | `Lambda (args, e) ->
     let ctx' = List.fold_left ~f:(fun c (n, t) -> bind c ~key:n ~data:t)
                               ~init:ctx args in
     typeof_expr ctx' e
  | `Apply (e, args) -> 
     (match typeof_expr ctx e with
      | Arrow_t (its, ot) -> 
         if List.equal its (typeof_all args) ~equal:type_equal then ot
         else raise @@ RuntimeError ("Bad argument to " ^ (expr_to_string e))
      | _ -> raise @@ RuntimeError "Tried to apply non-lambda.")

(** Get the type of a value. No type context is necessary, since ids
are not values. *)
let rec typeof_value (value: value) : typ =
  match value with
  | `Num _ -> Num_t
  | `Bool _ -> Bool_t
  | `List l -> 
     (match List.map ~f:typeof_value l with
      | [] -> Nil_t
      | [a] -> (List_t a)
      | a::b -> if List.for_all ~f:(type_equal a) b
                then (List_t a) 
                else raise @@ RuntimeError "List has inconsistent type.")
  | `Nil -> Nil_t
  | `Unit -> Unit_t
  | `Closure _ -> raise @@ RuntimeError "Closures not permitted in examples."

let rec specialize t1 t2 = 
  let error a b = raise @@ TypeError (Printf.sprintf "No specialization for %s %s."
                                                     (typ_to_string a)
                                                     (typ_to_string b)) in
  match t1 with
  | Nil_t -> (match t2 with
              | Nil_t -> t1
              | List_t _ -> t2
              | _ -> error t1 t2)
  | List_t ct1 -> (match t2 with
                   | Nil_t -> t1
                   | List_t ct2 -> List_t (specialize ct1 ct2)
                   | _ -> error t1 t2)
  | Arrow_t (its1, ot1) -> 
     (match t2 with
      | Arrow_t (its2, ot2) -> 
         Arrow_t (List.map2_exn ~f:specialize its1 its2, specialize ot1 ot2)
      | _ -> error t1 t2)
  | _ -> if t1 = t2 then t1 else error t1 t2

let specialize_all = function
  | [] -> raise @@ TypeError "No types to specialize."
  | x::xs -> List.fold_left xs ~f:specialize ~init:x
