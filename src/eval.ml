open Core.Std
open Ast

(** Exceptions that can be thrown by the evaluation and type-checking functions. *)
exception RuntimeError of string

type value = [ `Num of int
             | `Bool of bool
             | `List of value list
             | `Closure of expr * (value Ctx.t)
             | `Unit ]

let rec value_to_string = function
  | `Num x  -> expr_to_string (`Num x)
  | `Bool x -> expr_to_string (`Bool x)
  | `List x -> "[" ^ (String.concat ~sep:" " (List.map x ~f:value_to_string)) ^ "]"
  | `Closure (e, _) -> expr_to_string e
  | `Unit -> "unit"

(** Raise a bad argument error. *)
let arg_error op args =
  raise (RuntimeError (Printf.sprintf "Bad arguments to %s %s."
                                      (Ast.Op.to_string op)
                                      (sexp "(" (List.map ~f:expr_to_string args) ")")))

(** Raise a wrong # of arguments error. *)
let argn_error id = raise (RuntimeError ("Wrong # of arguments to " ^ id))

let stdlib = [
  "foldr", "(lambda (l f i) (if (= l []) i (f (foldr (cdr l) f i) (car l))))";
  "foldl", "(lambda (l f i) (if (= l []) i (foldl (cdr l) f (f i (car l)))))";
  "map", "(lambda (l f) (if (= l []) [] (cons (f (car l)) (map (cdr l) f))))";
  "filter", "(lambda (l f) (if (= l []) []
             (if (f (car l))
             (cons (car l) (filter (cdr l) f))
             (filter (cdr l) f))))";
] |> List.map ~f:(fun (name, str) -> name, Util.parse_expr str)

let (stdlib_vctx: value Ctx.t) =
  List.fold stdlib 
            ~init:(Ctx.empty ())
            ~f:(fun ctx (name, lambda) ->
                let ctx' = Ctx.bind (Ctx.empty ()) name `Unit in
                let value = `Closure (lambda, ctx') in
                Ctx.update ctx' name value;
                Ctx.bind ctx name value)

(** Evaluate an expression in the provided context. *)
let eval ctx expr =
  let ctx' =
    Ctx.merge stdlib_vctx ctx ~f:(fun ~key:_ value ->
                                  match value with
                                  | `Both (_, v) | `Left v | `Right v -> Some v) in
  let rec ev ctx expr =
    let ev_all = List.map ~f:(ev ctx) in
    match expr with
    | `Num x  -> `Num x
    | `Bool x -> `Bool x
    | `List x -> `List (ev_all x)
    | `Id id  -> Ctx.lookup_exn ctx id
    | `Let (name, bound, body) -> 
       let ctx' = Ctx.bind ctx name `Unit in
       Ctx.update ctx' name (ev ctx' bound);
       ev ctx' body
    | `Lambda _ as lambda -> `Closure (lambda, ctx)
    | `Apply (func, args) ->
       (match ev ctx func with
        | `Closure (`Lambda (arg_names, body), enclosed_ctx) ->
           (match List.zip arg_names (ev_all args) with
            | Some bindings ->
               let ctx' = List.fold bindings
                                    ~init:(enclosed_ctx)
                                    ~f:(fun ctx' (arg_name, value) -> Ctx.bind ctx' arg_name value) in
               ev ctx' body
            | None -> argn_error @@ expr_to_string body)
        | _ -> 
           print_endline (Ctx.to_string ctx value_to_string);
           raise @@ RuntimeError (sprintf "Tried to apply a non-function: %s"
                                          (expr_to_string expr)))
    | `Op (op, args) ->
       let open Op in
       (match op with
        | Not -> (match ev_all args with
                  | [`Bool x] -> `Bool (not x)
                  | _ -> arg_error op args)
        | Car -> (match ev_all args with
                  | [`List (x::_)] -> x
                  | _ -> arg_error op args)
        | Cdr -> (match ev_all args with
                  | [`List (_::xs)] -> `List xs
                  | _ -> arg_error op args)
        | Plus -> (match ev_all args with
                   | [`Num x; `Num y] -> `Num (x + y)
                   | _ -> arg_error op args)
        | Minus -> (match ev_all args with
                    | [`Num x; `Num y] -> `Num (x - y)
                    | _ -> arg_error op args)
        | Mul -> (match ev_all args with
                  | [`Num x; `Num y] -> `Num (x * y)
                  | _ -> arg_error op args)
        | Div -> (match ev_all args with
                  | [`Num x; `Num y] -> if y = 0 then raise (RuntimeError "Divide by zero.")
                                        else `Num (x / y)
                  | _ -> arg_error op args)
        | Mod -> (match ev_all args with
                  | [`Num x; `Num y] -> if y = 0 then raise (RuntimeError "Divide by zero.")
                                        else `Num (x mod y)
                  | _ -> arg_error op args)
        | Eq -> (match ev_all args with
                 | [x; y] -> `Bool (x = y)
                 | _ -> arg_error op args)
        | Neq -> (match ev_all args with
                  | [x; y] -> `Bool (x <> y)
                  | _ -> arg_error op args)
        | Lt -> (match ev_all args with
                 | [`Num x; `Num y] -> `Bool (x < y)
                 | _ -> arg_error op args)
        | Leq -> (match ev_all args with
                  | [`Num x; `Num y] -> `Bool (x <= y)
                  | _ -> arg_error op args)
        | Gt -> (match ev_all args with
                 | [`Num x; `Num y] -> `Bool (x > y)
                 | _ -> arg_error op args)
        | Geq -> (match ev_all args with
                  | [`Num x; `Num y] -> `Bool (x >= y)
                  | _ -> arg_error op args)
        | And -> (match ev_all args with
                  | [`Bool x; `Bool y] -> `Bool (x && y)
                  | _ -> arg_error op args)
        | Or -> (match ev_all args with
                 | [`Bool x; `Bool y] -> `Bool (x || y)
                 | _ -> arg_error op args)
        | Cons -> (match ev_all args with
                   | [x; `List y] -> `List (x :: y)
                   | _ -> arg_error op args)
        | If -> (match args with
                 | [ux; uy; uz] -> (match ev ctx ux with
                                    | `Bool x -> if x then ev ctx uy
                                                 else ev ctx uz
                                    | _ -> arg_error op args)
                 | _ -> arg_error op args))
  in
  ev ctx' expr
