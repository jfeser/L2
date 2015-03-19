open Core.Std
open Ast
open Util

(** Exceptions that can be thrown by the evaluation and type-checking functions. *)
exception RuntimeError of string

type value = [
  | `Num of int
  | `Bool of bool
  | `List of value list
  | `Tree of value Tree.t
  | `Closure of expr * (value Ctx.t)
  | `Unit
] with compare

let rec value_to_string v =
  let join = String.concat ~sep:" " in
  match v with
  | `Num x  -> Expr.to_string (`Num x)
  | `Bool x -> Expr.to_string (`Bool x)
  | `Tree x -> Tree.to_string x ~str:value_to_string
  | `List x -> "[" ^ (join (List.map x ~f:value_to_string)) ^ "]"
  | `Closure (e, _) -> Expr.to_string e
  | `Unit -> "unit"

(** Raise a bad argument error. *)
let arg_error op args =
  raise (RuntimeError
           (Printf.sprintf "Bad arguments to %s: (%s)."
              (Expr.Op.to_string op)
              (String.concat ~sep:" " (List.map ~f:Expr.to_string args))))

(** Raise a wrong # of arguments error. *)
let argn_error id = raise (RuntimeError ("Wrong # of arguments to " ^ id))

let stdlib =
  ["inf", `Num Int.max_value]
  @ ([
      "foldr", "(lambda (l f i) (if (= l []) i (f (foldr (cdr l) f i) (car l))))";
      "foldl", "(lambda (l f i) (if (= l []) i (foldl (cdr l) f (f i (car l)))))";
      "map", "(lambda (l f) (if (= l []) [] (cons (f (car l)) (map (cdr l) f))))";
      "filter", "(lambda (l f) (if (= l []) []
             (if (f (car l))
             (cons (car l) (filter (cdr l) f))
             (filter (cdr l) f))))";
      "mapt", "(lambda (t f)
           (if (= t {}) {}
           (tree (f (value t)) (map (children t) (lambda (c) (mapt c f))))))";
      "foldt", "(lambda (t f i)
            (if (= t {}) i
            (f (map (children t) (lambda (ct) (foldt ct f i)))
            (value t))))";
    ] |> List.map ~f:(fun (name, str) -> name, Util.parse_expr str))

let eval_ctx_of_alist =
  List.fold_left ~init:(Ctx.empty ())
    ~f:(fun ctx (name, lambda) ->
        let ctx' = Ctx.bind ctx name `Unit in
        let value = `Closure (lambda, ctx') in
        Ctx.update ctx' name value;
        Ctx.bind ctx name value)

let (stdlib_vctx: value Ctx.t) = eval_ctx_of_alist stdlib

(** Evaluate an expression in the provided context. *)
let eval ?recursion_limit:(limit = (-1)) ctx expr : value =
  let ctx' =
    Ctx.merge stdlib_vctx ctx ~f:(fun ~key:_ value ->
        match value with
        | `Both (_, v) | `Left v | `Right v -> Some v) in
  let rec ev ctx lim expr : value =
    if lim = 0
    then (
      printf "Exceeded recursion limit.\n";
      raise (RuntimeError (sprintf "Exceeded recursion limit: %s" (Expr.to_string expr)))
    )
    else
      let ev_all = List.map ~f:(ev ctx lim) in
      match expr with
      | `Num x  -> `Num x
      | `Bool x -> `Bool x
      | `List x -> `List (ev_all x)
      | `Tree x -> `Tree (Tree.map x ~f:(ev ctx lim))
      | `Id id  -> Ctx.lookup_exn ctx id
      | `Let (name, bound, body) ->
        let ctx' = Ctx.bind ctx name `Unit in
        Ctx.update ctx' name (ev ctx' lim bound);
        ev ctx' lim body
      | `Lambda _ as lambda -> `Closure (lambda, ctx)
      | `Apply (func, args) ->
        let func_error name args =
          raise @@ RuntimeError
            (sprintf "Bad arguments to %s: %s."
               name (String.concat ~sep:" " (List.map ~f:Expr.to_string args)))
        in
        (match func with
         | `Id ("sort" as name) -> (match ev_all args with
             | [`List l] ->
               let l' =
                 List.map l ~f:(fun e -> match e with
                     | `Num e' -> e'
                     | _ -> func_error name args)
                 |> List.sort ~cmp:compare_int
                 |> List.map ~f:(fun e -> `Num e)
               in `List l'
             | _ -> func_error name args)

         | `Id ("merge" as name) -> (match ev_all args with
             | [`List l1; `List l2] ->
               try
                 let l1', l2' =
                   List.map2_exn l1 l2 ~f:(fun e1 e2 -> match e1, e2 with
                       | `Num e1', `Num e2' -> (e1', e2')
                       | _ -> func_error name args)
                   |> List.unzip
                 in
                 `List (List.merge l1' l2' ~cmp:compare_int
                        |> List.map ~f:(fun e -> `Num e))
               with Invalid_argument _ -> func_error name args
             | _ -> func_error name args)

         | `Id ("dedup" as name) -> (match ev_all args with
             | [`List l] -> `List (List.dedup ~compare:compare_value l)
             | _ -> func_error name args)

         | `Id ("take" as name) -> (match ev_all args with
             | [`List l; `Num x] -> `List (List.take l x)
             | _ -> func_error name args)

         | `Id ("drop" as name) -> (match ev_all args with
             | [`List l; `Num x] -> `List (List.drop l x)
             | _ -> func_error name args)

         | `Id ("append" as name) -> (match ev_all args with
             | [`List l1; `List l2] -> `List (List.append l1 l2)
             | _ -> func_error name args)

         | `Id ("reverse" as name) -> (match ev_all args with
             | [`List l] -> `List (List.rev l)
             | _ -> func_error name args)

         | `Id ("intersperse" as name) -> (match ev_all args with
             | [x; `List l] -> `List (List.intersperse ~sep:x l)
             | _ -> func_error name args)

         | `Id ("concat" as name) -> (match ev_all args with
             | [`List ls] ->
               let ls' = List.map ls ~f:(fun l -> match l with
                   | `List l' -> l'
                   | _ -> func_error name args)
               in
               `List (List.concat ls')
             | _ -> func_error name args)

         | `Id ("zip" as name) -> (match ev_all args with
             | [`List l1; `List l2] ->
               try `List (List.map2_exn l1 l2 ~f:(fun x1 x2 -> `List [x1; x2]))
               with Invalid_argument _ -> func_error name args
                  | _ -> func_error name args)

         (* | `Id ("unzip" as name) -> (match ev_all args with *)
         (*     | [`List l] -> *)
         (*       let l1, l2 = List.fold_right l ~init:([], []) *)
         (*           ~f:(fun (l1, l2) x -> match x with *)
         (*               | `List [x1; x2] -> x1::l1, x2::l2 *)
         (*               | _ -> func_error name args) *)
         (*       in *)
         (*       `List [`List l1; `List l2] *)
         (*     | _ -> func_error name args) *)

         | _ -> (match ev ctx lim func with
             | `Closure (`Lambda (arg_names, body), enclosed_ctx) ->
               (match List.zip arg_names (ev_all args) with
                | Some bindings ->
                  let ctx' =
                    List.fold bindings ~init:(enclosed_ctx)
                      ~f:(fun ctx' (arg_name, value) -> Ctx.bind ctx' arg_name value)
                  in
                  ev ctx' (lim - 1) body
                | None -> argn_error @@ Expr.to_string body)
             | _ -> raise @@ RuntimeError (sprintf "Tried to apply a non-function: %s"
                                             (Expr.to_string expr))))

      | `Op (op, args) ->
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
             | [`Num x; `Num y] ->
               if y = 0 then raise (RuntimeError "Divide by zero.") else `Num (x / y)
             | _ -> arg_error op args)
         | Mod -> (match ev_all args with
             | [`Num x; `Num y] ->
               if y = 0 then raise (RuntimeError "Divide by zero.") else `Num (x mod y)
             | _ -> arg_error op args)
         | Eq -> (match ev_all args with
             | [x; y] -> (try `Bool (x = y) with Invalid_argument _ -> arg_error op args)
             | _ -> arg_error op args)
         | Neq -> (match ev_all args with
             | [x; y] -> (try `Bool (x <> y) with Invalid_argument _ -> arg_error op args)
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
         | RCons -> (match ev_all args with
             | [`List y; x] -> `List (x :: y)
             | _ -> arg_error op args)
         | Cons -> (match ev_all args with
             | [x; `List y] -> `List (x :: y)
             | _ -> arg_error op args)
         | Tree -> (match ev_all args with
             | [x; `List y] ->
               let (y': value Tree.t list) = List.map y ~f:(fun e -> match e with `Tree t -> t | _ -> arg_error op args) in
               `Tree (Tree.Node (x, y'))
             | _ -> arg_error op args)
         | Value -> (match ev_all args with
             | [`Tree (Tree.Node (x, _))] -> x
             | _ -> arg_error op args)
         | Children -> (match ev_all args with
             | [`Tree Tree.Empty] -> `List []
             | [`Tree (Tree.Node (_, x))] -> `List (List.map x ~f:(fun e -> `Tree e))
             | _ -> arg_error op args)
         | If -> (match args with
             | [ux; uy; uz] -> (match ev ctx lim ux with
                 | `Bool x -> if x then ev ctx lim uy
                   else ev ctx lim uz
                 | _ -> arg_error op args)
             | _ -> arg_error op args))
  in
  ev ctx' limit expr
