open Core.Std
open Printf
open Ast
open Util

exception TypeError of string

let fresh_free level = Var_t (ref (Free (Fresh.int (), level)))

let normalize typ =
  let count = ref (-1) in
  let fresh_name () = incr count; "t" ^ (Int.to_string !count) in
  let rec norm ctx typ = match typ with
    | Const_t _
    | Var_t {contents = Free _} -> typ
    | Var_t {contents = Link typ'} -> norm ctx typ'
    | Var_t {contents = Quant name} ->
       (match Ctx.lookup ctx name with
        | Some name' -> Var_t (ref (Quant name'))
        | None -> let name' = fresh_name () in
                  Ctx.update ctx name name'; Var_t (ref (Quant name')))
    | App_t (const, args) -> App_t (const, List.map args ~f:(norm ctx))
    | Arrow_t (args, ret) -> Arrow_t (List.map args ~f:(norm ctx), norm ctx ret)
  in
  norm (Ctx.empty ()) typ

let rec occurs id level typ = match typ with
  | Const_t _
  | Var_t {contents = Quant _} -> ()
  | Var_t ({contents = Free (id', level')} as typ') ->
     if id' = id
     then raise @@ TypeError (sprintf "Failed occurs check: t%d in %s" id (typ_to_string typ))
     else 
       (* The other type is being claimed by the let binding, if it is
       owned by a lower let. This prevents the free variable from
       being prematurely generalized. *)
       if level' > level
       then typ' := Free (id', level)
       else ()
  | Var_t {contents = Link typ'} -> occurs id level typ'
  | App_t (_, args) -> List.iter args ~f:(fun arg -> occurs id level arg)
  | Arrow_t (args, ret) -> List.iter args ~f:(fun arg -> occurs id level arg); occurs id level ret

(** The level is associated with the let expression that "owns" a
particular free type variable. When that let expression is completely
typed, its free type variables can be generalized. *)
let rec generalize level typ =
  match typ with
  | Var_t {contents = Free (id, level')} when level' > level ->
     Var_t (ref (Quant ("t" ^ (Int.to_string id))))
  | Var_t {contents = Link typ'} -> generalize level typ'
  | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(generalize level) args, generalize level ret)
  | App_t (const, args) -> App_t (const, List.map ~f:(generalize level) args)
  | Const_t _ | Var_t {contents = Quant _} | Var_t {contents = Free _} -> typ

(** Instantiating a type replaces all quantified type variables with
 fresh free type variables. *)
let instantiate level typ =
  let rec inst ctx typ =
    match typ with
    | Const_t _
    | Var_t {contents = Free _} -> typ
    | Var_t {contents = Quant name} ->
       (match Ctx.lookup ctx name with
        | Some typ' -> typ'
        | None -> let typ' = fresh_free level in
                  Ctx.update ctx name typ'; typ')
    | Var_t {contents = Link typ'} -> inst ctx typ'
    | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(inst ctx) args, inst ctx ret)
    | App_t (const, args) -> App_t (const, List.map ~f:(inst ctx) args)
  in
  inst (Ctx.empty ()) typ

let rec unify t1 t2 =
  let error () = raise @@ TypeError (sprintf "Failed to unify %s and %s."
                                             (typ_to_string t1)
                                             (typ_to_string t2))
  in
  if t1 = t2 then () else
    match t1, t2 with
    | Const_t t1', Const_t t2' when t1' = t2' -> ()
    | Var_t {contents = Link t1'}, t2'
    | t1', Var_t {contents = Link t2'} -> unify t1' t2'
    | Var_t {contents = Free (id1, _)}, Var_t {contents = Free (id2, _)} when id1 = id2 -> error ()
    | Var_t ({contents = Free (id, level)} as t'), t
    | t, Var_t ({contents = Free (id, level)} as t') -> occurs id level t; t' := Link t
    | Arrow_t (args1, ret1), Arrow_t (args2, ret2) ->
       (match List.zip args1 args2 with
        | Some args -> List.iter args ~f:(fun (a1, a2) -> unify a1 a2)
        | None -> error ());
       unify ret1 ret2
    | App_t (const1, args1), App_t (const2, args2) when const1 = const2 ->
       (match List.zip args1 args2 with
        | Some args -> List.iter args ~f:(fun (a1, a2) -> unify a1 a2)
        | None -> error ())
    | _ -> error ()

(* let to_string (sub: typ Sub.t) = *)
(*   Sub.to_alist sub *)
(*   |> List.map ~f:(fun (id, typ) -> (typ_to_string (Var_t (Free id))) ^ ": " ^ (typ_to_string typ)) *)
(*   |> String.concat ~sep:" " *)

let typ_of_expr = function
  | Num (_, t) 
  | Bool (_, t) 
  | List (_, t) 
  | Id (_, t) 
  | Lambda (_, t)
  | Apply (_, t) 
  | Op (_, t) 
  | Let (_, t) -> t

let rec typeof ctx level expr =
  let rec typeof_func num_args typ =
    match typ with
    | Arrow_t (args, ret) -> args, ret
    | Var_t {contents = Link typ} -> typeof_func num_args typ
    | Var_t ({contents = Free (_, level)} as typ) ->
        let args = List.range 0 num_args |> List.map ~f:(fun _ -> fresh_free level) in
        let ret = fresh_free level in
        typ := Link (Arrow_t (args, ret));
        args, ret
    | _ -> raise @@ TypeError "Not a function."
  in
  match expr with
  | `Num x -> Num (x, Const_t Num_t)
  | `Bool x -> Bool (x, Const_t Bool_t)
  | `List [] -> List ([], App_t ("list", [fresh_free level]))
  | `List elems ->
     List.fold_left elems
                    ~init:(typeof ctx level (`List []))
                    ~f:(fun texpr elem ->
                        match texpr with
                        | List (elems, App_t ("list", [typ])) ->
                           let elem' = typeof ctx level elem in
                           unify typ (typ_of_expr elem');
                           List (List.append elems [elem'], App_t ("list", [typ]))
                        | _ -> assert false)
  | `Id name -> Id (name, instantiate level (Ctx.lookup_exn ctx name))
  | `Lambda (args, body) ->
     (* Generate fresh type variables for each argument and bind them
        into the existing context. *)
     let ctx' = List.fold args
                          ~init:ctx
                          ~f:(fun ctx' arg -> Ctx.bind ctx' arg (fresh_free level)) in
     let arg_typs = List.map args ~f:(fun arg -> Ctx.lookup_exn ctx' arg) in
     let body' = typeof ctx' level body in
     Lambda ((args, body'), Arrow_t (arg_typs, typ_of_expr body'))
  | `Apply (func, args) ->
     let func' = typeof ctx level func in
     let args' = List.map args ~f:(typeof ctx level) in
     let arg_typs, ret_typ = typeof_func (List.length args) (typ_of_expr func') in
     (match List.zip arg_typs args' with
      | Some pairs -> List.iter pairs ~f:(fun (typ, arg') -> unify typ (typ_of_expr arg'))
      | None -> raise @@ TypeError "Wrong number of arguments.");
     Apply ((func', args'), ret_typ)
  | `Op (op, args) ->
     let args' = List.map args ~f:(typeof ctx level) in
     let arg_typs, ret_typ = typeof_func (List.length args) (instantiate level (Op.typ op)) in
     (match List.zip arg_typs args' with
      | Some pairs -> List.iter pairs ~f:(fun (typ, arg') -> unify typ (typ_of_expr arg'))
      | None -> raise @@ TypeError "Wrong number of arguments.");
     Op ((op, args'), ret_typ)
  | `Let (name, bound, body) ->
     let bound' = typeof ctx (level + 1) bound in
     let body' =
       let bound_typ = generalize level (typ_of_expr bound') in
       typeof (Ctx.bind ctx name bound_typ) level body in
     Let ((name, bound', body'), typ_of_expr body')

let stdlib_tctx = [
  "foldr", "(list[a], ((b, a) -> b), b) -> b";
  "foldl", "(list[a], ((b, a) -> b), b) -> b";
  "map", "(list[a], (a -> b)) -> list[b]";
  "filter", "(list[a], (a -> bool)) -> list[a]";
] |> List.map ~f:(fun (name, str) -> name, Util.parse_typ str) |> Ctx.of_alist_exn

let infer ctx expr =
  let ctx' = Ctx.merge stdlib_tctx ctx
                       ~f:(fun ~key:_ value ->
                           match value with
                           | `Both (_, v) | `Left v | `Right v -> Some v) in
  let expr' = typeof ctx' 0 expr in
  generalize (-1) (typ_of_expr expr')
