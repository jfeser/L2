open Core.Std
open Printf
open Ast
open Expr
open Util

type typed_id = id * typ
type typed_expr =
  | Num of int * typ
  | Bool of bool * typ
  | List of typed_expr list * typ
  | Tree of typed_expr Tree.t * typ
  | Id of id * typ
  | Let of (id * typed_expr * typed_expr) * typ
  | Lambda of (id list * typed_expr) * typ
  | Apply of (typed_expr * (typed_expr list)) * typ
  | Op of (Op.t * (typed_expr list)) * typ
  with compare, sexp

let rec map f texpr = match texpr with
  | Num (x, t) -> Num (x, f t)
  | Bool (x, t) -> Bool (x, f t) 
  | List (x, t) -> List (List.map x ~f:(map f), f t)
  | Tree (x, t) -> Tree (Tree.map x ~f:(map f), f t)
  | Id (x, t) -> Id (x, f t)
  | Lambda ((x, y), t) -> Lambda ((x, map f y), f t)
  | Apply ((x, y), t) -> Apply ((map f x, List.map y ~f:(map f)), f t)
  | Op ((x, y), t) -> Op ((x, List.map y ~f:(map f)), f t)
  | Let ((x, y, z), t) -> Let ((x, map f y, map f z), f t)

let rec expr_of_texpr = function
  | Num (x, _) -> `Num x
  | Bool (x, _) -> `Bool x 
  | Id (x, _) -> `Id x
  | List (x, _) -> `List (List.map x ~f:(expr_of_texpr))
  | Tree (x, _) -> `Tree (Tree.map x ~f:(expr_of_texpr))
  | Lambda ((x, y), _) -> `Lambda (x, expr_of_texpr y)
  | Apply ((x, y), _) -> `Apply (expr_of_texpr x, List.map y ~f:(expr_of_texpr))
  | Op ((x, y), _) -> `Op (x, List.map y ~f:(expr_of_texpr))
  | Let ((x, y, z), _) -> `Let (x, expr_of_texpr y, expr_of_texpr z)

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
     then raise @@ TypeError (sprintf "Failed occurs check: ft%d in %s" id (typ_to_string typ))
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
let rec generalize level typ = match typ with
  | Var_t {contents = Free (id, level')} when level' > level ->
     Var_t (ref (Quant ("t" ^ (Int.to_string id))))
  | Var_t {contents = Link typ'} -> generalize level typ'
  | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(generalize level) args, generalize level ret)
  | App_t (const, args) -> App_t (const, List.map ~f:(generalize level) args)
  | Const_t _ | Var_t {contents = Quant _} | Var_t {contents = Free _} -> typ

(** Instantiating a type replaces all quantified type variables with
fresh free type variables. *)
let instantiate ?ctx:(ctx = Ctx.empty ()) level typ =
  let rec inst ctx typ = match typ with
    | Const_t _
    | Var_t {contents = Free _} -> typ
    | Var_t {contents = Quant name} ->
       (match Ctx.lookup ctx name with
        | Some typ' -> typ'
        | None -> let typ' = fresh_free level in Ctx.update ctx name typ'; typ')
    | Var_t {contents = Link typ'} -> inst ctx typ'
    | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(inst ctx) args, inst ctx ret)
    | App_t (const, args) -> App_t (const, List.map ~f:(inst ctx) args)
  in
  inst ctx typ

let rec unify_exn t1 t2 =
  let error () = raise @@ TypeError (sprintf "Failed to unify %s and %s."
                                             (typ_to_string t1)
                                             (typ_to_string t2))
  in
  if t1 = t2 then () else
    match t1, t2 with
    | Const_t t1', Const_t t2' when t1' = t2' -> ()
    | Var_t {contents = Link t1'}, t2'
    | t1', Var_t {contents = Link t2'} -> unify_exn t1' t2'
    | Var_t {contents = Free (id1, _)}, Var_t {contents = Free (id2, _)} when id1 = id2 -> 
       raise (TypeError "Free variable occurred in both types.")
    | Var_t ({contents = Free (id, level)} as t'), t
    | t, Var_t ({contents = Free (id, level)} as t') -> occurs id level t; t' := Link t
    | Arrow_t (args1, ret1), Arrow_t (args2, ret2) ->
       (match List.zip args1 args2 with
        | Some args -> List.iter args ~f:(fun (a1, a2) -> unify_exn a1 a2)
        | None -> error ());
       unify_exn ret1 ret2
    | App_t (const1, args1), App_t (const2, args2) when const1 = const2 ->
       (match List.zip args1 args2 with
        | Some args -> List.iter args ~f:(fun (a1, a2) -> unify_exn a1 a2)
        | None -> error ())
    | _ -> error ()

let unify t1 t2 = try Some (unify_exn t1 t2; t1) with TypeError _ -> None
let is_unifiable t1 t2 = Option.is_some (unify (instantiate 0 t1) (instantiate 0 t2))

let typ_of_expr = function
  | Num (_, t) 
  | Bool (_, t) 
  | List (_, t) 
  | Tree (_, t)
  | Id (_, t) 
  | Lambda (_, t)
  | Apply (_, t) 
  | Op (_, t) 
  | Let (_, t) -> t

let rec typeof ctx level (expr: expr) : typed_expr =
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
  let rec typeof_tree t : typed_expr Tree.t * typ =
    let open Tree in
    match t with
    | Empty -> Empty, App_t ("tree", [fresh_free level])
    | Node (x, y) ->
       let x' = typeof ctx level x in
       let typ = App_t ("tree", [typ_of_expr x']) in
       let y', y_typs = List.map y ~f:typeof_tree |> List.unzip in
       List.iter y_typs ~f:(unify_exn typ); Node (x', y'), typ
  in
  match expr with
  | `Num x -> Num (x, Const_t Num_t)
  | `Bool x -> Bool (x, Const_t Bool_t)
  | `Tree x -> let x', typ = typeof_tree x in Tree (x', typ)
  | `List [] -> List ([], App_t ("list", [fresh_free level]))
  | `List elems ->
     List.fold_left elems
                    ~init:(typeof ctx level (`List []))
                    ~f:(fun texpr elem ->
                        match texpr with
                        | List (elems, App_t ("list", [typ])) ->
                           let elem' = typeof ctx level elem in
                           unify_exn typ (typ_of_expr elem');
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
      | Some pairs -> List.iter pairs ~f:(fun (typ, arg') -> unify_exn typ (typ_of_expr arg'))
      | None -> raise @@ TypeError "Wrong number of arguments.");
     Apply ((func', args'), ret_typ)
  | `Op (op, args) ->
     let args' = List.map args ~f:(typeof ctx level) in
     let arg_typs, ret_typ = typeof_func (List.length args) (instantiate level (Op.typ op)) in
     (match List.zip arg_typs args' with
      | Some pairs -> List.iter pairs ~f:(fun (typ, arg') -> unify_exn typ (typ_of_expr arg'))
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
  "foldt", "(tree[a], ((list[b], a) -> b), b) -> b";
  "map", "(list[a], (a -> b)) -> list[b]";
  "mapt", "(tree[a], (a -> b)) -> tree[b]";
  "filter", "(list[a], (a -> bool)) -> list[a]";
  "inf", "num";
] |> List.map ~f:(fun (name, str) -> name, Util.parse_typ str) |> Ctx.of_alist_exn

(** Infer the type of an expression in context. Returns an expression
tree annotated with types. *)
let infer ctx (expr: expr) : typed_expr =
  let ctx' = Ctx.merge stdlib_tctx ctx
                       ~f:(fun ~key:_ value ->
                           match value with
                           | `Both (_, v) | `Left v | `Right v -> Some v) in
  let expr' = typeof ctx' 0 expr in
  map (generalize (-1)) expr'
