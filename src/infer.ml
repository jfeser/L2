open Core.Std
open Printf
open Ast
open Expr
open Util

exception TypeError of string

(* A substitution is a mapping from free type variables to types. It
can be applied to a type to fill in some or all of its free type
variables. *)
module IntMap = Map.Make(Int)
type subst = typ IntMap.t

let rec apply (s: subst) (t: typ) : typ =
  match t with
    | Const_t _ | Var_t {contents = Quant _} -> t
    | Var_t {contents = Free (id, _)} ->
      (match IntMap.find s id with
       | Some t' -> t'
       | None -> t)
    | Var_t {contents = Link t} -> apply s t
    | App_t (name, args) -> App_t (name, List.map ~f:(apply s) args)
    | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(apply s) args, apply s ret)

let compose (s1: subst) (s2: subst) : subst =
  let merge outer inner =
    IntMap.fold ~f:(fun ~key:name ~data:typ m ->
                    IntMap.add ~key:name ~data:typ m) ~init:outer inner
  in merge s1 (IntMap.map ~f:(fun t -> apply s1 t) s2)

let rec unifier (t1: typ) (t2: typ) : subst =
  let error msg =
    let finalMsg =
      if msg = ""
      then sprintf "Failed to unify %s and %s." (typ_to_string t1) (typ_to_string t2)
      else sprintf "Failed to unify %s and %s: %s" (typ_to_string t1) (typ_to_string t2) msg
    in raise @@ TypeError finalMsg
  in

  (* Check whether the free variable 'id' occurs in type 'typ'. If it
  does, we cannot substitute 'typ' for 'id' due to infinite
  recursion. *)
  let rec occurs (id: int) (typ: typ) : bool =
    match typ with
      | Const_t _ | Var_t {contents = Quant _} -> false
      | Var_t ({contents = Free (id', _)}) -> id = id'
      | Var_t {contents = Link t} -> occurs id t
      | App_t (_, args) -> List.exists args ~f:(occurs id)
      | Arrow_t (args, ret) -> List.exists args ~f:(occurs id) || occurs id ret
  in

  if t1 = t2 then IntMap.empty else
    match t1, t2 with
      | Var_t {contents = Link x}, y
      | x, Var_t {contents = Link y} -> unifier x y
      | Var_t {contents = Free (x, _)}, Var_t {contents = Free (y, _)} when x = y ->
        error (sprintf "Free variable %d occurred in %s and %s."
                       x (typ_to_string t1) (typ_to_string t2))
      | t, Var_t ({contents = Free (id, _)}) | Var_t ({contents = Free (id, _)}), t ->
        if occurs id t
        then error (sprintf "Free variable %d occurs in %s." id (typ_to_string t))
        else IntMap.singleton id t
      | Arrow_t (args1, ret1), Arrow_t (args2, ret2) ->
        let s1 = List.fold2_exn ~f:(fun s a1 a2 -> compose s (unifier a1 a2)) ~init:IntMap.empty args1 args2 in
        let s2 = unifier ret1 ret2 in
        compose s1 s2
      | App_t (const1, args1), App_t (const2, args2) when const1 = const2 ->
        List.fold2_exn ~f:(fun s a1 a2 -> compose s (unifier a1 a2)) ~init:IntMap.empty args1 args2
      | _ -> error ""

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

let occurs id level typ =
  let error msg =
    raise @@ TypeError (sprintf "Failed occurs check in %s: %s"
                          (typ_to_string typ) msg)
  in
  let rec occurs' id level typ =
    match typ with
    | Const_t _
    | Var_t {contents = Quant _} -> ()
    | Var_t ({contents = Free (id', level')} as typ') ->
      if id' = id
      then error (sprintf "ft%d occurred twice" id)
      else
        (* The other type is being claimed by the let binding, if it is
           owned by a lower let. This prevents the free variable from
           being prematurely generalized. *)
      if level' > level
      then typ' := Free (id', level)
      else ()
    | Var_t {contents = Link typ'} -> occurs' id level typ'
    | App_t (_, args) -> List.iter args ~f:(fun arg -> occurs' id level arg)
    | Arrow_t (args, ret) ->
      List.iter args ~f:(fun arg -> occurs' id level arg); occurs' id level ret
  in occurs' id level typ

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

let typeof (ctx: typ Ctx.t) (level: level) (expr: expr) : typed_expr =
  let error msg =
    raise @@ TypeError (sprintf "In %s: %s" (Expr.to_string expr) msg)
  in

  let rec typeof' ctx level expr =
    let rec typeof_func num_args typ =
      match typ with
      | Arrow_t (args, ret) -> args, ret
      | Var_t {contents = Link typ} -> typeof_func num_args typ
      | Var_t ({contents = Free (_, level)} as typ) ->
        let args = List.range 0 num_args |> List.map ~f:(fun _ -> fresh_free level) in
        let ret = fresh_free level in
        typ := Link (Arrow_t (args, ret));
        args, ret
      | _ -> error "Not a function."
    in
    let rec typeof_tree t : typed_expr Tree.t * typ =
      let open Tree in
      match t with
      | Empty -> Empty, App_t ("tree", [fresh_free level])
      | Node (x, y) ->
        let x' = typeof' ctx level x in
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
        ~init:(typeof' ctx level (`List []))
        ~f:(fun texpr elem ->
            match texpr with
            | List (elems, App_t ("list", [typ])) ->
              let elem' = typeof' ctx level elem in
              unify_exn typ (typ_of_expr elem');
              List (List.append elems [elem'], App_t ("list", [typ]))
            | _ -> assert false)
    | `Id name ->
      (match Ctx.lookup ctx name with
       | Some t -> Id (name, instantiate level t)
       | None -> error (sprintf "%s is unbound in context %s."
                          name (Ctx.to_string ctx typ_to_string)))
    | `Lambda (args, body) ->
      (* Generate fresh type variables for each argument and bind them
         into the existing context. *)
      let ctx' = List.fold args
          ~init:ctx
          ~f:(fun ctx' arg -> Ctx.bind ctx' arg (fresh_free level)) in
      let arg_typs = List.map args ~f:(fun arg -> Ctx.lookup_exn ctx' arg) in
      let body' = typeof' ctx' level body in
      Lambda ((args, body'), Arrow_t (arg_typs, typ_of_expr body'))
    | `Apply (func, args) ->
      let func' = typeof' ctx level func in
      let args' = List.map args ~f:(typeof' ctx level) in
      let arg_typs, ret_typ = typeof_func (List.length args) (typ_of_expr func') in
      (match List.zip arg_typs args' with
       | Some pairs -> List.iter pairs ~f:(fun (typ, arg') -> unify_exn typ (typ_of_expr arg'))
       | None -> error "Wrong number of arguments.");
      Apply ((func', args'), ret_typ)
    | `Op (op, args) ->
      let args' = List.map args ~f:(typeof' ctx level) in
      let arg_typs, ret_typ = typeof_func (List.length args) (instantiate level (Op.typ op)) in
      (match List.zip arg_typs args' with
       | Some pairs -> List.iter pairs ~f:(fun (typ, arg') -> unify_exn typ (typ_of_expr arg'))
       | None -> error "Wrong number of arguments.");
      Op ((op, args'), ret_typ)
    | `Let (name, bound, body) ->
      let bound' = typeof' ctx (level + 1) bound in
      let body' =
        let bound_typ = generalize level (typ_of_expr bound') in
        typeof' (Ctx.bind ctx name bound_typ) level body in
      Let ((name, bound', body'), typ_of_expr body')
  in typeof' ctx level expr

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

(** Parse a string and return a typed expression. *)
let typed_expr_of_string (s: string) : typed_expr =
  let expr = Util.parse_expr s in
  infer (Ctx.empty ()) expr

(** Return a list of names that are free in the given expression,
    along with their types. *)
module IdTypeSet = Set.Make(struct
    type t = id * typ with compare, sexp
  end)

let stdlib_names = Ctx.keys stdlib_tctx |> String.Set.of_list
let free ?(bound=stdlib_names) (e: typed_expr) : (id * typ) list =
  let rec f bound e : IdTypeSet.t = match e with
    | Num _ | Bool _ -> IdTypeSet.empty
    | Id (x, t) -> if String.Set.mem bound x then IdTypeSet.empty
      else IdTypeSet.singleton (x, t)
    | List (x, _) -> List.map ~f:(f bound) x |> IdTypeSet.union_list
    | Tree (x, _) ->
      Tree.flatten x |> List.map ~f:(f bound) |> IdTypeSet.union_list
    | Lambda ((args, body), _) ->
      f (String.Set.union bound (String.Set.of_list args)) body
    | Apply ((func, args), _) ->
      IdTypeSet.union_list ((f bound func)::(List.map ~f:(f bound) args))
    | Op ((_, args), _) -> List.map ~f:(f bound) args |> IdTypeSet.union_list
    | Let ((x, e1, e2), _) ->
      let bound' = String.Set.add bound x in
      IdTypeSet.union (f bound' e1) (f bound' e2)
  in f bound e |> IdTypeSet.to_list

(** Check whether expression e contains expression x. *)
(* let contains (x: typed_expr) (e: typed_expr) : bool = match e with *)
(*   | Num _ | Bool _ | Id _ -> e = x *)
(*   | List (l, _) -> List.find ~f:(contains x) l *)
(*   | Tree (l, _) -> Tree.flatten x |> List.find ~f:(contains x) *)
(*   | Lambda ((_, body), _) -> contains x body *)
(*   | Apply ((func, args), _) -> *)
(*     contains x args || List.find ~f:(contains x) args *)
(*   | Op ((_, args), _) -> List.find ~f:(contains x) args *)
(*   | Let ((_, e1, e2), _) -> contains x e1 || contains x e2 *)

(* let contains_name (x: typed_exper) (n: string) : bool = match e with *)
(*   | Num _ | Bool _ -> false *)
(*   | Id n' -> n' = n *)
(*   | List (l, _) -> List.find ~f:(contains_name x) l *)
(*   | Tree (l, _) -> Tree.flatten x |> List.find ~f:(contains_name x) *)
(*   | Lambda ((_, body), _) -> contains_name x body *)
(*   | Apply ((func, args), _) -> *)
(*     contains_name x args || List.find ~f:(contains_name x) args *)
(*   | Op ((_, args), _) -> List.find ~f:(contains_name x) args *)
(*   | Let ((_, e1, e2), _) -> contains_name x e1 || contains_name x e2 *)

let rec type_nesting_depth (t: typ) : int =
  match t with
  | Const_t _ | Var_t _ -> 1
  | App_t (_, args) -> 1 + (max (List.map ~f:type_nesting_depth args))
  | Arrow_t (args, ret) ->
    let args_max = (max (List.map ~f:type_nesting_depth args)) in
    let ret_depth = type_nesting_depth ret in
    if args_max > ret_depth then args_max else ret_depth
