open Core.Std
open Printf

open Ast
open Collections
open Expr
open Util

exception TypeError of Error.t

let total_infer_time = ref (Time.Span.of_float 0.0)

let unify_error ?msg (t1: typ) (t2: typ) =
  raise @@ TypeError (Error.of_thunk (fun () -> match msg with
      | Some msg ->
        sprintf "Failed to unify %s and %s: %s"
          (typ_to_string t1) (typ_to_string t2) (Info.to_string_hum msg)
      | None ->
        sprintf "Failed to unify %s and %s."
          (typ_to_string t1) (typ_to_string t2)))
    
module TypedExpr = struct
  type t =
    | Num of int * Type.t
    | Bool of bool * Type.t
    | List of t list * Type.t
    | Tree of t Tree.t * Type.t
    | Id of id * Type.t
    | Let of (id * t * t) * Type.t
    | Lambda of (id list * t) * Type.t
    | Apply of (t * (t list)) * Type.t
    | Op of (Op.t * (t list)) * Type.t
  with compare, sexp, variants

  let normalize (expr: t) : t =
    let count = ref (-1) in
    let fresh_name () =
      let n = incr count; !count in
      let prefix = Char.of_int_exn ((n mod 26) + 97) in
      let suffix = if n >= 26 then Int.to_string ((n - 26) mod 26) else "" in
      Printf.sprintf "%c%s" prefix suffix
    in
    let rec norm ctx e =
      let norm_all = List.map ~f:(norm ctx) in
      match e with
      | Num _ | Bool _ -> e
      | Id (x, t) ->
        (match Ctx.lookup ctx x with
         | Some x' -> Id (x', t)
         | None -> e)
      | List (x, t) -> List (norm_all x, t)
      | Tree (x, t) -> Tree (Tree.map x ~f:(norm ctx), t)
      | Op ((op, args), t) -> Op ((op, norm_all args), t)
      | Apply ((func, args), t) -> Apply ((norm ctx func, norm_all args), t)
      | Let ((name, x, y), t) ->
        let name' = fresh_name () in
        let ctx' = Ctx.bind ctx name name' in
        Let ((name', norm ctx' x, norm ctx' y), t)
      | Lambda ((args, body), t) ->
        let ctx', args' =
          List.fold_right args
            ~init:(ctx, [])
            ~f:(fun arg (ctx', args') ->
                let arg' = fresh_name () in
                Ctx.bind ctx' arg arg', arg'::args')
        in Lambda ((args', norm ctx' body), t)
    in norm (Ctx.empty ()) expr

  let rec map ~f (e: t) : t = match e with
    | Num (x, t) -> Num (x, f t)
    | Bool (x, t) -> Bool (x, f t)
    | List (x, t) -> List (List.map x ~f:(map ~f), f t)
    | Tree (x, t) -> Tree (Tree.map x ~f:(map ~f), f t)
    | Id (x, t) -> Id (x, f t)
    | Lambda ((x, y), t) -> Lambda ((x, map ~f y), f t)
    | Apply ((x, y), t) -> Apply ((map ~f x, List.map y ~f:(map ~f)), f t)
    | Op ((x, y), t) -> Op ((x, List.map y ~f:(map ~f)), f t)
    | Let ((x, y, z), t) -> Let ((x, map ~f y, map ~f z), f t)

  (** Strip the type annotations from a typed expression. *)
  let rec to_expr (e: t) : expr = match e with
    | Num (x, _) -> `Num x
    | Bool (x, _) -> `Bool x
    | Id (x, _) -> `Id x
    | List (x, _) -> `List (List.map x ~f:(to_expr))
    | Tree (x, _) -> `Tree (Tree.map x ~f:(to_expr))
    | Lambda ((x, y), _) -> `Lambda (x, to_expr y)
    | Apply ((x, y), _) -> `Apply (to_expr x, List.map y ~f:(to_expr))
    | Op ((x, y), _) -> `Op (x, List.map y ~f:(to_expr))
    | Let ((x, y, z), _) -> `Let (x, to_expr y, to_expr z)

  (** Get the type annotation of the root of a typed expression. *)
  let to_type = function
    | Num (_, t)
    | Bool (_, t)
    | List (_, t)
    | Tree (_, t)
    | Id (_, t)
    | Lambda (_, t)
    | Apply (_, t)
    | Op (_, t)
    | Let (_, t) -> t

  (** Convert a typed expression to a string. *)
  let to_string (e: t) : string = Expr.to_string (to_expr e)
end

module TypedExprMap = Core.Std.Map.Make(TypedExpr)

(** A unifier is a mapping from free type variables to types. It
    can be applied to a type to fill in some or all of its free type
    variables. *)
module Unifier = struct
  module IntMap = Core.Std.Map.Make(Int)
  type t = typ IntMap.t

  let rec apply (s: t) (t: typ) : typ = match t with
    | Const_t _ | Var_t {contents = Quant _} -> t
    | Var_t {contents = Free (id, _)} ->
      (match IntMap.find s id with
       | Some t' -> t'
       | None -> t)
    | Var_t {contents = Link t} -> apply s t
    | App_t (name, args) -> App_t (name, List.map ~f:(apply s) args)
    | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(apply s) args, apply s ret)

  let compose (s1: t) (s2: t) : t =
    let merge outer inner =
      IntMap.fold ~f:(fun ~key:name ~data:typ m ->
          IntMap.add ~key:name ~data:typ m) ~init:outer inner
    in merge s1 (IntMap.map ~f:(fun t -> apply s1 t) s2)

  let rec of_types (t1: typ) (t2: typ) : t =
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
      | x, Var_t {contents = Link y} -> of_types x y
      | Var_t {contents = Free (x, _)}, Var_t {contents = Free (y, _)}
        when x = y ->
        unify_error t1 t2 ~msg:(Info.of_thunk (fun () ->
            sprintf "Free variable %d occurred in %s and %s."
              x (typ_to_string t1) (typ_to_string t2)))
      | t, Var_t ({contents = Free (id, _)})
      | Var_t ({contents = Free (id, _)}), t ->
        if occurs id t then
          unify_error t1 t2 ~msg:(Info.of_thunk (fun () ->
              sprintf "Free variable %d occurs in %s." id (typ_to_string t)))
        else IntMap.singleton id t
      | Arrow_t (args1, ret1), Arrow_t (args2, ret2) ->
        let s1 =
          List.fold2_exn ~init:IntMap.empty args1 args2 ~f:(fun s a1 a2 ->
              compose s (of_types a1 a2))
        in
        let s2 = of_types ret1 ret2 in
        compose s1 s2
      | App_t (const1, args1), App_t (const2, args2) when const1 = const2 ->
        List.fold2_exn ~init:IntMap.empty args1 args2 ~f:(fun s a1 a2 ->
            compose s (of_types a1 a2))
      | _ -> unify_error t1 t2
end

let fresh_free level = Var_t (ref (Free (Fresh.int (), level)))

let normalize = Type.normalize

let occurs id level typ =
  let error (msg: Info.t) =
    raise @@ TypeError (Error.of_thunk (fun () ->
        sprintf "Failed occurs check in %s: %s"
          (typ_to_string typ) (Info.to_string_hum msg)))
  in

  let rec occurs' id level typ =
    match typ with
    | Const_t _
    | Var_t {contents = Quant _} -> ()
    | Var_t ({contents = Free (id', level')} as typ') ->
      if id' = id
      then error (Info.of_thunk (fun () -> sprintf "ft%d occurred twice" id))
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
  if t1 = t2 then () else
    match t1, t2 with
    | Const_t t1', Const_t t2' when t1' = t2' -> ()
    | Var_t {contents = Link t1'}, t2'
    | t1', Var_t {contents = Link t2'} -> unify_exn t1' t2'
    | Var_t {contents = Free (id1, _)}, Var_t {contents = Free (id2, _)} when id1 = id2 ->
      raise (TypeError (Error.of_string "Free variable occurred in both types."))
    | Var_t ({contents = Free (id, level)} as t'), t
    | t, Var_t ({contents = Free (id, level)} as t') -> occurs id level t; t' := Link t
    | Arrow_t (args1, ret1), Arrow_t (args2, ret2) ->
       (match List.zip args1 args2 with
        | Some args -> List.iter args ~f:(fun (a1, a2) -> unify_exn a1 a2)
        | None -> unify_error t1 t2);
       unify_exn ret1 ret2
    | App_t (const1, args1), App_t (const2, args2) when const1 = const2 ->
       (match List.zip args1 args2 with
        | Some args -> List.iter args ~f:(fun (a1, a2) -> unify_exn a1 a2)
        | None -> unify_error t1 t2)
    | _ -> unify_error t1 t2

let unify t1 t2 = try Some (unify_exn t1 t2; t1) with TypeError _ -> None
let is_unifiable t1 t2 = Option.is_some (unify (instantiate 0 t1) (instantiate 0 t2))

let typeof (ctx: typ Ctx.t) (level: level) (expr: expr) : TypedExpr.t =
  let open TypedExpr in
  let error msg =
    raise @@ TypeError (Error.of_thunk (fun () ->
        sprintf "In %s: %s" (Expr.to_string expr) (Info.to_string_hum msg)))
  in

  let rec typeof' ctx level expr =
    let rec typeof_func num_args typ =
      match typ with
      | Arrow_t (args, ret) -> args, ret
      | Var_t {contents = Link typ} -> typeof_func num_args typ
      | Var_t ({contents = Free (_, level)} as typ) ->
        let args =
          List.range 0 num_args |> List.map ~f:(fun _ -> fresh_free level)
        in
        let ret = fresh_free level in
        typ := Link (Arrow_t (args, ret));
        args, ret
      | _ -> error (Info.of_string "Not a function.")
    in
    let rec typeof_tree t : TypedExpr.t Tree.t * typ =
      match t with
      | Tree.Empty -> Tree.Empty, App_t ("tree", [fresh_free level])
      | Tree.Node (x, y) ->
        let x' = typeof' ctx level x in
        let typ = App_t ("tree", [TypedExpr.to_type x']) in
        let y', y_typs = List.map y ~f:typeof_tree |> List.unzip in
        List.iter y_typs ~f:(unify_exn typ); Tree.Node (x', y'), typ
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
              unify_exn typ (TypedExpr.to_type elem');
              List (List.append elems [elem'], App_t ("list", [typ]))
            | _ -> assert false)
    | `Id name ->
      (match Ctx.lookup ctx name with
       | Some t -> Id (name, instantiate level t)
       | None -> error (Info.of_thunk (fun () ->
           sprintf "%s is unbound in context %s."
             name (Ctx.to_string ctx typ_to_string))))
    | `Lambda (args, body) ->
      (* Generate fresh type variables for each argument and bind them
         into the existing context. *)
      let ctx' = List.fold args
          ~init:ctx
          ~f:(fun ctx' arg -> Ctx.bind ctx' arg (fresh_free level)) in
      let arg_typs = List.map args ~f:(fun arg -> Ctx.lookup_exn ctx' arg) in
      let body' = typeof' ctx' level body in
      Lambda ((args, body'), Arrow_t (arg_typs, TypedExpr.to_type body'))
    | `Apply (func, args) ->
      let func' = typeof' ctx level func in
      let args' = List.map args ~f:(typeof' ctx level) in
      let arg_typs, ret_typ = typeof_func (List.length args) (TypedExpr.to_type func') in
      (match List.zip arg_typs args' with
       | Some pairs -> List.iter pairs ~f:(fun (typ, arg') -> unify_exn typ (TypedExpr.to_type arg'))
       | None -> error (Info.of_string "Wrong number of arguments."));
      Apply ((func', args'), ret_typ)
    | `Op (op, args) ->
      let args' = List.map args ~f:(typeof' ctx level) in
      let arg_typs, ret_typ = typeof_func (List.length args) (instantiate level (Op.typ op)) in
      (match List.zip arg_typs args' with
       | Some pairs -> List.iter pairs ~f:(fun (typ, arg') -> unify_exn typ (TypedExpr.to_type arg'))
       | None -> error (Info.of_string "Wrong number of arguments."));
      Op ((op, args'), ret_typ)
    | `Let (name, bound, body) ->
      let bound' = typeof' ctx (level + 1) bound in
      let body' =
        let bound_typ = generalize level (TypedExpr.to_type bound') in
        typeof' (Ctx.bind ctx name bound_typ) level body in
      Let ((name, bound', body'), TypedExpr.to_type body')
  in typeof' ctx level expr

let stdlib_tctx = [
  "foldr", "(list[a], ((b, a) -> b), b) -> b";
  "foldl", "(list[a], ((b, a) -> b), b) -> b";
  "foldt", "(tree[a], ((list[b], a) -> b), b) -> b";
  "map", "(list[a], (a -> b)) -> list[b]";
  "mapt", "(tree[a], (a -> b)) -> tree[b]";
  "filter", "(list[a], (a -> bool)) -> list[a]";

  "sort", "(list[num]) -> list[num]";
  "merge", "(list[num], list[num]) -> list[num]";
  "dedup", "(list[a]) -> list[a]";
  "take", "(list[a], num) -> list[a]";
  "drop", "(list[a], num) -> list[a]";
  "append", "(list[a], list[a]) -> list[a]";
  "reverse", "(list[a]) -> list[a]";
  "intersperse", "(a, list[a]) -> list[a]";
  "concat", "(list[list[a]]) -> list[a]";
  "zip", "(list[a], list[a]) -> list[list[a]]";

  "inf", "num";
] |> List.map ~f:(fun (name, str) -> name, Type.of_string str) |> Ctx.of_alist_exn

(** Infer the type of an expression in context. Returns an expression
tree annotated with types. *)
let infer ctx (expr: expr) : TypedExpr.t =
  let (x, runtime) = with_runtime (fun () ->
      let ctx' = Ctx.merge stdlib_tctx ctx
          ~f:(fun ~key:_ value ->
              match value with
              | `Both (_, v) | `Left v | `Right v -> Some v) in
      let expr' = typeof ctx' 0 expr in
      TypedExpr.map ~f:(generalize (-1)) expr')
  in
  add_time total_infer_time runtime; x

(** Parse a string and return a typed expression. *)
let typed_expr_of_string (s: string) : TypedExpr.t =
  let expr = Expr.of_string s in
  infer (Ctx.empty ()) expr

(** Return a list of names that are free in the given expression,
    along with their types. *)
module IdTypeSet = Set.Make(struct
    type t = id * typ with compare, sexp
  end)

let stdlib_names = Ctx.keys stdlib_tctx |> String.Set.of_list
let free ?(bound=stdlib_names) (e: TypedExpr.t) : (id * typ) list =
  let open TypedExpr in
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

let type_nesting_depth = Type.nesting_depth
