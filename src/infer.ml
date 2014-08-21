open Core.Std 
open Printf
open Ast
open Util

exception TypeError of string

module IntSet = Set.Make(Int)

let fresh_quant () = Var_t (Quant (Fresh.name "t"))
let fresh_free () = Var_t (Free (Fresh.int ()))

let rec free = function
  | Const_t _
  | Var_t (Quant _) -> IntSet.empty
  | Var_t (Free id) -> IntSet.singleton id
  | App_t (_, args) -> List.map args ~f:free |> IntSet.union_list
  | Arrow_t (args, ret) -> IntSet.union (List.map args ~f:free |> IntSet.union_list) (free ret)

let rec occurs id typ = match typ with
  | Const_t _
  | Var_t (Quant _) -> ()
  | Var_t (Free id') -> 
     if id = id' 
     then raise @@ TypeError (sprintf "Failed occurs check: t%d in %s" id (typ_to_string typ))
     else ()
  | App_t (_, args) -> List.iter args ~f:(fun arg -> occurs id arg)
  | Arrow_t (args, ret) -> List.iter args ~f:(fun arg -> occurs id arg); occurs id ret

let normalize typ =
  let count = ref (-1) in
  let fresh_name () = incr count; "t" ^ (Int.to_string !count) in
  let rec norm ctx typ = match typ with
    | Const_t _
    | Var_t (Free _) -> typ
    | Var_t (Quant name) ->
       (match Ctx.lookup ctx name with
        | Some name' -> Var_t (Quant name')
        | None -> let name' = fresh_name () in
                  Ctx.update ctx name name'; Var_t (Quant name'))
    | App_t (const, args) -> App_t (const, List.map args ~f:(norm ctx))
    | Arrow_t (args, ret) -> Arrow_t (List.map args ~f:(norm ctx), norm ctx ret)
  in
  norm (Ctx.empty ()) typ

(** A substitution is a mapping from free type variables to types. *)
module Sub = struct
  include Map.Make(Int)
   
  (** Check whether a substitution has any entries that fail the
   occurs check. Raise an exception if any such entries are found. *)
  let check sub = to_alist sub |> List.iter ~f:(fun (id, typ) -> occurs id typ)

  let bind sub id typ = occurs id typ; add sub ~key:id ~data:typ

  (** Replace all free type variables with their value in the substitution. *)
  let rec apply sub typ = 
    check sub;
    match typ with
    | Const_t _ 
    | Var_t (Quant _) -> typ
    | Var_t (Free id) -> (match find sub id with Some typ' -> typ' | None -> typ)
    | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(apply sub) args, apply sub ret)
    | App_t (constr, args) -> App_t (constr, List.map ~f:(apply sub) args)

  let apply_ctx sub ctx =
    check sub;
    Ctx.map ctx ~f:(fun typ -> apply sub typ)

  (** Compose sub1 and sub2. Returns a substitution that is equivalent
   to applying sub1 followed by sub2. *)
  let compose sub1 sub2 = 
    check sub1; check sub2;
    map sub2 ~f:(apply sub1) 
    |> merge sub1 ~f:(fun ~key:_ value ->
                      match value with `Both (v, _) | `Left v | `Right v -> Some v)
end

(** Generalizing a type quantifies all the free type variables that
 are not bound in the context. Effectively, this means that a
 generalized type is made polymorphic over the type variables that are
 not already bound. *)
let rec generalize ctx typ =
  let typ_free = free typ in
  let ctx_free =
    Ctx.to_alist ctx |> List.map ~f:(fun (_, t) -> free t) |> IntSet.union_list in
  let general_ids = IntSet.diff typ_free ctx_free in
  match typ with
  | Const_t _
  | Var_t (Quant _) -> typ
  | Var_t (Free id) -> 
     if IntSet.mem general_ids id
     then Var_t (Quant ("t" ^ (Int.to_string id)))
     else typ
  | Arrow_t (args, ret) -> 
     Arrow_t (List.map ~f:(generalize ctx) args, generalize ctx ret)
  | App_t (const, args) ->
     App_t (const, List.map ~f:(generalize ctx) args)

(** Instantiating a type replaces all quantified type variables with
 fresh free type variables. *)
let instantiate typ = 
  let rec inst ctx typ =
    match typ with
    | Const_t _
    | Var_t (Free _) -> typ
    | Var_t (Quant name) -> 
       (match Ctx.lookup ctx name with
        | Some id -> Var_t (Free id)
        | None -> let id = Fresh.int () in
                  Ctx.update ctx name id;
                  Var_t (Free id))
    | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(inst ctx) args, inst ctx ret)
    | App_t (const, args) -> App_t (const, List.map ~f:(inst ctx) args)
  in
  inst (Ctx.empty ()) typ

(* Unify two types and return the substitution that makes the two types the same. *)
let rec unify t1 t2 = 
  let error () = raise @@ TypeError (sprintf "Failed to unify %s and %s."
                                             (typ_to_string t1)
                                             (typ_to_string t2))
  in
  if t1 = t2 then Sub.empty else
    match t1, t2 with
    | Const_t t1', Const_t t2' when t1' = t2' -> Sub.empty
    | Var_t (Free id), t 
    | t, Var_t (Free id) -> Sub.bind Sub.empty id t
    | Arrow_t (args1, ret1), Arrow_t (args2, ret2) ->
       (match List.zip args1 args2 with
        | Some arg_pairs ->
           let args_sub =
             List.fold_left arg_pairs 
                            ~init:Sub.empty 
                            ~f:(fun sub (a1, a2) -> 
                                let a1', a2' = (Sub.apply sub a1), (Sub.apply sub a2) in
                                Sub.compose (unify a1' a2') sub) in
           let ret1', ret2' = (Sub.apply args_sub ret1), (Sub.apply args_sub ret2) in
           Sub.compose (unify ret1' ret2') args_sub
        | None -> error ())
    | App_t (const1, args1), App_t (const2, args2) when const1 = const2 ->
       (match List.zip args1 args2 with
        | Some arg_pairs ->
           List.fold_left arg_pairs 
                          ~init:Sub.empty 
                          ~f:(fun sub (a1, a2) -> 
                              let a1', a2' = (Sub.apply sub a1), (Sub.apply sub a2) in
                              Sub.compose (unify a1' a2') sub)
        | None -> error ())
    | _ -> error ()

let to_string (sub: typ Sub.t) =
  Sub.to_alist sub
  |> List.map ~f:(fun (id, typ) -> (typ_to_string (Var_t (Free id))) ^ ": " ^ (typ_to_string typ))
  |> String.concat ~sep:" "

let rec typeof ctx (expr: expr) : typ * typ Sub.t =
  match expr with
  | `Num _ -> Const_t Num, Sub.empty
  | `Bool _ -> Const_t Bool, Sub.empty
  | `List [] -> App_t ("list", [fresh_free ()]), Sub.empty
  | `List elems ->
     let et, s = List.fold_left elems
                                ~init:(fresh_free (), Sub.empty)
                                ~f:(fun (typ, sub) elem ->
                                    let t, s = typeof (Sub.apply_ctx sub ctx) elem in
                                    let s = unify (Sub.apply s t) typ in
                                    t, s) in
     App_t ("list", [et]), s
  | `Id name -> instantiate (Ctx.lookup_exn ctx name), Sub.empty
  | `Lambda (args, body) ->
     (* Generate fresh type variables for each argument and bind them
        into the existing context. *)
     let ctx' = List.fold args
                          ~init:ctx
                          ~f:(fun ctx' arg -> Ctx.bind ctx' arg (fresh_free ())) in
     let arg_typs = List.map args ~f:(fun arg -> Ctx.lookup_exn ctx' arg) in
     let t1, s1 = typeof ctx' body in
     Sub.apply s1 (Arrow_t (arg_typs, t1)), s1
  | `Apply (func, args) ->
     let t1, s1 = typeof ctx func in
     let t2s, s2 = List.fold_left args 
                                  ~init:([], s1) 
                                  ~f:(fun (ts, sub) arg -> 
                                      let t, s = typeof (Sub.apply_ctx sub ctx) arg in
                                      (List.append ts [t]), Sub.compose s sub) in
     let b = fresh_free () in
     let s3 = unify (Sub.apply s2 t1) (Arrow_t (t2s, b)) in
     Sub.apply s3 b, Sub.compose s1 (Sub.compose s2 s3)
  | `Op (op, args) ->
     let t1, s1 = instantiate (Op.typ op), Sub.empty in
     let t2s, s2 = List.fold_left args 
                                  ~init:([], s1) 
                                  ~f:(fun (ts, sub) arg -> 
                                      let t, s = typeof (Sub.apply_ctx sub ctx) arg in
                                      List.append ts [t], Sub.compose s sub) in
     let b = fresh_free () in
     let s3 = unify (Sub.apply s2 t1) (Arrow_t (t2s, b)) in
     Sub.apply s3 b, Sub.compose s1 (Sub.compose s2 s3)
  | `Let (name, bound, body) ->
     let t1, s1 = typeof ctx bound in
     let t2, s2 =
       let ctx' = 
         let ctx'' = (Sub.apply_ctx s1 ctx) in
         Ctx.bind ctx'' name (generalize ctx'' (Sub.apply s1 t1)) in
       typeof ctx' body in
     t2, Sub.compose s1 s2

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
  let typ, sub = typeof ctx' expr in 
  generalize ctx' (Sub.apply sub typ)
