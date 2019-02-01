open Core
open Printf
open Ast
open Collections
open Expr
open Util

exception TypeError of Error.t

let total_infer_time = ref Time.Span.zero

module Type0 = struct
  type const = const_typ = Num_t | Bool_t [@@deriving compare, sexp]

  type level = int [@@deriving compare, sexp]

  type t = typ =
    | Const_t of const
    | App_t of id * t list
    | Arrow_t of t list * t
    | Var_t of var ref

  and var = var_typ = Free of int * level | Link of t | Quant of string
  [@@deriving compare, sexp]

  let equal t1 t2 = compare t1 t2 = 0

  let rec free_vars = function
    | Var_t {contents= Free (id, _)} -> Int.Set.singleton id
    | App_t (_, args) -> Int.Set.union_list (List.map args ~f:free_vars)
    | Arrow_t (args, ret) ->
        Int.Set.union
          (Int.Set.union_list (List.map args ~f:free_vars))
          (free_vars ret)
    | _ -> Int.Set.empty

  (** Return the nesting depth of this type. For example, the type
      "int" has a nesting depth of 1, and the type "list[int]" has a
      nesting depth of 2. *)
  let rec nesting_depth (t : t) : int =
    match t with
    | Const_t _ | Var_t _ -> 1
    | App_t (_, args) -> 1 + List.max (List.map ~f:nesting_depth args)
    | Arrow_t (args, ret) ->
        let args_max = List.max (List.map ~f:nesting_depth args) in
        let ret_depth = nesting_depth ret in
        if args_max > ret_depth then args_max else ret_depth

  (** Normalize a type by renaming each of its quantified type variables. *)
  let normalize (t : t) : t =
    let count = ref (-1) in
    let fresh_name () =
      incr count ;
      "t" ^ Int.to_string !count
    in
    let rec norm ctx typ =
      match typ with
      | Const_t _ | Var_t {contents= Free _} -> typ
      | Var_t {contents= Link typ'} -> norm ctx typ'
      | Var_t {contents= Quant name} -> (
        match Ctx.lookup ctx name with
        | Some name' -> Var_t (ref (Quant name'))
        | None ->
            let name' = fresh_name () in
            Ctx.update ctx name name' ;
            Var_t (ref (Quant name')) )
      | App_t (const, args) -> App_t (const, List.map args ~f:(norm ctx))
      | Arrow_t (args, ret) -> Arrow_t (List.map args ~f:(norm ctx), norm ctx ret)
    in
    norm (Ctx.empty ()) t

  let num = Const_t Num_t

  let bool = Const_t Bool_t

  let quant name = Var_t (ref (Quant name))

  let free id level = Var_t (ref (Free (id, level)))

  let list t = App_t ("list", [t])

  let tree t = App_t ("tree", [t])

  let arrow1 arg body = Arrow_t ([arg], body)

  let arrow2 a1 a2 body = Arrow_t ([a1; a2], body)

  let arity : t -> int = function Arrow_t (args, _) -> List.length args | _ -> 0

  (** Parse a type from a string. *)
  let of_string_exn : string -> t =
   fun s ->
    let lexbuf = Lexing.from_string s in
    try Parser_sexp.typ_eof Lexer_sexp.token lexbuf with
    | Parser_sexp.Error -> raise (ParseError s)
    | Lexer_sexp.SyntaxError _ -> raise (ParseError s)
    | Parsing.Parse_error -> raise (ParseError s)

  let of_string : string -> t Or_error.t =
   fun s -> Or_error.try_with (fun () -> of_string_exn s)

  (** Convert a type to a string. *)
  let rec to_string (t : t) : string =
    let tlist_str typs = typs |> List.map ~f:to_string |> String.concat ~sep:", " in
    match t with
    | Const_t Num_t -> "num"
    | Const_t Bool_t -> "bool"
    | Var_t {contents= Free (id, _)} -> "ft" ^ Int.to_string id
    | Var_t {contents= Quant name} -> name
    | Var_t {contents= Link typ'} -> to_string typ'
    | App_t (id, args) -> sprintf "%s[%s]" id (tlist_str args)
    | Arrow_t ([arg], ret) -> sprintf "(%s -> %s)" (to_string arg) (to_string ret)
    | Arrow_t (args, ret) -> sprintf "((%s) -> %s)" (tlist_str args) (to_string ret)
end

let unify_error ?msg t1 t2 =
  raise
  @@ TypeError
       (Error.of_thunk (fun () ->
            match msg with
            | Some msg ->
                sprintf "Failed to unify %s and %s: %s" (Type0.to_string t1)
                  (Type0.to_string t2) (Info.to_string_hum msg)
            | None ->
                sprintf "Failed to unify %s and %s." (Type0.to_string t1)
                  (Type0.to_string t2) ))

module TypedExpr = struct
  module T = struct
    type t =
      | Num of int * Type0.t
      | Bool of bool * Type0.t
      | List of t list * Type0.t
      | Tree of t Tree.t * Type0.t
      | Id of id * Type0.t
      | Let of (id * t * t) * Type0.t
      | Lambda of (id list * t) * Type0.t
      | Apply of (t * t list) * Type0.t
      | Op of (Op.t * t list) * Type0.t
    [@@deriving compare, sexp]
  end

  include T

  let normalize (expr : t) : t =
    let count = ref (-1) in
    let fresh_name () =
      let n = incr count ; !count in
      let prefix = Char.of_int_exn ((n mod 26) + 97) in
      let suffix = if n >= 26 then Int.to_string ((n - 26) mod 26) else "" in
      Printf.sprintf "%c%s" prefix suffix
    in
    let rec norm ctx e =
      let norm_all = List.map ~f:(norm ctx) in
      match e with
      | Num _ | Bool _ -> e
      | Id (x, t) -> (
        match Ctx.lookup ctx x with Some x' -> Id (x', t) | None -> e )
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
            List.fold_right args ~init:(ctx, []) ~f:(fun arg (ctx', args') ->
                let arg' = fresh_name () in
                (Ctx.bind ctx' arg arg', arg' :: args') )
          in
          Lambda ((args', norm ctx' body), t)
    in
    norm (Ctx.empty ()) expr

  let rec map ~f (e : t) : t =
    match e with
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
  let rec to_expr (e : t) : expr =
    match e with
    | Num (x, _) -> `Num x
    | Bool (x, _) -> `Bool x
    | Id (x, _) -> `Id x
    | List (x, _) -> `List (List.map x ~f:to_expr)
    | Tree (x, _) -> `Tree (Tree.map x ~f:to_expr)
    | Lambda ((x, y), _) -> `Lambda (x, to_expr y)
    | Apply ((x, y), _) -> `Apply (to_expr x, List.map y ~f:to_expr)
    | Op ((x, y), _) -> `Op (x, List.map y ~f:to_expr)
    | Let ((x, y, z), _) -> `Let (x, to_expr y, to_expr z)

  (** Get the type annotation of the root of a typed expression. *)
  let to_type = function
    | Num (_, t)
     |Bool (_, t)
     |List (_, t)
     |Tree (_, t)
     |Id (_, t)
     |Lambda (_, t)
     |Apply (_, t)
     |Op (_, t)
     |Let (_, t) ->
        t

  (** Convert a typed expression to a string. *)
  let to_string (e : t) : string = Expr.to_string (to_expr e)

  include Comparable.Make (T)
end

(** A unifier is a mapping from free type variables to types. It
    can be applied to a type to fill in some or all of its free type
    variables. *)
module Unifier = struct
  type t = Type0.t Int.Map.t [@@deriving sexp]

  let empty = Int.Map.empty

  let equal = Int.Map.equal Type0.equal

  let to_string u = Sexp.to_string_hum (sexp_of_t u)

  let rec apply (s : t) (t : typ) : typ =
    match t with
    | Const_t _ | Var_t {contents= Quant _} -> t
    | Var_t {contents= Free (id, _)} -> (
      match Int.Map.find s id with Some t' -> t' | None -> t )
    | Var_t {contents= Link t} -> apply s t
    | App_t (name, args) -> App_t (name, List.map ~f:(apply s) args)
    | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(apply s) args, apply s ret)

  let apply_ctx : t -> Type0.t String.Map.t -> Type0.t String.Map.t =
   fun u ctx -> String.Map.map ctx ~f:(apply u)

  let merge outer inner =
    Int.Map.merge outer inner ~f:(fun ~key:_ -> function
      | `Both (_, i) -> Some i | `Left x | `Right x -> Some x )

  let compose : outer:t -> inner:t -> t =
   fun ~outer ~inner -> merge (Int.Map.map ~f:(fun t -> apply inner t) outer) inner

  let rec of_types_exn (t1 : typ) (t2 : typ) : t =
    (* Check whether the free variable 'id' occurs in type 'typ'. If it
       does, we cannot substitute 'typ' for 'id' due to infinite
       recursion. *)
    let rec occurs (id : int) (typ : typ) : bool =
      match typ with
      | Const_t _ | Var_t {contents= Quant _} -> false
      | Var_t {contents= Free (id', _)} -> id = id'
      | Var_t {contents= Link t} -> occurs id t
      | App_t (_, args) -> List.exists args ~f:(occurs id)
      | Arrow_t (args, ret) -> List.exists args ~f:(occurs id) || occurs id ret
    in
    if t1 = t2 then Int.Map.empty
    else
      match (t1, t2) with
      | Var_t {contents= Link x}, y | x, Var_t {contents= Link y} ->
          of_types_exn x y
      | Var_t {contents= Free (x, _)}, Var_t {contents= Free (y, _)} when x = y ->
          unify_error t1 t2
            ~msg:
              (Info.of_thunk (fun () ->
                   sprintf "Free variable %d occurred in %s and %s." x
                     (Type0.to_string t1) (Type0.to_string t2) ))
      | t, Var_t {contents= Free (id, _)} | Var_t {contents= Free (id, _)}, t ->
          if occurs id t then
            unify_error t1 t2
              ~msg:
                (Info.of_thunk (fun () ->
                     sprintf "Free variable %d occurs in %s." id (Type0.to_string t)
                 ))
          else Int.Map.singleton id t
      | Arrow_t (args1, ret1), Arrow_t (args2, ret2) ->
          let s1 = of_many_types_exn args1 args2 in
          let s2 = of_types_exn ret1 ret2 in
          compose ~outer:s1 ~inner:s2
      | App_t (const1, args1), App_t (const2, args2) when const1 = const2 ->
          of_many_types_exn args1 args2
      | _ -> unify_error t1 t2

  and of_many_types_exn : Type0.t list -> Type0.t list -> t =
   fun ts1 ts2 ->
    match List.zip ts1 ts2 with
    | Some ts ->
        List.fold_left ts ~init:empty ~f:(fun s (a1, a2) ->
            compose ~outer:s ~inner:(of_types_exn (apply s a1) (apply s a2)) )
    | None ->
        let err =
          Error.create "Length mismatch." (ts1, ts2)
            [%sexp_of: Type0.t list * Type0.t list]
        in
        raise (TypeError err)

  let of_types t1 t2 = try Some (of_types_exn t1 t2) with TypeError _ -> None

  let of_alist_exn = Int.Map.of_alist_exn

  let to_alist = Int.Map.to_alist ~key_order:`Decreasing

  let relevant_to u t =
    let free_t = Type0.free_vars t in
    Int.Map.filteri u ~f:(fun ~key:id ~data:_ -> Int.Set.mem free_t id)
end

let fresh_free level = Var_t (ref (Free (Fresh.int (), level)))

let normalize = Type0.normalize

let occurs id level typ =
  let error (msg : Info.t) =
    raise
    @@ TypeError
         (Error.of_thunk (fun () ->
              sprintf "Failed occurs check in %s: %s" (Type0.to_string typ)
                (Info.to_string_hum msg) ))
  in
  let rec occurs' id level typ =
    match typ with
    | Const_t _ | Var_t {contents= Quant _} -> ()
    | Var_t ({contents= Free (id', level')} as typ') ->
        if id' = id then
          error (Info.of_thunk (fun () -> sprintf "ft%d occurred twice" id))
        else if
          (* The other type is being claimed by the let binding, if it is
           owned by a lower let. This prevents the free variable from
           being prematurely generalized. *)
          level' > level
        then typ' := Free (id', level)
        else ()
    | Var_t {contents= Link typ'} -> occurs' id level typ'
    | App_t (_, args) -> List.iter args ~f:(fun arg -> occurs' id level arg)
    | Arrow_t (args, ret) ->
        List.iter args ~f:(fun arg -> occurs' id level arg) ;
        occurs' id level ret
  in
  occurs' id level typ

(** The level is associated with the let expression that "owns" a
particular free type variable. When that let expression is completely
typed, its free type variables can be generalized. *)
let rec generalize level typ =
  match typ with
  | Var_t {contents= Free (id, level')} when level' > level ->
      Var_t (ref (Quant ("t" ^ Int.to_string id)))
  | Var_t {contents= Link typ'} -> generalize level typ'
  | Arrow_t (args, ret) ->
      Arrow_t (List.map ~f:(generalize level) args, generalize level ret)
  | App_t (const, args) -> App_t (const, List.map ~f:(generalize level) args)
  | Const_t _ | Var_t {contents= Quant _} | Var_t {contents= Free _} -> typ

(** Instantiating a type replaces all quantified type variables with
fresh free type variables. *)
let instantiate ?(ctx = Ctx.empty ()) level typ =
  let rec inst ctx typ =
    match typ with
    | Const_t _ | Var_t {contents= Free _} -> typ
    | Var_t {contents= Quant name} -> (
      match Ctx.lookup ctx name with
      | Some typ' -> typ'
      | None ->
          let typ' = fresh_free level in
          Ctx.update ctx name typ' ; typ' )
    | Var_t {contents= Link typ'} -> inst ctx typ'
    | Arrow_t (args, ret) -> Arrow_t (List.map ~f:(inst ctx) args, inst ctx ret)
    | App_t (const, args) -> App_t (const, List.map ~f:(inst ctx) args)
  in
  inst ctx typ

let rec unify_exn t1 t2 =
  if t1 = t2 then ()
  else
    match (t1, t2) with
    | Const_t t1', Const_t t2' when t1' = t2' -> ()
    | Var_t {contents= Link t1'}, t2' | t1', Var_t {contents= Link t2'} ->
        unify_exn t1' t2'
    | Var_t {contents= Free (id1, _)}, Var_t {contents= Free (id2, _)}
      when id1 = id2 ->
        raise (TypeError (Error.of_string "Free variable occurred in both types."))
    | Var_t ({contents= Free (id, level)} as t'), t
     |t, Var_t ({contents= Free (id, level)} as t') ->
        occurs id level t ;
        t' := Link t
    | Arrow_t (args1, ret1), Arrow_t (args2, ret2) ->
        ( match List.zip args1 args2 with
        | Some args -> List.iter args ~f:(fun (a1, a2) -> unify_exn a1 a2)
        | None -> unify_error t1 t2 ) ;
        unify_exn ret1 ret2
    | App_t (const1, args1), App_t (const2, args2) when const1 = const2 -> (
      match List.zip args1 args2 with
      | Some args -> List.iter args ~f:(fun (a1, a2) -> unify_exn a1 a2)
      | None -> unify_error t1 t2 )
    | _ -> unify_error t1 t2

let unify t1 t2 = try Some (unify_exn t1 t2 ; t1) with TypeError _ -> None

let is_unifiable t1 t2 =
  Option.is_some (unify (instantiate 0 t1) (instantiate 0 t2))

let typeof (ctx : typ Ctx.t) (level : level) (expr : expr) : TypedExpr.t =
  let open TypedExpr in
  let error msg =
    raise
    @@ TypeError
         (Error.of_thunk (fun () ->
              sprintf "In %s: %s" (Expr.to_string expr) (Info.to_string_hum msg) ))
  in
  let rec typeof' ctx level expr =
    let rec typeof_func num_args typ =
      match typ with
      | Arrow_t (args, ret) -> (args, ret)
      | Var_t {contents= Link typ} -> typeof_func num_args typ
      | Var_t ({contents= Free (_, level)} as typ) ->
          let args =
            List.range 0 num_args |> List.map ~f:(fun _ -> fresh_free level)
          in
          let ret = fresh_free level in
          typ := Link (Arrow_t (args, ret)) ;
          (args, ret)
      | _ -> error (Info.of_string "Not a function.")
    in
    let rec typeof_tree t : TypedExpr.t Tree.t * typ =
      match t with
      | Tree.Empty -> (Tree.Empty, App_t ("tree", [fresh_free level]))
      | Tree.Node (x, y) ->
          let x' = typeof' ctx level x in
          let typ = App_t ("tree", [TypedExpr.to_type x']) in
          let y', y_typs = List.map y ~f:typeof_tree |> List.unzip in
          List.iter y_typs ~f:(unify_exn typ) ;
          (Tree.Node (x', y'), typ)
    in
    match expr with
    | `Num x -> Num (x, Const_t Num_t)
    | `Bool x -> Bool (x, Const_t Bool_t)
    | `Tree x ->
        let x', typ = typeof_tree x in
        Tree (x', typ)
    | `List [] -> List ([], App_t ("list", [fresh_free level]))
    | `List elems ->
        List.fold_left elems
          ~init:(typeof' ctx level (`List []))
          ~f:(fun texpr elem ->
            match texpr with
            | List (elems, App_t ("list", [typ])) ->
                let elem' = typeof' ctx level elem in
                unify_exn typ (TypedExpr.to_type elem') ;
                List (List.append elems [elem'], App_t ("list", [typ]))
            | _ -> assert false )
    | `Id name -> (
      match Ctx.lookup ctx name with
      | Some t -> Id (name, instantiate level t)
      | None ->
          error
            (Info.of_thunk (fun () ->
                 sprintf "%s is unbound in context %s." name
                   (Ctx.to_string ctx Type0.to_string) )) )
    | `Lambda (args, body) ->
        (* Generate fresh type variables for each argument and bind them
         into the existing context. *)
        let ctx' =
          List.fold args ~init:ctx ~f:(fun ctx' arg ->
              Ctx.bind ctx' arg (fresh_free level) )
        in
        let arg_typs = List.map args ~f:(fun arg -> Ctx.lookup_exn ctx' arg) in
        let body' = typeof' ctx' level body in
        Lambda ((args, body'), Arrow_t (arg_typs, TypedExpr.to_type body'))
    | `Apply (func, args) ->
        let func' = typeof' ctx level func in
        let args' = List.map args ~f:(typeof' ctx level) in
        let arg_typs, ret_typ =
          typeof_func (List.length args) (TypedExpr.to_type func')
        in
        ( match List.zip arg_typs args' with
        | Some pairs ->
            List.iter pairs ~f:(fun (typ, arg') ->
                unify_exn typ (TypedExpr.to_type arg') )
        | None -> error (Info.of_string "Wrong number of arguments.") ) ;
        Apply ((func', args'), ret_typ)
    | `Op (op, args) ->
        let args' = List.map args ~f:(typeof' ctx level) in
        let arg_typs, ret_typ =
          typeof_func (List.length args) (instantiate level (Op.typ op))
        in
        ( match List.zip arg_typs args' with
        | Some pairs ->
            List.iter pairs ~f:(fun (typ, arg') ->
                unify_exn typ (TypedExpr.to_type arg') )
        | None -> error (Info.of_string "Wrong number of arguments.") ) ;
        Op ((op, args'), ret_typ)
    | `Let (name, bound, body) ->
        (* Bind a fresh free type variable to the name. *)
        let ctx = Ctx.bind ctx name (fresh_free level) in
        let bound' = typeof' ctx (level + 1) bound in
        let body' =
          let bound_typ = generalize level (TypedExpr.to_type bound') in
          typeof' (Ctx.bind ctx name bound_typ) level body
        in
        Let ((name, bound', body'), TypedExpr.to_type body')
  in
  typeof' ctx level expr

let stdlib_tctx =
  [ ("foldr", "(list[a], ((b, a) -> b), b) -> b")
  ; ("foldl", "(list[a], ((b, a) -> b), b) -> b")
  ; ("foldt", "(tree[a], ((list[b], a) -> b), b) -> b")
  ; ("map", "(list[a], (a -> b)) -> list[b]")
  ; ("mapt", "(tree[a], (a -> b)) -> tree[b]")
  ; ("filter", "(list[a], (a -> bool)) -> list[a]")
  ; ("sort", "(list[num]) -> list[num]")
  ; ("merge", "(list[num], list[num]) -> list[num]")
  ; ("dedup", "(list[a]) -> list[a]")
  ; ("take", "(list[a], num) -> list[a]")
  ; ("drop", "(list[a], num) -> list[a]")
  ; ("append", "(list[a], list[a]) -> list[a]")
  ; ("reverse", "(list[a]) -> list[a]")
  ; ("intersperse", "(list[a], a) -> list[a]")
  ; ("concat", "(list[list[a]]) -> list[a]")
  ; ("zip", "(list[a], list[a]) -> list[list[a]]")
  ; ("inf", "num") ]
  |> List.map ~f:(fun (name, str) -> (name, Type0.of_string_exn str))
  |> Ctx.of_alist_exn

(** Infer the type of an expression in context. Returns an expression
tree annotated with types. *)
let infer_exn ctx (expr : expr) : TypedExpr.t =
  let x, runtime =
    with_runtime (fun () ->
        let ctx' =
          Ctx.merge stdlib_tctx ctx ~f:(fun ~key:_ value ->
              match value with `Both (_, v) | `Left v | `Right v -> Some v )
        in
        let expr' = typeof ctx' 0 expr in
        TypedExpr.map ~f:(generalize (-1)) expr' )
  in
  add_time total_infer_time runtime ;
  x

let infer ctx expr = try Ok (infer_exn ctx expr) with TypeError err -> Error err

(** Parse a string and return a typed expression. *)
let typed_expr_of_string (s : string) : TypedExpr.t =
  let expr = Expr.of_string_exn s in
  infer_exn (Ctx.empty ()) expr

(** Return a list of names that are free in the given expression,
    along with their types. *)
module IdTypeSet = Set.Make (struct
  type t = id * typ [@@deriving compare, sexp]
end)

let stdlib_names = Ctx.keys stdlib_tctx |> String.Set.of_list

let free ?(bound = stdlib_names) (e : TypedExpr.t) : (id * typ) list =
  let open TypedExpr in
  let rec f bound e : IdTypeSet.t =
    match e with
    | Num _ | Bool _ -> IdTypeSet.empty
    | Id (x, t) ->
        if String.Set.mem bound x then IdTypeSet.empty
        else IdTypeSet.singleton (x, t)
    | List (x, _) -> List.map ~f:(f bound) x |> IdTypeSet.union_list
    | Tree (x, _) -> Tree.flatten x |> List.map ~f:(f bound) |> IdTypeSet.union_list
    | Lambda ((args, body), _) ->
        f (String.Set.union bound (String.Set.of_list args)) body
    | Apply ((func, args), _) ->
        IdTypeSet.union_list (f bound func :: List.map ~f:(f bound) args)
    | Op ((_, args), _) -> List.map ~f:(f bound) args |> IdTypeSet.union_list
    | Let ((x, e1, e2), _) ->
        let bound' = String.Set.add bound x in
        IdTypeSet.union (f bound' e1) (f bound' e2)
  in
  f bound e |> IdTypeSet.to_list

module Type = struct
  include Type0

  let generalize : t String.Map.t -> t -> t =
   fun ctx t ->
    let free_ctx_vars =
      String.Map.to_alist ctx |> List.map ~f:Tuple.T2.get2 |> List.map ~f:free_vars
      |> Int.Set.union_list
    in
    let gen_vars = Int.Set.diff (free_vars t) free_ctx_vars in
    let rec gen = function
      | Var_t {contents= Free (id, _)} when Set.mem gen_vars id ->
          Var_t (ref (Quant ("t" ^ Int.to_string id)))
      | Var_t {contents= Link t} -> gen t
      | Arrow_t (args, ret) -> Arrow_t (List.map ~f:gen args, gen ret)
      | App_t (const, args) -> App_t (const, List.map ~f:gen args)
      | (Const_t _ | Var_t {contents= Quant _} | Var_t {contents= Free _}) as t -> t
    in
    gen t

  let of_expr : ?ctx:t String.Map.t -> Expr.t -> t * t Int.Map.t =
   fun ?(ctx = String.Map.empty) expr ->
    let error msg =
      raise
      @@ TypeError
           (Error.of_thunk (fun () ->
                sprintf "In %s: %s" (Expr.to_string expr) (Info.to_string_hum msg)
            ))
    in
    let rec of_tree ctx = function
      | Tree.Empty -> (fresh_free 0, Unifier.empty)
      | Tree.Node (x, ys) ->
          let t1, u1 = of_expr ctx x in
          List.fold_left ys ~init:(t1, u1) ~f:(fun (t, u) y ->
              let ctx = Unifier.apply_ctx u ctx in
              let t', _ = of_tree ctx y in
              let u'' = Unifier.of_types_exn t t' in
              (Unifier.apply u'' t', u'') )
    and of_list ctx = function
      | [] -> (fresh_free 0, Unifier.empty)
      | x :: xs ->
          let t1, u1 = of_expr ctx x in
          let t2, u2 = of_list (Unifier.apply_ctx u1 ctx) xs in
          let u = Unifier.compose ~inner:u2 ~outer:u1 in
          let u3 = Unifier.of_types_exn (Unifier.apply u t1) (Unifier.apply u t2) in
          let u = Unifier.compose ~inner:u3 ~outer:u in
          (Unifier.apply u3 t2, u)
    and of_id ctx id =
      match String.Map.find ctx id with
      | Some t -> (instantiate 0 t, Unifier.empty)
      | None ->
          Info.create "Unbound name." (id, ctx) [%sexp_of: string * t String.Map.t]
          |> error
    and of_lambda ctx args body =
      let ctx, ts =
        List.fold_right args ~init:(ctx, []) ~f:(fun arg (ctx, ts) ->
            let t = fresh_free 0 in
            (String.Map.set ctx ~key:arg ~data:t, t :: ts) )
      in
      let t, u = of_expr ctx body in
      (Unifier.apply u (Arrow_t (ts, t)), u)
    and of_callable ctx func_t func_u args =
      let args_t, u =
        List.fold_right args ~init:([], func_u) ~f:(fun arg (ts, u) ->
            let arg_t, u' = of_expr (Unifier.apply_ctx u ctx) arg in
            (arg_t :: ts, Unifier.compose ~outer:u ~inner:u') )
      in
      let ret_t = fresh_free 0 in
      let u' =
        Unifier.of_types_exn (Unifier.apply u func_t)
          (Unifier.apply u (Arrow_t (args_t, ret_t)))
      in
      (Unifier.apply u' ret_t, Unifier.compose ~outer:u ~inner:u')
    and of_func ctx func args =
      let t, u = of_expr ctx func in
      let t = Unifier.apply u t in
      of_callable ctx t u args
    and of_op ctx op args =
      let t = Op.typ op |> instantiate 0 in
      of_callable ctx t Unifier.empty args
    and of_let ctx name bound body =
      let tv = fresh_free 0 in
      let bound_t, u = of_expr (String.Map.set ctx ~key:name ~data:tv) bound in
      let u =
        Unifier.compose ~outer:u
          ~inner:
            (Unifier.of_types_exn (Unifier.apply u tv) (Unifier.apply u bound_t))
      in
      let bound_t = Unifier.apply u bound_t in
      let ctx = Unifier.apply_ctx u ctx in
      let bound_t = generalize ctx bound_t in
      let body_t, u' = of_expr (String.Map.set ctx ~key:name ~data:bound_t) body in
      let u = Unifier.compose ~outer:u ~inner:u' in
      (Unifier.apply u body_t, u)
    and of_expr ctx expr =
      try
        let t, u =
          match expr with
          | `Num _ -> (Const_t Num_t, Unifier.empty)
          | `Bool _ -> (Const_t Bool_t, Unifier.empty)
          | `Tree x ->
              let t, u = of_tree ctx x in
              (App_t ("tree", [t]), u)
          | `List x ->
              let t, u = of_list ctx x in
              (App_t ("list", [t]), u)
          | `Id id -> of_id ctx id
          | `Lambda (args, body) -> of_lambda ctx args body
          | `Apply (func, args) -> of_func ctx func args
          | `Op (op, args) -> of_op ctx op args
          | `Let (name, bound, body) -> of_let ctx name bound body
        in
        let t = Unifier.apply u t in
        (t, u)
      with TypeError err ->
        let err =
          Error.tag_arg err "Type inference failed." expr [%sexp_of: Expr.t]
        in
        raise (TypeError err)
    in
    of_expr ctx expr

  let are_unifiable t1 t2 = Option.is_some (Unifier.of_types t1 t2)
end

module ImmutableType = struct
  module T = struct
    type t =
      | Const_i of const_typ
      | App_i of id * t list
      | Arrow_i of t list * t
      | Quant_i of string
      | Free_i of int * level
    [@@deriving compare, sexp]

    let hash = Hashtbl.hash
  end

  include T
  module Table = Hashtbl.Make (T)

  let rec of_type = function
    | Const_t t -> Const_i t
    | App_t (name, ts) -> App_i (name, List.map ~f:of_type ts)
    | Arrow_t (args, ret) -> Arrow_i (List.map ~f:of_type args, of_type ret)
    | Var_t {contents= Free (id, level)} -> Free_i (id, level)
    | Var_t {contents= Link t} -> of_type t
    | Var_t {contents= Quant name} -> Quant_i name

  let rec to_type = function
    | Const_i t -> Const_t t
    | App_i (name, ts) -> App_t (name, List.map ~f:to_type ts)
    | Arrow_i (args, ret) -> Arrow_t (List.map ~f:to_type args, to_type ret)
    | Free_i (id, level) -> Var_t (ref (Free (id, level)))
    | Quant_i name -> Var_t (ref (Quant name))
end
