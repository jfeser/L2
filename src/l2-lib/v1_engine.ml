open Core
open Printf
open Ast
open Collections
open Infer
open Structure
open Util
module TypMemoizer = Sstream.Memoizer (Type) (TypedExpr)

module SimpleMemoizer =
  Sstream.Memoizer (struct
      type t = TypedExpr.t list [@@deriving compare, sexp]
    end)
    (Expr)

type config =
  { verbosity: int
  ; untyped: bool
  ; deduction: bool
  ; infer_base: bool
  ; max_exhaustive_depth: int
  ; flat_cost: bool }

let default_config =
  { verbosity= 0
  ; untyped= false
  ; deduction= true
  ; infer_base= true
  ; flat_cost= false
  ; max_exhaustive_depth= 7 }

let default_ops = Expr.Op.all |> List.filter ~f:(fun op -> op <> RCons)

let default_init =
  ["0"; "1"; "inf"; "[]"; "#f"]
  |> List.map ~f:(fun str -> Expr.of_string_exn str |> infer_exn (Ctx.empty ()))

let eval_ctx_of_alist =
  List.fold_left ~init:(Ctx.empty ()) ~f:(fun ctx (name, lambda) ->
      let ctx' = Ctx.bind ctx name `Unit in
      let value = `Closure (lambda, ctx') in
      Ctx.update ctx' name value ; Ctx.bind ctx name value )

let default_stdlib =
  [("inf", `Num Int.max_value)]
  @ ( [ ("foldr", "(lambda (l f i) (if (= l []) i (f (foldr (cdr l) f i) (car l))))")
      ; ("foldl", "(lambda (l f i) (if (= l []) i (foldl (cdr l) f (f i (car l)))))")
      ; ("map", "(lambda (l f) (if (= l []) [] (cons (f (car l)) (map (cdr l) f))))")
      ; ( "filter"
        , "(lambda (l f) (if (= l []) []\n\
          \             (if (f (car l))\n\
          \             (cons (car l) (filter (cdr l) f))\n\
          \             (filter (cdr l) f))))" )
      ; ( "mapt"
        , "(lambda (t f)\n\
          \           (if (= t {}) {}\n\
          \           (tree (f (value t)) (map (children t) (lambda (c) (mapt c \
           f))))))" )
      ; ( "foldt"
        , "(lambda (t f i)\n\
          \            (if (= t {}) i\n\
          \            (f (map (children t) (lambda (ct) (foldt ct f i)))\n\
          \                (value t))))" ) ]
    |> List.map ~f:(fun (name, str) -> (name, Expr.of_string_exn str)) )
  |> eval_ctx_of_alist

let _stdlib =
  [("inf", `Num Int.max_value)]
  @ ( [ ("foldr", "(lambda (l f i) (if (= l []) i (f (foldr (cdr l) f i) (car l))))")
      ; ("foldl", "(lambda (l f i) (if (= l []) i (foldl (cdr l) f (f i (car l)))))")
      ; ("map", "(lambda (l f) (if (= l []) [] (cons (f (car l)) (map (cdr l) f))))")
      ; ( "filter"
        , "(lambda (l f) (if (= l []) []\n\
          \             (if (f (car l))\n\
          \             (cons (car l) (filter (cdr l) f))\n\
          \             (filter (cdr l) f))))" )
      ; ( "mapt"
        , "(lambda (t f)\n\
          \           (if (= t {}) {}\n\
          \           (tree (f (value t)) (map (children t) (lambda (c) (mapt c \
           f))))))" )
      ; ( "foldt"
        , "(lambda (t f i)\n\
          \            (if (= t {}) i\n\
          \            (f (map (children t) (lambda (ct) (foldt ct f i)))\n\
          \                (value t))))" )
      ; ( "merge"
        , "(lambda (x y) (if (= x []) y (if (= y []) x (let a (car x) (let b (car \
           y) (if (< a b) (cons a (merge (cdr x) y)) (cons b (merge x (cdr \
           y)))))))))" )
      ; ( "take"
        , "(lambda (l x) (if (= [] l) [] (if (> x 0) (cons (car l) (take (cdr l) \
           (- x 1))) [])))" )
      ; ( "zip"
        , "(lambda (x y)\n\
          \            (if (| (= x []) (= y []))\n\
          \            []\n\
          \            (cons (cons (car x) (cons (car y) [])) (zip (cdr x) (cdr \
           y)))))" )
      ; ( "intersperse"
        , "(lambda (l e)\n\
          \  (if (= l []) []\n\
          \    (let xs (cdr l)\n\
          \      (if (= xs []) l\n\
          \        (cons (car l) (cons e (intersperse xs e)))))))" )
      ; ( "append"
        , "(lambda (l1 l2)\n\
          \  (if (= l1 []) l2\n\
          \    (if (= l2 []) l1\n\
          \      (cons (car l1) (append (cdr l1) l2)))))" )
      ; ( "reverse"
        , "(lambda (l)\n\
          \  (if (= l []) []\n\
          \    (append (reverse (cdr l)) [(car l)])))" )
      ; ( "concat"
        , "(lambda (l)\n\
          \  (if (= l []) []\n\
          \    (append (car l) (concat (cdr l)))))" )
      ; ("drop", "(lambda (l x)\n  (if (= x 0) l\n    (drop (cdr l) (- x 1))))")
      ; ( "sort"
        , "(lambda (l)\n\
          \  (if (= l []) []\n\
          \    (let p (car l)\n\
          \         (let lesser (filter (cdr l) (lambda (e) (< e p)))\n\
          \              (let greater (filter (cdr l) (lambda (e) (>= e p)))\n\
          \                   (append (sort lesser) (cons p (sort greater))))))))"
        )
      ; ( "dedup"
        , "(lambda (l)\n\
          \    (if (= l []) []\n\
          \      (if (= (cdr l) []) l\n\
          \        (let sl (sort l)\n\
          \             (let x1 (car sl)\n\
          \                  (let x2 (car (cdr sl))\n\
          \                       (if (= x1 x2) (dedup (cdr sl)) (cons x1 (dedup \
           (cdr sl))))))))))" ) ]
    |> List.map ~f:(fun (name, str) -> (name, Expr.of_string_exn str)) )

let matrix_of_texpr_list ~size (texprs : TypedExpr.t list) :
    TypedExpr.t Sstream.matrix =
  let init_sizes = List.map texprs ~f:(fun e -> (e, size e)) in
  let max_size =
    List.fold_left init_sizes ~init:0 ~f:(fun x (_, y) -> if x > y then x else y)
  in
  List.range ~stop:`inclusive 1 max_size
  |> List.map ~f:(fun s ->
         List.filter_map init_sizes ~f:(fun (e, s') ->
             if s = s' then Some e else None ) )
  |> Sstream.of_list

let arrow_error () = failwith "Operator is not of type Arrow_t."

let rec simple_enumerate ?(memo = SimpleMemoizer.empty ()) init :
    expr Sstream.matrix =
  let open Sstream in
  let init_matrix =
    matrix_of_texpr_list ~size:(fun e -> Expr.cost (TypedExpr.to_expr e)) init
    |> map_matrix ~f:TypedExpr.to_expr
  in
  let args_matrix num_args =
    let choose prev_args =
      slazy (fun () ->
          map_matrix
            (SimpleMemoizer.get memo init (fun () -> simple_enumerate ~memo init))
            ~f:(fun arg -> prev_args @ [arg]) )
    in
    match List.range 0 num_args with
    | _ :: xs ->
        (List.fold_left xs ~init:choose ~f:(fun acc _ -> compose acc choose)) []
    | [] -> failwith "Cannot generate args matrix with no arguments."
  in
  let callable_matrix cost apply_callable callable_typ =
    match callable_typ with
    | Arrow_t (arg_typs, _) ->
        let num_args = List.length arg_typs in
        let prefix = repeat_n (num_args + cost - 1) [] in
        let matrix =
          slazy (fun () -> map_matrix (args_matrix num_args) ~f:apply_callable)
        in
        concat prefix matrix
    | _ -> arrow_error ()
  in
  let op_matrix op op_typ =
    callable_matrix (Expr.Op.cost op) (fun args -> `Op (op, args)) op_typ
  in
  let apply_matrix func func_typ =
    callable_matrix 1 (fun args -> `Apply (func, args)) func_typ
  in
  let (op_matrices : expr matrix list) =
    List.map Expr.Op.all ~f:(fun op ->
        let meta = Expr.Op.meta op in
        op_matrix op meta.Expr.Op.typ )
  in
  let (apply_matrices : expr matrix list) =
    List.filter init ~f:(fun texpr ->
        match TypedExpr.to_type texpr with Arrow_t _ -> true | _ -> false )
    |> List.map ~f:(fun func ->
           apply_matrix (TypedExpr.to_expr func) (TypedExpr.to_type func) )
  in
  merge (init_matrix :: (op_matrices @ apply_matrices))

let rec enumerate ?(ops = default_ops) ?(memo = TypMemoizer.empty ()) config init
    typ : TypedExpr.t Sstream.matrix =
  let open Sstream in
  (* Init is finite, so we can construct an init stream by breaking
     init into a list of size classes and returning that list as a
     stream. *)
  let init_matrix =
    List.filter init ~f:(fun e -> is_unifiable typ (TypedExpr.to_type e))
    |> matrix_of_texpr_list ~size:(fun e -> Expr.cost (TypedExpr.to_expr e))
  in
  (* Generate an argument list matrix that conforms to the provided list of types. *)
  let args_matrix (arg_typs : typ list) =
    let choose (prev_args : TypedExpr.t list) : TypedExpr.t list matrix =
      (* Instantiate the argument types in the same context. Free
         type variables should be shared across arguments. For example,
         when instantiating the argument types for equals: (a, a) ->
         bool, both a's should map to the same free type. *)
      let arg_typs' =
        let ctx = Ctx.empty () in
        List.map arg_typs ~f:(instantiate ~ctx 0)
      in
      (* Split the argument type list into the types of the arguments
         that have already been selected and the head of the list of
         remaining types (which will be the type of the current
         argument). *)
      let prev_arg_typs, current_typ =
        match List.split_n arg_typs' (List.length prev_args) with
        | x, y :: _ -> (x, y)
        | x, y ->
            failwiths "No types remaining." (x, y)
              [%sexp_of: Type.t list * Type.t list]
      in
      (* Unify the types of the previous arguments with the actual
         selected types. By the size effects of unify, this should fill
         in any type variables in the current type that have already been
         bound. *)
      let prev_selected_typs =
        let ctx = Ctx.empty () in
        List.map prev_args ~f:(fun arg -> instantiate ~ctx 0 (TypedExpr.to_type arg))
      in
      List.iter2_exn prev_arg_typs prev_selected_typs ~f:unify_exn ;
      let current_typ' = normalize (generalize (-1) current_typ) in
      (* Generate the argument matrix lazily so that it will not be
         created until the prefix classes are exhausted. *)
      slazy (fun () ->
          map_matrix
            (TypMemoizer.get memo current_typ' (fun () ->
                 enumerate config ~memo init current_typ' ))
            ~f:(fun arg -> prev_args @ [arg]) )
    in
    match arg_typs with
    | _ :: xs ->
        (List.fold_left xs ~init:choose ~f:(fun acc _ -> compose acc choose)) []
    | [] -> failwith "Cannot generate args matrix with no arguments."
  in
  let callable_matrix cost apply_callable callable_typ =
    match callable_typ with
    | Arrow_t (arg_typs, ret_typ) ->
        let num_args = List.length arg_typs in
        let prefix = repeat_n (cost + num_args - 1) [] in
        let matrix =
          slazy (fun () ->
              map_matrix (args_matrix arg_typs) ~f:(apply_callable ret_typ) )
        in
        concat prefix matrix
    | _ -> arrow_error ()
  in
  let op_matrix op op_typ =
    callable_matrix (Expr.Op.cost op)
      (fun ret_typ args -> TypedExpr.Op ((op, args), ret_typ))
      op_typ
  in
  let apply_matrix func func_typ =
    callable_matrix 1
      (fun ret_typ args -> TypedExpr.Apply ((func, args), ret_typ))
      func_typ
  in
  (* The op stream is infinite, so it needs more careful handling. *)
  let op_matrices =
    List.map ops ~f:(fun op -> (op, Expr.Op.meta op))
    (* Filter all operators that can return the correct type. *)
    |> List.filter ~f:(fun (_, meta) ->
           match meta.Expr.Op.typ with
           | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
           | _ -> arrow_error () )
    (* Unify the return type of the operator with the input type. By
       the side effects of unify, all the other free type variables in
       the operator type will reflect the substitution. Now we have
       correct types for the arguments. *)
    |> List.map ~f:(fun (op, meta) ->
           match (instantiate 0 typ, instantiate 0 meta.Expr.Op.typ) with
           | typ', (Arrow_t (_, ret_typ) as op_typ) ->
               unify_exn typ' ret_typ ;
               (op, normalize (generalize (-1) op_typ))
           | _ -> arrow_error () )
    (* Generate a matrix for each operator. *)
    |> List.map ~f:(fun (op, op_typ) -> op_matrix op op_typ)
  in
  let apply_matrices =
    init
    |> List.filter ~f:(fun texpr ->
           match TypedExpr.to_type texpr with
           | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
           | _ -> false )
    |> List.map ~f:(fun texpr ->
           match (instantiate 0 typ, instantiate 0 (TypedExpr.to_type texpr)) with
           | typ', (Arrow_t (_, ret_typ) as func_typ) ->
               unify_exn typ' ret_typ ;
               (texpr, normalize (generalize (-1) func_typ))
           | _ -> arrow_error () )
    |> List.map ~f:(fun (func, func_typ) -> apply_matrix func func_typ)
  in
  merge (init_matrix :: (op_matrices @ apply_matrices))
  |> map
       ~f:
         (List.filter ~f:(fun x ->
              let e = TypedExpr.to_expr x in
              if config.deduction then
                match Rewrite.simplify (List.map init ~f:TypedExpr.to_expr) e with
                | Some e' -> Expr.cost e' >= Expr.cost e
                | None -> false
              else true ))

type hypothesis = {skel: Spec.t; max_exh_cost: int; generalized: bool}

let solve_single ?(init = []) ?(verify = Verify.verify_examples ~ctx:(Ctx.empty ()))
    ~config (examples : example list) =
  let initial_spec =
    let target_name = Example.name examples in
    let target ctx expr =
      let body = Ctx.lookup_exn ctx target_name in
      `Let (target_name, body, expr)
    in
    { Spec.target
    ; Spec.holes=
        Ctx.of_alist_exn
          [ ( target_name
            , { examples= List.map examples ~f:(fun ex -> (ex, Ctx.empty ()))
              ; signature= Example.signature examples
              ; tctx= Ctx.empty () } ) ]
    ; Spec.cost= 0 }
  in
  let generate_specs (specs : Spec.t list) : Spec.t list =
    let cost = if config.flat_cost then Cost.flat else Cost.default in
    List.concat_map specs ~f:(fun parent ->
        Spec.map_bodies ~deduce_examples:config.deduction ~cost parent
        @ Spec.filter_bodies ~deduce_examples:config.deduction ~cost parent
        @ Spec.fold_bodies ~deduce_examples:config.deduction
            ~infer_base:config.infer_base ~cost parent
        @ Spec.foldt_bodies ~deduce_examples:config.deduction
            ~infer_base:config.infer_base ~cost parent
        (* @ (Spec.recurs_bodies ~deduce_examples:config.deduction parent) *) )
  in
  let matrix_of_hole hole =
    let init' =
      ( Ctx.to_alist hole.tctx
      |> List.map ~f:(fun (name, typ) -> TypedExpr.Id (name, typ)) )
      @ init
    in
    match hole.signature with
    | Arrow_t (arg_typs, ret_typ) ->
        let args = List.map arg_typs ~f:(fun typ -> (Fresh.name "x", typ)) in
        let arg_names, _ = List.unzip args in
        let init'' =
          init' @ List.map args ~f:(fun (name, typ) -> TypedExpr.Id (name, typ))
        in
        if config.untyped then
          simple_enumerate init''
          |> Sstream.map_matrix ~f:(fun expr -> `Lambda (arg_names, expr))
        else
          enumerate config init'' ret_typ
          |> Sstream.map_matrix ~f:(fun texpr ->
                 `Lambda (arg_names, TypedExpr.to_expr texpr) )
    | typ ->
        if config.untyped then simple_enumerate init'
        else enumerate config init' typ |> Sstream.map_matrix ~f:TypedExpr.to_expr
  in
  let choose name hole ctx : expr Ctx.t Sstream.matrix =
    Sstream.map_matrix (matrix_of_hole hole) ~f:(Ctx.bind ctx name)
  in
  let total_cost =
    if config.flat_cost then fun hypo_cost enum_cost -> hypo_cost + enum_cost
    else fun hypo_cost enum_cost ->
      hypo_cost + Int.of_float (1.5 ** Float.of_int enum_cost)
  in
  let solver_of_spec spec =
    let matrix =
      match Ctx.to_alist spec.Spec.holes with
      | [] -> failwith "Specification has no holes."
      | (name, hole) :: hs ->
          (List.fold_left hs ~init:(choose name hole)
             ~f:(fun matrix (name', hole') ->
               Sstream.compose matrix (choose name' hole') ))
            (Ctx.empty ())
    in
    Sstream.map_matrix matrix ~f:(fun ctx ->
        let target = spec.Spec.target ctx in
        log config.verbosity 2
          (sprintf "Examined %s." (Expr.to_string (target (`Id "_")))) ;
        if verify target examples then Some target else None )
  in
  (* Search a spec up to a specified maximum cost. The amount of
     exhaustive search that this involves depends on the cost of the
     hypothesis. *)
  let search max_cost spec : (expr -> expr) option =
    let solver = solver_of_spec spec in
    let rec search' (exh_cost : int) : (expr -> expr) option =
      if total_cost spec.Structure.Spec.cost exh_cost >= max_cost then (
        if exh_cost > 0 then
          log config.verbosity 1
            (sprintf "Searched %s to exhaustive cost %d." (Spec.to_string spec)
               exh_cost) ;
        None )
      else
        let row = Sstream.next solver in
        match List.find_map row ~f:ident with
        | Some result -> Some result
        | None -> search' (exh_cost + 1)
    in
    search' 0
  in
  let rec search_unbounded (cost : int) (hypos : hypothesis list) =
    let can_search hypo =
      total_cost hypo.skel.Structure.Spec.cost (hypo.max_exh_cost + 1) <= cost
    in
    log config.verbosity 1 (sprintf "Searching up to cost %d." cost) ;
    let m_result =
      List.find_map hypos ~f:(fun hypo ->
          (* Check whether it is possible to search more than has been
           searched with the current cost. Since the total cost can be
           non-linear, this must be explicitly checked. *)
          if can_search hypo then search cost hypo.skel else None )
    in
    match m_result with
    | Some result -> result
    | None ->
        let hypos =
          List.map hypos ~f:(fun h ->
              if can_search h then {h with max_exh_cost= h.max_exh_cost + 1} else h
          )
        in
        let generalizable, rest =
          List.partition_tf hypos ~f:(fun h ->
              (not h.generalized) && total_cost h.skel.Structure.Spec.cost 0 < cost
          )
        in
        let new_hypos =
          List.map generalizable ~f:(fun h -> h.skel)
          |> generate_specs
          |> List.map ~f:(fun s -> {skel= s; max_exh_cost= 0; generalized= false})
        in
        search_unbounded (cost + 1)
          ( new_hypos @ rest
          @ List.map generalizable ~f:(fun h -> {h with generalized= true}) )
  in
  search_unbounded 1 [{skel= initial_spec; max_exh_cost= 0; generalized= false}]

let solve ?(config = default_config) ?(bk = []) ?(init = default_init) examples =
  (* Check examples. *)
  if not (List.map examples ~f:(fun ex -> (ex, Ctx.empty ())) |> Example.check) then
    failwith "Examples do not represent a function." ;
  let tctx =
    List.fold_left bk ~init:(Ctx.empty ()) ~f:(fun ctx (name, impl) ->
        Ctx.bind ctx name (TypedExpr.to_type (infer_exn ctx impl)) )
  in
  let vctx =
    List.fold_left bk ~init:default_stdlib ~f:(fun ctx (name, impl) ->
        Ctx.bind ctx name (`Closure (impl, ctx)) )
  in
  let init =
    init
    @ ( Ctx.to_alist tctx
      |> List.map ~f:(fun (name, typ) -> TypedExpr.Id (name, typ)) )
  in
  let verify ?(limit = 100) target examples =
    try
      match target (`Id "_") with
      | `Let (name, body, _) ->
          let _ = infer (Ctx.bind tctx name (fresh_free 0)) body in
          Verify.verify_examples ~limit ~ctx:vctx target examples
      | _ -> failwith "Bad result from solve_single."
    with
    | TypeError _ -> false
    | Ctx.UnboundError _ -> false
  in
  Ctx.bind (Ctx.empty ()) (Example.name examples)
    ((solve_single ~init ~verify ~config examples) (`Id "_"))
