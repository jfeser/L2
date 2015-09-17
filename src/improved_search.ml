open Core.Std

open Ast
open Collections
open Infer
open Util

module Symbol = struct
  type t = {
    id : int;
    name : string;
  } with compare, sexp

  let to_sexp = sexp_of_t
  let of_sexp = t_of_sexp

  let equal s1 s2 = compare s1 s2 = 0

  let counter = ref 0

  let create name = begin
    incr counter;
    { id = !counter; name }
  end
end

module StaticDistance = struct
  module T = struct
    type t = int * int with compare, sexp
    let compare = compare_t
  end

  include T

  let increment_scope x =
    let (a, b) = x in
    (a + 1, b)

  module Map = struct
    include Map.Make(T)

    let increment_scope x =
      to_alist x
      |> List.map ~f:(fun (k, v) -> (increment_scope k, v))
      |> of_alist_exn
  end

  let create distance index =
    if distance <= 0 || index <= 0 then raise (Invalid_argument "Argument out of range.") else
      (distance, index)

  let distance x = let (a, b) = x in a
  let index x = let (a, b) = x in b

  let args num =
    List.range ~stride:1 ~start:`inclusive ~stop:`inclusive 1 num
    |> List.map ~f:(fun i -> (1, i))

  let to_string x =
    let (a, b) = x in
    sprintf "%d_%d" a b
end

module Hole = struct
  type t = {
    id  : int;
    ctx : Type.t StaticDistance.Map.t;
    type_ : Type.t;
    symbol : Symbol.t;
  } with compare, sexp

  let to_sexp = sexp_of_t
  let of_sexp = t_of_sexp
  let compare_id h1 h2 = Int.compare h1.id h2.id

  let counter = ref 0

  let equal h1 h2 = h1.id = h2.id

  let to_string h = Sexp.to_string_hum (to_sexp h)

  let create ctx type_ symbol = begin
    incr counter;
    { id = !counter; ctx; type_; symbol }
  end

  let apply_unifier u h =
    {
      h with
      ctx = StaticDistance.Map.map h.ctx ~f:(Unifier.apply u);
      type_ = Unifier.apply u h.type_;
    }
end

module Skeleton = struct
  type id =
    | StaticDistance of StaticDistance.t
    | Name of string
  with compare, sexp

  type 'a t =
    | Num_h of int * 'a
    | Bool_h of bool * 'a
    | List_h of 'a t list * 'a
    | Tree_h of 'a t Tree.t * 'a
    | Id_h of id * 'a
    | Let_h of ('a t * 'a t) * 'a
    | Lambda_h of (int * 'a t) * 'a
    | Apply_h of ('a t * ('a t list)) * 'a
    | Op_h of (op * ('a t list)) * 'a
    | Hole_h of Hole.t * 'a
  with compare, sexp

  let of_sexp = t_of_sexp
  let to_sexp = sexp_of_t

  let rec to_string_hum s =
    let ts = to_string_hum in
    let list_to_string l : string = String.concat ~sep:" " (List.map ~f:ts l) in
    match s with
    | Num_h (x, _) -> Int.to_string x
    | Bool_h (true, _) -> "#t"
    | Bool_h (false, _) -> "#f"
    | Id_h (StaticDistance x, _) -> StaticDistance.to_string x
    | Id_h (Name x, _) -> x
    | List_h (x, _) -> sprintf "[%s]" (list_to_string x)
    | Tree_h (x, _) -> Tree.to_string x ~str:ts
    | Op_h ((op, args), _) -> sprintf "(%s %s)" (Expr.Op.to_string op) (list_to_string args)
    | Let_h ((bound, body), _) -> sprintf "(let *1* %s %s)" (ts bound) (ts body)
    | Apply_h ((x, y), _) -> sprintf "(%s %s)" (ts x) (list_to_string y)
    | Lambda_h ((num_args, body), _) -> sprintf "(lambda *%d* %s)" num_args (ts body)
    | Hole_h (h, _) -> sprintf "?%d" h.Hole.id

  let to_expr ?(ctx = StaticDistance.Map.empty) ?(fresh_name) (f: Hole.t -> Expr.t) (s: 'a t) : Expr.t =
    let fresh_name = match fresh_name with
      | Some fresh -> fresh
      | None -> Fresh.mk_fresh_name_fun ()
    in
    let rec to_expr ctx s =
      match s with
      | Num_h (x, _) -> `Num x
      | Bool_h (x, _) -> `Bool x
      | Id_h (StaticDistance x, _) ->
        (match StaticDistance.Map.find ctx x with
         | Some name -> `Id name
         | None ->
           failwiths "Context does not contain coordinate." (s, x, ctx)
             (Tuple.T3.sexp_of_t
                (sexp_of_t (fun _ -> Sexp.Atom "?"))
                StaticDistance.sexp_of_t
                (StaticDistance.Map.sexp_of_t String.sexp_of_t)))
      | Id_h (Name x, _) -> `Id x
      | List_h (elems, _) -> `List (List.map elems ~f:(to_expr ctx))
      | Tree_h (elems, _) -> `Tree (Tree.map elems ~f:(to_expr ctx))
      | Let_h ((bound, body), _) ->
        let name = fresh_name () in
        let ctx =
          StaticDistance.Map.increment_scope ctx |> Map.add ~key:(StaticDistance.create 1 1) ~data:name
        in
        `Let (name, to_expr ctx bound, to_expr ctx body)
      | Lambda_h ((num_args, body), _) ->
        let ctx = StaticDistance.Map.increment_scope ctx in
        let arg_names = List.init num_args ~f:(fun _ -> fresh_name ()) in
        let ctx = List.fold (List.zip_exn arg_names (StaticDistance.args num_args)) ~init:ctx
            ~f:(fun ctx (name, sd) -> Map.add ctx ~key:sd ~data:name)
        in
        `Lambda (arg_names, to_expr ctx body)
      | Apply_h ((func, args), _) -> `Apply (to_expr ctx func, List.map ~f:(to_expr ctx) args)
      | Op_h ((op, args), _) -> `Op (op, List.map ~f:(to_expr ctx) args)
      | Hole_h (x, _) -> f x
    in
    to_expr ctx s

  let to_expr_exn ?(ctx = StaticDistance.Map.empty) ?(fresh_name) s =
    match fresh_name with
    | Some fresh ->
      to_expr ~ctx ~fresh_name:fresh
        (fun _ -> failwith "Tried to convert skeleton with holes to expression.") s
    | None -> to_expr ~ctx (fun _ -> failwith "Tried to convert skeleton with holes to expression.") s

  let compare = compare_t
  let hash = Hashtbl.hash

  let rec fill_hole hole ~parent:p ~child:c =
    let f p' = fill_hole hole ~child:c ~parent:p' in
    match p with
    | Num_h _
    | Bool_h _
    | Id_h _ -> p
    | Hole_h (h, s) -> if Hole.equal h hole then c else p
    | List_h (x, s) -> List_h (List.map ~f:f x, s)
    | Tree_h (x, s) -> Tree_h (Tree.map ~f:f x, s)
    | Let_h ((x, y), s) -> Let_h ((f x, f y), s)
    | Lambda_h ((x, y), s) -> Lambda_h ((x, f y), s)
    | Apply_h ((x, y), s) -> Apply_h ((f x, List.map ~f:f y), s)
    | Op_h ((x, y), s) -> Op_h ((x, List.map ~f:f y), s)

  let annotation = function
    | Num_h (_, a)
    | Bool_h (_, a)
    | Id_h (_, a)
    | List_h (_, a)
    | Tree_h (_, a)
    | Let_h (_, a)
    | Lambda_h (_, a)
    | Apply_h (_, a)
    | Op_h (_, a)
    | Hole_h (_, a) -> a

  let rec map ~f s = match s with
    | Num_h _
    | Bool_h _
    | Id_h _
    | Hole_h _ -> f s
    | List_h (x, a) -> f (List_h (List.map ~f:(map ~f:f) x, a))
    | Tree_h (x, a) -> f (Tree_h (Tree.map ~f:(map ~f:f) x, a))
    | Let_h ((bound, body), a) -> f (Let_h ((map ~f:f bound, map ~f:f body), a))
    | Lambda_h ((args, body), a) -> f (Lambda_h ((args, map ~f:f body), a))
    | Apply_h ((func, args), a) -> f (Apply_h ((map ~f:f func, List.map ~f:(map ~f:f) args), a))
    | Op_h ((op, args), a) -> f (Op_h ((op, List.map ~f:(map ~f:f) args), a))

  let is_simplifiable base s =
    let e = to_expr (fun h -> `Id (sprintf "h%d" h.Hole.id)) s in
    Rewrite.is_redundant base e
end

module Specification = struct
  module T = struct
    type t =
      | Bottom
      | Top
      | Examples of (value StaticDistance.Map.t * value) list
      | FunctionExamples of (value StaticDistance.Map.t * value list * value) list
    with compare, sexp

    let hash = Hashtbl.hash
    let compare = compare_t
  end

  include T
  include Hashable.Make(T)

  let of_sexp = t_of_sexp
  let to_sexp = sexp_of_t

  let to_string s = Sexp.to_string (to_sexp s)

  let verify spec skel = begin
    match spec with
    | Top -> true
    | Bottom -> false
    | Examples exs ->
      (try
         List.for_all exs ~f:(fun (in_ctx, out) ->
             let fresh_name = Fresh.mk_fresh_name_fun () in
             let name_ctx = StaticDistance.Map.map in_ctx ~f:(fun _ -> fresh_name ()) in
             let expr = Skeleton.to_expr_exn ~ctx:name_ctx ~fresh_name skel in
             let value_ctx =
               StaticDistance.Map.to_alist in_ctx
               |> List.map ~f:(fun (k, v) -> StaticDistance.Map.find_exn name_ctx k, v)
               |> Ctx.of_alist_exn
               |> Ctx.merge_right Eval.stdlib_vctx
             in
             Eval.eval value_ctx expr = out)
       with Eval.RuntimeError _ -> false)
    | FunctionExamples exs ->
      (try
         List.for_all exs ~f:(fun (in_ctx, in_args, out) ->
             let fresh_name = Fresh.mk_fresh_name_fun () in
             let name_ctx = StaticDistance.Map.map in_ctx ~f:(fun _ -> fresh_name ()) in
             let expr = Skeleton.to_expr_exn ~ctx:name_ctx ~fresh_name skel in
             let value_ctx =
               StaticDistance.Map.to_alist in_ctx
               |> List.map ~f:(fun (k, v) -> StaticDistance.Map.find_exn name_ctx k, v)
               |> Ctx.of_alist_exn
               |> Ctx.merge_right Eval.stdlib_vctx
             in
             Eval.eval value_ctx (`Apply (expr, List.map in_args ~f:Expr.of_value)) = out)
       with Eval.RuntimeError _ -> false)
  end

  let increment_scope spec =
    match spec with
    | Bottom
    | Top -> spec
    | Examples exs ->
      let exs =
        List.map exs ~f:(fun (in_ctx, out) ->
            let in_ctx =
              StaticDistance.Map.to_alist in_ctx
              |> List.map ~f:(fun (k, v) -> (StaticDistance.increment_scope k, v))
              |> StaticDistance.Map.of_alist_exn
            in
            (in_ctx, out))
      in
      Examples exs
    | FunctionExamples exs ->
      let exs =
        List.map exs ~f:(fun (in_ctx, in_args, out) ->
            let in_ctx =
              StaticDistance.Map.to_alist in_ctx
              |> List.map ~f:(fun (k, v) -> (StaticDistance.increment_scope k, v))
              |> StaticDistance.Map.of_alist_exn
            in
            (in_ctx, in_args, out))
      in
      FunctionExamples exs
end

module type CostModel_Intf = sig
  val id_cost : id -> int
  val op_cost : Expr.Op.t -> int
end

module Hypothesis = struct
  module H = struct
    type skeleton = Specification.t Skeleton.t

    module Table = Hashcons.Make(struct
        type t = skeleton
        let equal h1 h2 = Skeleton.compare Specification.compare h1 h2 = 0
        let hash = Skeleton.hash
      end)

    type kind =
      | Abstract
      | Concrete
    with sexp

    type t = {
      skeleton : skeleton Hashcons.hash_consed;
      cost : int;
      kind : kind;
      holes : (Hole.t * Specification.t) list;
    }

    let table = Table.create 100

    let sexp_of_t h =
      let open Sexp in
      List [
        List [ Atom "skeleton"; Skeleton.to_sexp Specification.to_sexp h.skeleton.Hashcons.node ];
        List [ Atom "cost"; sexp_of_int h.cost ];
        List [ Atom "kind"; sexp_of_kind h.kind ];
        List [
          Atom "holes";
          sexp_of_list (fun (hole, spec) -> List [ Hole.to_sexp hole; Specification.to_sexp spec ]) h.holes
        ];
      ]

    let t_of_sexp s =
      let open Sexp in
      match s with
      | List [
          List [ Atom "skeleton"; skel_s ];
          List [ Atom "cost"; cost_s ];
          List [ Atom "kind"; kind_s ];
          List [ Atom "holes"; holes_s ];
        ] -> {
          skeleton = Table.hashcons table (Skeleton.of_sexp Specification.of_sexp skel_s);
          cost = Int.t_of_sexp cost_s;
          kind = kind_of_sexp kind_s;
          holes = List.t_of_sexp (Tuple2.t_of_sexp Hole.of_sexp Specification.of_sexp) holes_s;
        }
      | _ -> raise (Sexp.Of_sexp_error (Failure "Sexp has the wrong format.", s))

    let to_sexp = sexp_of_t
    let of_sexp = t_of_sexp

    let compare_cost h1 h2 = Int.compare h1.cost h2.cost

    let spec h : Specification.t = Skeleton.annotation h.skeleton.Hashcons.node

    let to_expr (h: t) : Expr.t =
      match h.kind with
      | Abstract -> failwith "Tried to convert an abstract hypothesis to an expression."
      | Concrete -> Skeleton.to_expr_exn (h.skeleton.Hashcons.node)

    let to_string h = Sexp.to_string_hum (to_sexp h)
    let to_string_hum h = Skeleton.to_string_hum (h.skeleton.Hashcons.node)

    let apply_unifier h u =
      {
        h with
        holes = List.map h.holes ~f:(fun (h, s) -> (Hole.apply_unifier u h, s));
        skeleton = Table.hashcons table
            (Skeleton.map h.skeleton.Hashcons.node ~f:(function
                 | Skeleton.Hole_h (h, a) -> Skeleton.Hole_h (Hole.apply_unifier u h, a)
                 | s -> s))
      }

    let fill_hole hole ~parent:p ~child:c = begin
      if not (List.exists p.holes ~f:(fun (h, _) -> Hole.equal h hole)) then
        failwith "Hypothesis does not contain the specified hole.";
      let holes =
        (List.filter p.holes ~f:(fun (h, _) -> not (Hole.equal h hole))) @ c.holes
      in
      {
        skeleton =
          Table.hashcons table
            (Skeleton.fill_hole hole
               ~parent:p.skeleton.Hashcons.node ~child:c.skeleton.Hashcons.node);
        cost = p.cost + c.cost;
        kind = if List.length holes = 0 then Concrete else Abstract;
        holes;
      }
    end

    let verify h = Specification.verify (spec h) h.skeleton.Hashcons.node

    let num x s : t = {
      skeleton = Table.hashcons table (Skeleton.Num_h (x, s));
      cost = 1;
      kind = Concrete;
      holes = [];
    }
    let bool x s : t = {
      skeleton = Table.hashcons table (Skeleton.Bool_h (x, s));
      cost = 1;
      kind = Concrete;
      holes = [];
    }
    let id_sd x s : t = {
      skeleton = Table.hashcons table (Skeleton.Id_h (Skeleton.StaticDistance x, s));
      cost = 1;
      kind = Concrete;
      holes = [];
    }
    let hole x s : t = {
      skeleton = Table.hashcons table (Skeleton.Hole_h (x, s));
      cost = 0;
      kind = Abstract;
      holes = [ (x, s) ];
    }
    let list (x: t list) s : t = {
      skeleton = Table.hashcons table
          (Skeleton.List_h (List.map x ~f:(fun h -> h.skeleton.Hashcons.node), s));
      cost = 1 + List.int_sum (List.map x ~f:(fun h -> h.cost));
      kind = if List.exists x ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat (List.map x ~f:(fun h -> h.holes));
    }
    let tree x s : t =
      let flat = Tree.flatten x in
      {
        skeleton = Table.hashcons table
            (Skeleton.Tree_h (Tree.map x ~f:(fun h -> h.skeleton.Hashcons.node), s));
        cost = 1 + List.int_sum (List.map flat ~f:(fun h -> h.cost));
        kind = if List.exists flat ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
        holes = List.concat (List.map (Tree.flatten x) ~f:(fun h -> h.holes));
      }
    let _let x s : t =
      let (bound, body) = x in
      {
        skeleton = Table.hashcons table
            (Skeleton.Let_h ((bound.skeleton.Hashcons.node, body.skeleton.Hashcons.node), s));
        cost = 1 + bound.cost + body.cost;
        kind = if bound.kind = Abstract || body.kind = Abstract then Abstract else Concrete;
        holes = bound.holes @ body.holes;
      }
    let lambda x s : t =
      let (num_args, body) = x in
      {
        skeleton = Table.hashcons table
            (Skeleton.Lambda_h ((num_args, body.skeleton.Hashcons.node), s));
        cost = 1 + body.cost;
        kind = if body.kind = Abstract then Abstract else Concrete;
        holes = body.holes;
      }
    let apply x s : t =
      let (func, args) = x in
      {
        skeleton = Table.hashcons table
            (Skeleton.Apply_h
               ((func.skeleton.Hashcons.node,
                 List.map args ~f:(fun h -> h.skeleton.Hashcons.node)), s));
        cost = 1 + func.cost + List.int_sum (List.map args ~f:(fun h -> h.cost));
        kind =
          if func.kind = Abstract || List.exists args ~f:(fun h -> h.kind = Abstract) then
            Abstract else Concrete;
        holes = func.holes @ (List.concat (List.map args ~f:(fun h -> h.holes)));
      }
  end

  module Make (CostModel : CostModel_Intf) = struct
    include H

    let id_name x s : t = {
      skeleton = Table.hashcons table (Skeleton.Id_h (Skeleton.Name x, s));
      cost = CostModel.id_cost x;
      kind = Concrete;
      holes = [];
    }
    let op x s : t =
      let (op, args) = x in
      {
        skeleton = Table.hashcons table
            (Skeleton.Op_h ((op, List.map args ~f:(fun h -> h.skeleton.Hashcons.node)), s));
        cost = CostModel.op_cost op + List.int_sum (List.map args ~f:(fun h -> h.cost));
        kind = if List.exists args ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
        holes = List.concat (List.map args ~f:(fun h -> h.holes));
      }
  end

  include H
end

module type Generalizer_intf = sig
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list
  val generalize : t
  val generalize_all : generalize:t -> Hypothesis.t -> Hypothesis.t list
end

module Generalizer_impl = struct
  type t = Hole.t -> Specification.t -> (Hypothesis.t * Unifier.t) list

  let generalize_all ~generalize:gen hypo =
    let open Hypothesis in
    List.fold_left
      (List.sort ~cmp:(fun (h1, _) (h2, _) -> Hole.compare_id h1 h2) hypo.holes)
      ~init:[ hypo ]
      ~f:(fun hypos (hole, spec) ->
          let children = List.filter (gen hole spec) ~f:(fun (c, u) ->
              c.kind = Abstract || Specification.verify spec c.Hypothesis.skeleton.Hashcons.node)
          in
          List.map hypos ~f:(fun p -> List.map children ~f:(fun (c, u) ->
              apply_unifier (fill_hole hole ~parent:p ~child:c) u))
          |> List.concat)
end

module L2_CostModel : CostModel_Intf = struct
  let id_cost = function
    | "foldr"
    | "foldl"
    | "foldt" -> 3
    | "map"
    | "mapt"
    | "filter" -> 2
    | _ -> 1

  let op_cost = Expr.Op.cost
end

module L2_Generalizer = struct
  include Generalizer_impl

  (* This generalizer generates programs of the following form. Each
     hole in the hypotheses that it returns is tagged with a symbol
     name that the generalizer uses to select the hypotheses that can
     be used to fill that hole later.

     L := fun x_1 ... x_n -> E

     E := map I (L)
        | filter I (L)
        | foldl I (L) C
        | ...
        | E'

     E' := car E'
         | cdr E'
         | cons E' E'
         | ...
         | C

     C := 0
        | 1
        | []
        | ...

     I := <identifier in current scope>
  *)

  module type Symbols_intf = sig
    val lambda : Symbol.t
    val combinator : Symbol.t
    val expression : Symbol.t
    val constant : Symbol.t
    val identifier : Symbol.t
  end

  module Make (Symbols : Symbols_intf) = struct
    module H = Hypothesis.Make(L2_CostModel)

    include Symbols

    let combinators = [
      "map"; "mapt"; "filter"; "foldl"; "foldr"; "foldt"; "rec"
    ]
    let functions = Ctx.filter Infer.stdlib_tctx ~f:(fun ~key:k ~data:v ->
        not (List.mem ~equal:String.equal combinators k))

    let generate_constants hole spec =
      let constants = [
        Type.num, [
          H.num 0 spec;
          H.num 1 spec;
          H.num Int.max_value spec;
        ];
        Type.bool, [
          H.bool true spec;
          H.bool false spec;
        ];
        Type.list (Type.quant "a") |> instantiate 0, [
          H.list [] spec;
        ]
      ] in
      List.concat_map constants ~f:(fun (t, xs) ->
          match Infer.Unifier.of_types hole.Hole.type_ t with
          | Some u -> List.map xs ~f:(fun x -> (x, u))
          | None -> [])

    let generate_identifiers hole spec =
      List.filter_map (StaticDistance.Map.to_alist hole.Hole.ctx) ~f:(fun (id, id_t) ->
          Option.map (Unifier.of_types hole.Hole.type_ id_t) ~f:(fun u ->
              H.id_sd id spec, u))

    let generate_expressions hole spec =
      let op_exprs = List.filter_map Expr.Op.all ~f:(fun op ->
          let op_t = instantiate 0 (Expr.Op.meta op).Expr.Op.typ in
          match op_t with
          | Arrow_t (args_t, ret_t) ->
            (* Try to unify the return type of the operator with the type of the hole. *)
            Option.map (Unifier.of_types hole.Hole.type_ ret_t) ~f:(fun u ->
                (* If unification succeeds, apply the unifier to the rest of the type. *)
                let args_t = List.map args_t ~f:(Unifier.apply u) in
                let arg_holes = List.map args_t ~f:(fun t ->
                    H.hole (Hole.create hole.Hole.ctx t expression) Specification.Top)
                in
                H.op (op, arg_holes) spec, u)
          | _ -> None)
      in
      let apply_exprs = List.filter_map (Ctx.to_alist functions) ~f:(fun (func, func_t) ->
          let func_t = instantiate 0 func_t in
          match func_t with
          | Arrow_t (args_t, ret_t) ->
            (* Try to unify the return type of the operator with the type of the hole. *)
            Option.map (Unifier.of_types hole.Hole.type_ ret_t) ~f:(fun u ->
                (* If unification succeeds, apply the unifier to the rest of the type. *)
                let args_t = List.map args_t ~f:(Unifier.apply u) in
                let arg_holes = List.map args_t ~f:(fun t ->
                    H.hole (Hole.create hole.Hole.ctx t expression) Specification.Top)
                in
                H.apply (H.id_name func Specification.Top, arg_holes) spec, u)
          | _ -> None)
      in
      op_exprs @ apply_exprs

    let generate_lambdas hole spec =
      match hole.Hole.type_ with
      (* If the hole has an arrow type, generate a lambda expression with
         the right number of arguments and push the specification down. *)
      | Arrow_t (args_t, ret_t) ->
        let num_args = List.length args_t in
        let arg_names = StaticDistance.args num_args in

        (* The lambda introduces a new scope, so remember to increment
           the scope of the parent specification. *)
        let hole_spec = match Specification.increment_scope spec with
          | Specification.FunctionExamples exs ->
            let hole_exs = List.map exs ~f:(fun (in_ctx, in_args, out) ->
                let value_ctx = StaticDistance.Map.of_alist_exn (List.zip_exn arg_names in_args) in
                let in_ctx =
                  StaticDistance.Map.merge value_ctx in_ctx ~f:(fun ~key:k v ->
                      match v with
                      | `Both (x, _)
                      | `Left x
                      | `Right x -> Some x)
                in
                (in_ctx, out))
            in
            Specification.Examples hole_exs
          | Specification.Bottom -> Specification.Bottom
          | _ -> Specification.Top
        in
        let type_ctx =
          List.fold (List.zip_exn arg_names args_t) ~init:(StaticDistance.Map.increment_scope hole.Hole.ctx)
            ~f:(fun ctx (arg, arg_t) -> StaticDistance.Map.add ctx ~key:arg ~data:arg_t)
        in
        let lambda =
          H.lambda (num_args, H.hole (Hole.create type_ctx ret_t combinator) hole_spec) spec
        in
        [ lambda, Unifier.empty ]
      | _ -> []

    let generate_combinators hole spec =
      
      List.filter_map (Ctx.to_alist Infer.stdlib_tctx) ~f:(fun (func, func_t) ->
          if List.mem ~equal:String.equal combinators func then
            let func_t = instantiate 0 func_t in
            match func_t with
            | Arrow_t (args_t, ret_t) ->
              (* Try to unify the return type of the operator with the type of the hole. *)
              Option.map (Unifier.of_types ret_t hole.Hole.type_) ~f:(fun u ->
                  (* If unification succeeds, apply the unifier to the rest of the type. *)
                  let args_t = List.map args_t ~f:(Infer.Unifier.apply u) in
                  let arg_holes = match (func, args_t) with
                    | "map", [ t1; t2 ] | "mapt", [ t1; t2 ] | "filter", [ t1; t2 ] -> [
                        H.hole (Hole.create hole.Hole.ctx t1 identifier) Specification.Top;
                        H.hole (Hole.create hole.Hole.ctx t2 lambda) Specification.Top;
                      ]
                    | "foldr", [ t1; t2; t3 ] | "foldl", [ t1; t2; t3 ] | "foldt", [ t1; t2; t3 ] -> [
                        H.hole (Hole.create hole.Hole.ctx t1 identifier) Specification.Top;
                        H.hole (Hole.create hole.Hole.ctx t2 lambda) Specification.Top;
                        H.hole (Hole.create hole.Hole.ctx t3 constant) Specification.Top;
                      ]
                    | name, _ -> failwith (sprintf "Unexpected combinator name: %s" name)
                  in
                  H.apply (H.id_name func Specification.Top, arg_holes) spec, u)
            | _ -> None
          else None)

    let select_generators symbol =
      if symbol = constant then
        [ generate_constants ]
      else if symbol = identifier then
        [ generate_identifiers ]
      else if symbol = lambda then
        [ generate_lambdas ]
      else if symbol = expression then
        [ generate_expressions; generate_identifiers; generate_constants ]
      else if symbol = combinator then
        [ generate_combinators; generate_expressions; generate_constants ]
      else
        failwiths "Unknown symbol type." symbol Symbol.to_sexp

    let generalize hole spec =
      let generators = select_generators hole.Hole.symbol in
      List.concat (List.map generators ~f:(fun g -> g hole spec))
  end

  include Make (struct
      let lambda = Symbol.create "Lambda"
      let combinator = Symbol.create "Combinator"
      let expression = Symbol.create "Expression"
      let constant = Symbol.create "Constant"
      let identifier = Symbol.create "Identifier"
    end)
end

module type Synthesizer_intf = sig
  type result =
    | Solution of Hypothesis.t
    | NoSolution

  val synthesize : Hypothesis.t -> result
end

module Make_BFS_Synthesizer (G: Generalizer_intf) : Synthesizer_intf = struct
  type result =
    | Solution of Hypothesis.t
    | NoSolution

  exception SynthesisException of result

  let synthesize hypo =
    let base_terms = [
      `Num 0; `Num 1; `Num Int.max_value; `Bool true; `Bool false; `List []
    ] in
    let open Hypothesis in
    let heap = Heap.create ~cmp:compare_cost () in
    try
      Heap.add heap hypo;
      while true do
        match Heap.pop heap with
        | Some h ->
          (* Take the hole with the smallest id. *)
          let m_hole =
            List.min_elt h.holes ~cmp:(fun (h1, _) (h2, _) -> Int.compare h1.Hole.id h2.Hole.id)
          in
          (match m_hole with
           | Some (hole, spec) ->
             List.iter (G.generalize hole spec) ~f:(fun (c, u) ->
                 if c.kind = Abstract || Hypothesis.verify c then
                   let h = apply_unifier (fill_hole hole ~parent:h ~child:c) u in

                   match h.kind with
                   | Concrete ->
                     let () = printf "%s\n" (Skeleton.to_string_hum h.skeleton.Hashcons.node) in
                     if Hypothesis.verify h then raise (SynthesisException (Solution h))
                   | Abstract ->
                     if not (Skeleton.is_simplifiable base_terms h.Hypothesis.skeleton.Hashcons.node) then
                       Heap.add heap h)
           | None -> failwiths "BUG: Abstract hypothesis has no holes." h Hypothesis.to_sexp)
        | None -> raise (SynthesisException NoSolution)
      done; NoSolution
    with SynthesisException h -> h
end

module BFS_Synthesizer = Make_BFS_Synthesizer(L2_Generalizer)

(** Maps (hole, spec) pairs to the hypotheses that can fill in the hole and match the spec. 

    The memoizer can be queried with a hole, a spec and a cost.

    Internally, the type of the hole and the types in the type context
    of the hole are normalized by substituting their free type
    variable ids with fresh ones. The memoizer only stores the
    normalized holes. This increases potential for sharing when
    different holes have the same type structure but different ids in
    their free type variables.
*)
module Memoizer = struct
  let denormalize_unifier u map =
    Unifier.to_alist u
    |> List.filter_map ~f:(fun (k, v) ->
        Option.map (IntMap.find map k) ~f:(fun k' -> k', v))
    |> Unifier.of_alist_exn

  module Key = struct
    module Hole_without_id = struct
      type t = {
        ctx : Type.t StaticDistance.Map.t;
        type_ : Type.t;
        symbol : Symbol.t;
      } with compare, sexp

      let normalize_free ctx t =
        let fresh_int = Util.Fresh.mk_fresh_int_fun () in
        let rec norm t = match t with
          | Var_t { contents = Quant _ }
          | Const_t _ -> t
          | App_t (name, args) -> App_t (name, List.map args ~f:norm)
          | Arrow_t (args, ret) -> Arrow_t (List.map args ~f:norm, norm ret)
          | Var_t { contents = Free (id, level) } ->
            (match IntMap.find !ctx id with
             | Some id -> Type.free id level
             | None ->
               let new_id = fresh_int () in
               ctx := IntMap.add !ctx new_id id;
               Type.free new_id level)
          | Var_t { contents = Link t } -> norm t
        in
        norm t

      let of_hole h =
        let free_ctx = ref IntMap.empty in
        let type_ = normalize_free free_ctx h.Hole.type_ in
        let type_ctx = StaticDistance.Map.map h.Hole.ctx ~f:(normalize_free free_ctx) in
        ({ ctx = type_ctx; symbol = h.Hole.symbol; type_; }, !free_ctx)
    end

    type t = {
      hole : Hole_without_id.t;
      spec : Specification.t;
    } with compare, sexp

    let hash = Hashtbl.hash

    let of_hole_spec hole spec =
      let (hole, map) = Hole_without_id.of_hole hole in
      ({ hole; spec; }, map)
  end

  module HoleTable = Hashtbl.Make(Key)
  module CostTable = Int.Table

  module HoleState = struct
    type t = {
      hypotheses : (Hypothesis.t * Unifier.t) list CostTable.t;
      generalizations : (Hypothesis.t * Unifier.t) list Lazy.t;
    } with sexp
  end

  type t = {
    hole_table : HoleState.t HoleTable.t;
    generalize : Generalizer_impl.t;
  }

  let create generalize = {
    hole_table = HoleTable.create ();
    generalize;
  }

  let rec get m hole spec cost =
    (* let () = *)
    (*   Debug.eprintf "Getting %s %s at cost %d" (Hole.to_string hole) *)
    (*     (Specification.to_string spec) cost *)
    (* in *)
    if cost < 0 then raise (Invalid_argument "Argument out of range.") else
    if cost = 0 then [] else
      let module S = HoleState in
      let module H = Hypothesis in
      let (key, map) = Key.of_hole_spec hole spec in
      let state = HoleTable.find_or_add m.hole_table key ~default:(fun () ->
          {
            S.hypotheses = CostTable.create ();
            S.generalizations = Lazy.from_fun (fun () -> m.generalize hole spec);
          })
      in
      let ret =
        match CostTable.find state.S.hypotheses cost with
        | Some hs -> hs
        | None ->
          let hs = List.concat_map (Lazy.force state.S.generalizations) ~f:(fun (p, p_u) ->
              match p.H.kind with
              | H.Concrete -> if p.H.cost = cost then [ (p, p_u) ] else []
              | H.Abstract -> if p.H.cost >= cost then [] else
                  let num_holes = List.length p.H.holes in
                  List.concat_map (Util.m_partition (cost - p.H.cost) num_holes)
                    ~f:(fun hole_costs ->
                        List.fold2_exn p.H.holes hole_costs ~init:[ (p, p_u) ]
                          ~f:(fun hs (hole, spec) hole_cost ->
                              List.concat_map hs ~f:(fun (p, p_u) ->
                                  let children = get m hole spec hole_cost in
                                  List.map children ~f:(fun (c, c_u) ->
                                      let u = Unifier.compose c_u p_u in
                                      let h = H.fill_hole hole ~parent:p ~child:c in
                                      h, u))))
                  |> List.filter ~f:(fun (h, u) ->
                      match h.H.kind with
                      | H.Concrete -> H.verify h
                      | H.Abstract -> failwiths "BUG: Did not fill in all holes." h H.to_sexp))
          in
          CostTable.add_exn state.S.hypotheses ~key:cost ~data:hs; hs
      in
      let ret = List.map ret ~f:(fun (h, u) -> (h, denormalize_unifier u map)) in
      (* let () = *)
      (*   Debug.eprintf "Returning %d hypos:" (List.length ret); *)
      (*   List.iter ret ~f:(fun (h, _) -> Debug.eprint (H.to_string_hum h)) *)
      (* in *)
      ret
end

module L2_Synthesizer = struct
  type result =
    | Solution of Hypothesis.t
    | NoSolution

  exception SynthesisException of result

  let generalize_expr hole spec =
    let symbol = hole.Hole.symbol in
    let generators =
      let open L2_Generalizer in
      if symbol = constant then
        [ generate_constants ]
      else if symbol = identifier then
        [ generate_identifiers ]
      else if symbol = lambda then
        [ ]
      else if symbol = expression then
        [ generate_expressions; generate_identifiers; generate_constants ]
      else if symbol = combinator then
        [ generate_expressions; generate_identifiers; generate_constants ]
      else
        failwiths "Unknown symbol type." symbol Symbol.to_sexp
    in
    List.concat (List.map generators ~f:(fun g -> g hole spec))

  let memoizer = Memoizer.create generalize_expr

  let total_cost (hypo_cost: int) (enum_cost: int) : int =
    hypo_cost + (Int.of_float (1.5 ** (Float.of_int enum_cost)))

  module AnnotatedH = struct
    type t = {
      hypothesis : Hypothesis.t;
      max_search_cost : int ref;
    }

    let of_hypothesis h = {
      hypothesis = h;
      max_search_cost = ref 0;
    }
  end

  let search hypo start_exh_cost end_cost : int =
    let module H = Hypothesis in
    let rec search (exh_cost: int) =
      (* If the cost of searching this level exceeds the max cost, end the search. *)
      if (total_cost hypo.H.cost exh_cost) >= end_cost then exh_cost else

        (* Otherwise, examine the next row in the search tree. *)
        begin
          let num_holes = List.length hypo.H.holes in
          List.concat_map (Util.m_partition exh_cost num_holes) ~f:(fun hole_costs ->
              List.fold2_exn hypo.H.holes hole_costs ~init:[ (hypo, Unifier.empty) ]
                ~f:(fun hs (hole, spec) hole_cost -> List.concat_map hs ~f:(fun (p, p_u) ->
                    let children = Memoizer.get memoizer hole spec hole_cost in
                    List.map children ~f:(fun (c, c_u) ->
                        let u = Unifier.compose c_u p_u in
                        let h = H.fill_hole hole ~parent:p ~child:c in
                        h, u))))
          |> List.iter ~f:(fun (h, u) ->
              match h.H.kind with
              | H.Concrete -> if H.verify h then raise (SynthesisException (Solution h))
              | H.Abstract -> failwiths "BUG: Did not fill in all holes." h H.to_sexp);
          search (exh_cost + 1)
        end
    in
    search start_exh_cost

  let select_generators symbol =
    let open L2_Generalizer in
    if symbol = constant then
      [ generate_constants ]
    else if symbol = identifier then
      [ generate_identifiers ]
    else if symbol = lambda then
      [ generate_lambdas ]
    else if symbol = expression then
      [ ]
    else if symbol = combinator then
      [ generate_combinators; ]
    else
      failwiths "Unknown symbol type." symbol Symbol.to_sexp

  let generalize hole spec =
    let generators = select_generators hole.Hole.symbol in
    List.concat (List.map generators ~f:(fun g -> g hole spec))

  let generalize_all = L2_Generalizer.generalize_all ~generalize:generalize

  let synthesize hypo max_cost =
    let module H = Hypothesis in
    let module AH = AnnotatedH in 
    let fresh_hypos = ref [ AH.of_hypothesis hypo ] in
    let stale_hypos = ref [] in

    try
      for cost = 1 to max_cost do
        (* Search each hypothesis that can be searched at this cost. If
           the search succeeds it will throw an exception. *)
        List.iter (!fresh_hypos @ !stale_hypos) ~f:(fun h ->
            if total_cost h.AH.hypothesis.H.cost (!(h.AH.max_search_cost) + 1) <= cost then
              let () =
                Debug.eprintf "Searching up to %d %s (cost = %d)"
                  cost (H.to_string_hum h.AH.hypothesis) (h.AH.hypothesis.H.cost)
              in
              h.AH.max_search_cost := search h.AH.hypothesis !(h.AH.max_search_cost) cost);

        (* Generalize each hypothesis that is cheap enough to generalize. *)
        let (generalizable, remaining) = List.partition_tf !fresh_hypos ~f:(fun h ->
            h.AH.hypothesis.H.cost < cost)
        in
        let children = List.concat_map generalizable ~f:(fun h ->
            generalize_all h.AH.hypothesis |> List.map ~f:AH.of_hypothesis)
        in
        let () = List.iter children ~f:(fun h -> Debug.eprint (Hypothesis.to_string h.AH.hypothesis)) in
        fresh_hypos := remaining @ children;
        stale_hypos := !stale_hypos @ generalizable;
      done; NoSolution
    with SynthesisException s -> s

  let initial_hypothesis examples =
    let exs = List.map examples ~f:(fun ex -> match ex with
        | (`Apply (_, args), out) ->
          (StaticDistance.Map.empty,
           List.map ~f:(Eval.eval (Ctx.empty ())) args,
           Eval.eval (Ctx.empty ()) out)
        | _ -> failwiths "Unexpected example type." ex sexp_of_example)
    in
    let t = Infer.Type.normalize (Example.signature examples) in
    Hypothesis.hole
      (Hole.create StaticDistance.Map.empty t L2_Generalizer.lambda)
      (Specification.FunctionExamples exs)
end


(* TODO: Finish fixing type snafu. Generalizer functions now return
   unifiers. Unifiers must be applied to the remainder of the
   hypothesis when a hole is filled (because filling a hole could
   instantiate a generic type variable). The memoizer needs to change
   as well and hasn't yet. Use new interface. Instead of returning a
   list of candidates, do the filling for the caller. *)
