open Core.Std

open Collections
open Infer
open Util

module StaticDistance = struct
  module T = struct
    type t = int * int with compare, sexp
  end

  include T
  include Comparable.Make(T)

  let increment_scope x =
    let (a, b) = x in
    (a + 1, b)

  let map_increment_scope x =
    Map.to_alist x
    |> List.map ~f:(fun (k, v) -> (increment_scope k, v))
    |> Map.of_alist_exn

  let create ~distance ~index =
    let open Int in
    if distance <= 0 || index <= 0 then raise (Invalid_argument "Argument out of range.") else
      (distance, index)

  let distance x = let (a, _) = x in a
  let index x = let (_, b) = x in b

  let args num =
    List.range ~stride:1 ~start:`inclusive ~stop:`inclusive 1 num
    |> List.map ~f:(fun i -> (1, i))

  let to_string x =
    let (a, b) = x in
    sprintf "%d_%d" a b
end

module Symbol = struct
  type t = int

  let (names: string Int.Table.t) = Int.Table.create ()
  let (counter: int ref) = ref 0

  let sexp_of_t (s: t) : Sexp.t =
    let open Sexp in
    match Int.Table.find names s with
    | Some name -> List [
        List [ Atom "id"; Atom (Int.to_string s) ];
        List [ Atom "name"; Atom name ];
      ]
    | None -> failwiths (sprintf "BUG: Looking up symbol name of '%d' failed." s)
                names <:sexp_of<string Int.Table.t>>

  let t_of_sexp (s: Sexp.t) : t =
    let open Sexp in
    match s with
    | List [ List [ Atom "id"; Atom id_s ]; List [ Atom "name"; Atom name ]; ] ->
      let id = Int.of_string id_s in
      (match Int.Table.add names ~key:id ~data:name with
       | `Ok -> id
       | `Duplicate -> raise (Sexp.Of_sexp_error (Failure "Symbol already loaded.", s)))
    | _ -> raise (Sexp.Of_sexp_error (Failure "Sexp has the wrong format.", s))

  let (compare: t -> t -> int) = Int.compare
  let (equal: t -> t -> bool) = Int.equal

  let create (name: string) : t = begin
    let id = incr counter; !counter in
    match Int.Table.add names ~key:id ~data:name with
    | `Ok -> id
    | `Duplicate -> failwiths "Symbol already created." name String.sexp_of_t
  end
end

module Hole = struct
  type id = int with sexp, compare
  
  type t = {
    id  : id;
    ctx : Type.t StaticDistance.Map.t;
    type_ : Type.t;
    symbol : Symbol.t;
  } with sexp

  let id_to_string = Int.to_string
  
  let compare h1 h2 = Int.compare h1.id h2.id

  let counter = ref 0

  let equal h1 h2 = h1.id = h2.id

  let to_string h = Sexp.to_string_hum (sexp_of_t h)

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
    | Op_h of (Expr.Op.t * ('a t list)) * 'a
    | Hole_h of Hole.t * 'a
  with compare, sexp

  let rec equal ~equal:e h1 h2 = match h1, h2 with
    | Num_h (x1, s1), Num_h (x2, s2) -> Int.equal x1 x2 && e s1 s2
    | Bool_h (x1, s1), Bool_h (x2, s2) -> Bool.equal x1 x2 && e s1 s2
    | List_h (l1, s1), List_h (l2, s2) -> List.equal l1 l2 ~equal:(equal ~equal:e) && e s1 s2
    | Tree_h (t1, s1), Tree_h (t2, s2) -> Tree.equal t1 t2 ~equal:(equal ~equal:e) && e s1 s2
    | Id_h (id1, s1), Id_h (id2, s2) -> id1 = id2 && e s1 s2
    | Let_h ((x1, y1), s1), Let_h ((x2, y2), s2) -> equal x1 x2 ~equal:e && equal y1 y2 ~equal:e && e s1 s2
    | Lambda_h ((x1, y1), s1), Lambda_h ((x2, y2), s2) -> Int.equal x1 x2 && equal y1 y2 ~equal:e && e s1 s2
    | Apply_h ((x1, a1), s1), Apply_h ((x2, a2), s2) ->
      equal x1 x2 ~equal:e && List.equal a1 a2 ~equal:(equal ~equal:e) && e s1 s2
    | Op_h ((o1, a1), s1), Op_h ((o2, a2), s2) ->
      Expr.Op.equal o1 o2 && List.equal a1 a2 ~equal:(equal ~equal:e) && e s1 s2
    | Hole_h (h1, s1), Hole_h (h2, s2) -> Hole.equal h1 h2 && e s1 s2
    | _ -> false

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
          StaticDistance.map_increment_scope ctx
          |> StaticDistance.Map.add ~key:(StaticDistance.create ~distance:1 ~index:1) ~data:name
        in
        `Let (name, to_expr ctx bound, to_expr ctx body)
      | Lambda_h ((num_args, body), _) ->
        let ctx = StaticDistance.map_increment_scope ctx in
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

  let of_expr spec e =
    let rec of_expr ctx = function
      | `Num x -> Num_h (x, spec)
      | `Bool x -> Bool_h (x, spec)
      | `Id id ->
        (match String.Map.find ctx id with
         | Some sd -> Id_h (StaticDistance sd, spec)
         | None -> Id_h (Name id, spec))
      | `List l -> List_h (List.map l ~f:(of_expr ctx), spec)
      | `Tree t -> Tree_h (Tree.map t ~f:(of_expr ctx), spec)
      | `Let (id, bound, body) ->
        let ctx = String.Map.map ctx ~f:StaticDistance.increment_scope in
        let ctx = String.Map.add ctx ~key:id ~data:(StaticDistance.create ~distance:1 ~index:1) in
        Let_h ((of_expr ctx bound, of_expr ctx body), spec)
      | `Lambda (args, body) ->
        let ctx = String.Map.map ctx ~f:StaticDistance.increment_scope in
        let num_args = List.length args in
        let ctx =
          List.fold2_exn args (StaticDistance.args num_args) ~init:ctx
            ~f:(fun ctx arg_id arg_sd -> String.Map.add ctx ~key:arg_id ~data:arg_sd)
        in
        Lambda_h ((num_args, of_expr ctx body), spec)
      | `Apply (func, args) ->
        Apply_h ((of_expr ctx func, List.map args ~f:(of_expr ctx)), spec)
      | `Op (op, args) -> Op_h ((op, List.map args ~f:(of_expr ctx)), spec)
    in
    of_expr String.Map.empty e

  let compare = compare_t
  let hash = Hashtbl.hash

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

  let map_annotation ~f s = match s with
    | Num_h (x, a) -> Num_h (x, f a)
    | Bool_h (x, a) -> Bool_h (x, f a)
    | Id_h (x, a) -> Id_h (x, f a)
    | List_h (x, a) -> List_h (x, f a)
    | Tree_h (x, a) -> Tree_h (x, f a)
    | Let_h (x, a) -> Let_h (x, f a)
    | Lambda_h (x, a) -> Lambda_h (x, f a)
    | Apply_h (x, a) -> Apply_h (x, f a)
    | Op_h (x, a) -> Op_h (x, f a)
    | Hole_h (x, a) -> Hole_h (x, f a)

  let rec fill_hole hole ~parent:p ~child:c =
    let f p' = fill_hole hole ~child:c ~parent:p' in
    match p with
    | Num_h _
    | Bool_h _
    | Id_h _ -> p
    | Hole_h (h, s) -> if Hole.equal h hole then (map_annotation c ~f:(fun _ -> s)) else p
    | List_h (x, s) -> List_h (List.map ~f:f x, s)
    | Tree_h (x, s) -> Tree_h (Tree.map ~f:f x, s)
    | Let_h ((x, y), s) -> Let_h ((f x, f y), s)
    | Lambda_h ((x, y), s) -> Lambda_h ((x, f y), s)
    | Apply_h ((x, y), s) -> Apply_h ((f x, List.map ~f:f y), s)
    | Op_h ((x, y), s) -> Op_h ((x, List.map ~f:f y), s)

  let rec holes = function
    | Num_h _
    | Bool_h _
    | Id_h _ -> []
    | List_h (x, _) -> List.concat_map x ~f:holes
    | Tree_h (x, _) -> List.concat_map (Tree.flatten x) ~f:holes
    | Let_h ((bound, body), _) -> (holes bound) @ (holes body)
    | Lambda_h ((_, body), _) -> holes body
    | Apply_h ((func, args), _) -> (holes func) @ (List.concat_map args ~f:holes)
    | Op_h ((_, args), _) -> List.concat_map args ~f:holes
    | Hole_h (hole, spec) -> [ (hole, spec) ]
end

module Specification = struct
  module Examples = struct
    module Input = struct
      module T = struct
        type t = Ast.value StaticDistance.Map.t with sexp, compare
      end
      include T
      include Comparable.Make(T)
    end

    type example = (Input.t * Ast.value) with sexp, compare
    type t = example list with sexp, compare

    let of_list exs =
      let module I = Input in
      let open Or_error in
      List.fold exs ~init:(Ok I.Map.empty) ~f:(fun m (ctx, ret) ->
          m >>= fun m ->
          match I.Map.find m ctx with
          | Some ret' when ret' = ret -> Ok m
          | Some _ -> error_string "Different return value for same input."
          | None -> Ok (I.Map.add m ~key:ctx ~data:ret))
      |> ignore
      >>| fun () -> List.dedup ~compare:compare_example exs

    let of_list_exn exs = of_list exs |> Or_error.ok_exn

    let to_list t = t
  end

  module FunctionExamples = struct
    module Input = struct
      module T = struct
        type t = Ast.value StaticDistance.Map.t * Ast.value list with sexp, compare
      end
      include T
      include Comparable.Make(T)
    end

    type example = (Input.t * Ast.value) with sexp, compare
    type t = example list with sexp, compare

    let of_list exs =
      let module I = Input in
      let open Or_error in
      List.fold exs ~init:(Ok I.Map.empty) ~f:(fun m ((ctx, args), ret) ->
          let key = (ctx, args) in
          m >>= fun m ->
          match I.Map.find m key with
          | Some ret' when ret' = ret -> Ok m
          | Some _ -> error_string "Different return value for same input."
          | None -> Ok (I.Map.add m ~key ~data:ret))
      |> ignore
      >>| fun () -> List.dedup ~compare:compare_example exs

    let of_list_exn exs = of_list exs |> Or_error.ok_exn
    
    let to_list t = t
  end
             
  type t =
    | Bottom
    | Top
    | Examples of Examples.t
    | FunctionExamples of FunctionExamples.t
  with compare, sexp

  let hash = Hashtbl.hash
  let compare = compare_t

  let to_string s = Sexp.to_string (sexp_of_t s)

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
             Eval.eval ~recursion_limit:100 value_ctx expr = out)
       with
       | Eval.HitRecursionLimit
       | Eval.RuntimeError _ -> false)
    | FunctionExamples exs ->
      (try
         List.for_all exs ~f:(fun ((in_ctx, in_args), out) ->
             let fresh_name = Fresh.mk_fresh_name_fun () in
             let name_ctx = StaticDistance.Map.map in_ctx ~f:(fun _ -> fresh_name ()) in
             let expr =
               `Apply (Skeleton.to_expr_exn ~ctx:name_ctx ~fresh_name skel,
                       List.map in_args ~f:Expr.of_value)
             in
             let value_ctx =
               StaticDistance.Map.to_alist in_ctx
               |> List.map ~f:(fun (k, v) -> StaticDistance.Map.find_exn name_ctx k, v)
               |> Ctx.of_alist_exn
               |> Ctx.merge_right Eval.stdlib_vctx
             in
             Eval.eval ~recursion_limit:100 value_ctx expr = out)
       with
       | Eval.HitRecursionLimit
       | Eval.RuntimeError _ -> false)
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
        List.map exs ~f:(fun ((in_ctx, in_args), out) ->
            let in_ctx =
              StaticDistance.Map.to_alist in_ctx
              |> List.map ~f:(fun (k, v) -> (StaticDistance.increment_scope k, v))
              |> StaticDistance.Map.of_alist_exn
            in
            ((in_ctx, in_args), out))
      in
      FunctionExamples exs
end

module type CostModel_Intf = sig
  val id_cost : Ast.id -> int
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
        List [ Atom "skeleton"; Skeleton.sexp_of_t Specification.sexp_of_t h.skeleton.Hashcons.node ];
        List [ Atom "cost"; sexp_of_int h.cost ];
        List [ Atom "kind"; sexp_of_kind h.kind ];
        List [
          Atom "holes";
          sexp_of_list (fun (hole, spec) ->
              List [ Hole.sexp_of_t hole; Specification.sexp_of_t spec ]) h.holes
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
          skeleton = Table.hashcons table (<:of_sexp<Specification.t Skeleton.t>> skel_s);
          cost = Int.t_of_sexp cost_s;
          kind = kind_of_sexp kind_s;
          holes = <:of_sexp<(Hole.t * Specification.t) list>> holes_s;
        }
      | _ -> raise (Sexp.Of_sexp_error (Failure "Sexp has the wrong format.", s))

    let compare_cost h1 h2 = Int.compare h1.cost h2.cost

    let spec h : Specification.t = Skeleton.annotation h.skeleton.Hashcons.node

    let to_expr (h: t) : Expr.t =
      match h.kind with
      | Abstract -> failwith "Tried to convert an abstract hypothesis to an expression."
      | Concrete -> Skeleton.to_expr_exn (h.skeleton.Hashcons.node)
    
    let to_string h = Sexp.to_string_hum (sexp_of_t h)
    let to_string_hum h = Skeleton.to_string_hum (h.skeleton.Hashcons.node)

    let map h ~skeleton:f =
      let skeleton = f h.skeleton.Hashcons.node in
      let holes = Skeleton.holes skeleton in
      { h with
        skeleton = Table.hashcons table skeleton;
        kind = if List.length holes = 0 then Concrete else Abstract;
        holes;
      }

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
        cost = func.cost + List.int_sum (List.map args ~f:(fun h -> h.cost));
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
