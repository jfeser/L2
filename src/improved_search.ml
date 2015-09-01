open Core.Std

open Ast
open Collections
open Infer
open Util

module Hole = struct
  type t = {
    id  : int;
    ctx : Type.t Ctx.t;
    type_ : Type.t;
  } with compare, sexp

  let to_sexp = sexp_of_t
  let of_sexp = t_of_sexp

  let counter = ref 0

  let equal h1 h2 = h1.id = h2.id

  let to_string h = Sexp.to_string_hum (to_sexp h)

  let create ctx type_ = begin
    incr counter;
    { id = !counter; ctx; type_ }
  end
end

module Skeleton = struct
  type 'a t =
    | Num_h of int * 'a
    | Bool_h of bool * 'a
    | List_h of 'a t list * 'a
    | Tree_h of 'a t Tree.t * 'a
    | Id_h of id * 'a
    | Let_h of (id * 'a t * 'a t) * 'a
    | Lambda_h of (id list * 'a t) * 'a
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
    | Id_h (x, _) -> x
    | List_h (x, _) -> sprintf "[%s]" (list_to_string x)
    | Tree_h (x, _) -> Tree.to_string x ~str:ts
    | Op_h ((op, args), _) -> sprintf "(%s %s)" (Expr.Op.to_string op) (list_to_string args)
    | Let_h ((x, y, z), _) -> sprintf "(let %s %s %s)" x (ts y) (ts z)
    | Apply_h ((x, y), _) -> sprintf "(%s %s)" (ts x) (list_to_string y)
    | Lambda_h ((args, body), _) ->
      sprintf "(lambda (%s) %s)" (String.concat ~sep:" " args) (ts body)
    | Hole_h (h, _) -> sprintf "?%d" h.Hole.id

  let rec to_expr (f: Hole.t -> Expr.t) (s: 'a t) : Expr.t =
    match s with
    | Num_h (x, _) -> `Num x
    | Bool_h (x, _) -> `Bool x
    | Id_h (x, _) -> `Id x
    | List_h (x, _) -> `List (List.map ~f:(to_expr f) x)
    | Tree_h (x, _) -> `Tree (Tree.map ~f:(to_expr f) x)
    | Let_h ((x, y, z), _) -> `Let (x, to_expr f y, to_expr f z)
    | Lambda_h ((x, y), _) -> `Lambda (x, to_expr f y)
    | Apply_h ((x, y), _) -> `Apply (to_expr f x, List.map ~f:(to_expr f) y)
    | Op_h ((x, y), _) -> `Op (x, List.map ~f:(to_expr f) y)
    | Hole_h (x, _) -> f x

  let to_expr_exn s =
    to_expr (fun _ -> failwith "Tried to convert skeleton with holes to expression.") s

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
    | Let_h ((x, y, z), s) -> Let_h ((x, f y, f z), s)
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

  let is_simplifiable base s =
    let e = to_expr (fun h -> `Id (sprintf "h%d" h.Hole.id)) s in
    Rewrite.is_redundant base e
end

module Specification = struct
  module T = struct
    type t =
      | Bottom
      | Top
      | Examples of (value Ctx.t * value) list
      | FunctionExamples of (value Ctx.t * value list * value) list
    with compare, sexp

    let hash = Hashtbl.hash
    let compare = compare_t
  end

  include T
  include Hashable.Make(T)

  let of_sexp = t_of_sexp
  let to_sexp = sexp_of_t

  let to_string s = Sexp.to_string (to_sexp s)

  let verify spec expr = begin
    match spec with
    | Top -> true
    | Bottom -> false
    | Examples exs ->
      (try
         List.for_all exs ~f:(fun (in_ctx, out) ->
             let ctx = Ctx.merge_right Eval.stdlib_vctx in_ctx in
             Eval.eval ctx expr = out)
       with Eval.RuntimeError _ -> false)
    | FunctionExamples exs ->
      (try
         List.for_all exs ~f:(fun (in_ctx, in_args, out) ->
             let ctx = Ctx.merge_right Eval.stdlib_vctx in_ctx in
             Eval.eval ctx (`Apply (expr, List.map in_args ~f:Expr.of_value)) = out)
       with Eval.RuntimeError _ -> false)
  end
end

module HypothesisTable = Hashcons.Make(struct
    type t = Specification.t Skeleton.t
    let equal h1 h2 = Skeleton.compare Specification.compare h1 h2 = 0
    let hash = Skeleton.hash
  end)

module Hypothesis = struct
  type kind =
    | Abstract
    | Concrete
  with sexp
      
  type t = {
    skeleton : Specification.t Skeleton.t Hashcons.hash_consed;
    cost : int;
    kind : kind;
    holes : (Hole.t * Specification.t) list;
  }

  let to_sexp h =
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

  let table = HypothesisTable.create 100
  let num x s : t = {
    skeleton = HypothesisTable.hashcons table (Skeleton.Num_h (x, s));
    cost = 1;
    kind = Concrete;
    holes = [];
  }
  let bool x s : t = {
    skeleton = HypothesisTable.hashcons table (Skeleton.Bool_h (x, s));
    cost = 1;
    kind = Concrete;
    holes = [];
  }
  let id x s : t = {
    skeleton = HypothesisTable.hashcons table (Skeleton.Id_h (x, s));
    cost = 1;
    kind = Concrete;
    holes = [];
  }
  let hole x s : t = {
    skeleton = HypothesisTable.hashcons table (Skeleton.Hole_h (x, s));
    cost = 1;
    kind = Abstract;
    holes = [ (x, s) ];
  }
  let list (x: t list) s : t = {
    skeleton = HypothesisTable.hashcons table
        (Skeleton.List_h (List.map x ~f:(fun h -> h.skeleton.Hashcons.node), s));
    cost = 1 + List.int_sum (List.map x ~f:(fun h -> h.cost));
    kind = if List.exists x ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
    holes = List.concat (List.map x ~f:(fun h -> h.holes));
  }
  let tree x s : t =
    let flat = Tree.flatten x in
    {
      skeleton = HypothesisTable.hashcons table
          (Skeleton.Tree_h (Tree.map x ~f:(fun h -> h.skeleton.Hashcons.node), s));
      cost = 1 + List.int_sum (List.map flat ~f:(fun h -> h.cost));
      kind = if List.exists flat ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat (List.map (Tree.flatten x) ~f:(fun h -> h.holes));
    }
  let _let x s : t =
    let (id, bound, body) = x in
    {
      skeleton = HypothesisTable.hashcons table
          (Skeleton.Let_h ((id, bound.skeleton.Hashcons.node, body.skeleton.Hashcons.node), s));
      cost = 1 + bound.cost + body.cost;
      kind = if bound.kind = Abstract || body.kind = Abstract then Abstract else Concrete;
      holes = bound.holes @ body.holes;
    }
  let lambda x s : t =
    let (args, body) = x in
    {
      skeleton = HypothesisTable.hashcons table
          (Skeleton.Lambda_h ((args, body.skeleton.Hashcons.node), s));
      cost = 1 + body.cost;
      kind = if body.kind = Abstract then Abstract else Concrete;
      holes = body.holes;
    }
  let apply x s : t =
    let (func, args) = x in
    {
      skeleton = HypothesisTable.hashcons table
          (Skeleton.Apply_h
             ((func.skeleton.Hashcons.node,
               List.map args ~f:(fun h -> h.skeleton.Hashcons.node)), s));
      cost = 1 + func.cost + List.int_sum (List.map args ~f:(fun h -> h.cost));
      kind =
        if func.kind = Abstract || List.exists args ~f:(fun h -> h.kind = Abstract) then
          Abstract else Concrete;
      holes = func.holes @ (List.concat (List.map args ~f:(fun h -> h.holes)));
    }
  let op x s : t =
    let (op, args) = x in
    {
      skeleton = HypothesisTable.hashcons table
          (Skeleton.Op_h ((op, List.map args ~f:(fun h -> h.skeleton.Hashcons.node)), s));
      cost = 1 + Expr.Op.cost op + List.int_sum (List.map args ~f:(fun h -> h.cost));
      kind = if List.exists args ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat (List.map args ~f:(fun h -> h.holes));
    }

  let compare_cost h1 h2 = Int.compare h1.cost h2.cost

  let spec h : Specification.t = Skeleton.annotation h.skeleton.Hashcons.node
  
  let to_expr (h: t) : Expr.t = begin
    if h.kind = Abstract then
      failwith "Tried to convert an abstract hypothesis to an expression.";
    let (s: Specification.t Skeleton.t) = h.skeleton.Hashcons.node in
    Skeleton.to_expr_exn s
  end

  let to_string h = Sexp.to_string_hum (to_sexp h)

  let fill_hole hole ~parent:p ~child:c = begin
    if not (List.exists p.holes ~f:(fun (h, _) -> Hole.equal h hole)) then
      failwith "Hypothesis does not contain the specified hole.";
    if List.exists c.holes ~f:(fun (h, _) -> Hole.equal h hole) then
      failwith "Same hole present in parent and child.";
    let holes =
      (List.filter p.holes ~f:(fun (h, _) -> not (Hole.equal h hole))) @ c.holes
    in
    {
      skeleton =
        HypothesisTable.hashcons table
          (Skeleton.fill_hole hole ~parent:p.skeleton.Hashcons.node ~child:c.skeleton.Hashcons.node);
      cost = p.cost + c.cost;
      kind = if List.length holes = 0 then Concrete else Abstract;
      holes;
    }
  end
end

let generate_concrete_hypotheses hole spec =
  let consts =
    match hole.Hole.type_ with
    | Const_t Num_t -> [
        Hypothesis.num 0 spec;
        Hypothesis.num 1 spec;
        Hypothesis.num Int.max_value spec;
      ]
    | Const_t Bool_t -> [
        Hypothesis.bool true spec;
        Hypothesis.bool false spec;
      ]
    | App_t ("list", _) -> [
        Hypothesis.list [] spec;
      ]
    | _ -> []
  in
  let names =
    Ctx.to_alist hole.Hole.ctx
    |> List.filter_map ~f:(fun (k, v) ->
        if Type.equal v hole.Hole.type_ then Some (Hypothesis.id k spec) else None)
  in
  consts @ names

let generate_abstract_hypotheses hole spec =
  match hole.Hole.type_ with
  (* If the hole has an arrow type, generate a lambda expression with
     the right number of arguments and push the specification down. *)
  | Arrow_t (args_t, ret_t) ->
    let args = List.map args_t ~f:(fun t -> Fresh.name "x", t) in
    let ctx = Ctx.of_alist_exn args in
    let arg_names = List.map args ~f:(fun (name, _) -> name) in
    let hole_spec = match spec with
      | Specification.FunctionExamples exs ->
        let hole_exs = List.map exs ~f:(fun (in_ctx, in_args, out) ->
            let in_ctx' = Ctx.bind_alist in_ctx (List.zip_exn arg_names in_args) in
            (in_ctx', out))
        in
        Specification.Examples hole_exs
      | Specification.Bottom -> Specification.Bottom
      | _ -> Specification.Top
    in
    [ Hypothesis.lambda (arg_names, Hypothesis.hole (Hole.create ctx ret_t) hole_spec) spec ]

  (* Otherwise, select all functions with the right return type. *)
  | _ ->
    let op_hypos =
      List.filter_map Expr.Op.all ~f:(fun op ->
          let op_t = instantiate 0 (Expr.Op.meta op).Expr.Op.typ in
          match op_t with
          | Arrow_t (args_t, ret_t) ->
            let hole_t = instantiate 0 hole.Hole.type_ in
            (* Try to unify the return type of the operator with the type of the hole. *)
            (match Infer.Unifier.of_types hole_t ret_t with
             | Some unifier ->
               (* If unification succeeds, apply the unifier to the rest of the type. *)
               let args_t = List.map args_t ~f:(fun a -> Infer.Unifier.apply unifier a) in
               let Arrow_t (args_t, ret_t) = normalize (generalize (-1) (Arrow_t (args_t, ret_t))) in
               let arg_holes = List.map args_t ~f:(fun t ->
                   Hypothesis.hole (Hole.create hole.Hole.ctx t) Specification.Top)
               in
               Some (Hypothesis.op (op, arg_holes) spec)
             | None -> None)
          | _ -> None)
    in
    let apply_hypos =
      List.filter_map (Ctx.to_alist Infer.stdlib_tctx) ~f:(fun (func, func_t) ->
          let func_t = instantiate 0 func_t in
          match func_t with
          | Arrow_t (args_t, ret_t) ->
            let hole_t = instantiate 0 hole.Hole.type_ in
            (* Try to unify the return type of the operator with the type of the hole. *)
            (match Infer.Unifier.of_types hole_t ret_t with
             | Some unifier ->
               (* If unification succeeds, apply the unifier to the rest of the type. *)
               let args_t = List.map args_t ~f:(fun a -> Infer.Unifier.apply unifier a) in
               let Arrow_t (args_t, ret_t) = normalize (generalize (-1) (Arrow_t (args_t, ret_t))) in
               let arg_holes = List.map args_t ~f:(fun t ->
                   Hypothesis.hole (Hole.create hole.Hole.ctx t) Specification.Top)
               in
               Some (Hypothesis.apply (Hypothesis.id func Specification.Top, arg_holes) spec)
             | None -> None)
          | _ -> None)
    in
    op_hypos @ apply_hypos

let generate_hypotheses =
  let memo =
    Memo.general (fun (hole, spec) ->
        (generate_concrete_hypotheses hole spec) @ (generate_abstract_hypotheses hole spec))
  in
  fun hole spec -> memo (hole, spec)

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
           List.iter (generate_hypotheses hole spec) ~f:(fun c ->
               if c.kind = Abstract || Specification.verify spec (to_expr c) then
                 let h = fill_hole hole ~parent:h ~child:c in

                 match h.kind with
                 | Concrete ->
                   let () = printf "%s\n" (Skeleton.to_string_hum h.skeleton.Hashcons.node) in
                   if Specification.verify (Hypothesis.spec h) (to_expr h) then
                     raise (SynthesisException (Solution h))
                 | Abstract ->
                   if not (Skeleton.is_simplifiable base_terms h.Hypothesis.skeleton.Hashcons.node) then
                     Heap.add heap h)
         | None -> failwiths "BUG: Abstract hypothesis has no holes." h Hypothesis.to_sexp)
      | None -> raise (SynthesisException NoSolution)
    done; NoSolution
  with SynthesisException h -> h

(* let h = Hypothesis.hole *)
(*     (Hole.create (Ctx.empty ()) (Type.of_string "(list[num]) -> num")) *)
(*     (Specification.FunctionExamples [ *)
(*         Ctx.empty (), [ `List [`Num 1] ], `Num 1; *)
(*         Ctx.empty (), [ `List [`Num 1; `Num 2] ], `Num 2; *)
(*       ]) *)
(* let () = *)
(*   match synthesize h with *)
(*   | Solution s -> printf "Solution: %s\n" (Hypothesis.to_string s) *)
(*   | NoSolution -> printf "No solution\n" *)
