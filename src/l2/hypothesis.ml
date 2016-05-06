open Core.Std

open Collections
open Infer
open Util

module StaticDistance = struct
  module T = struct
    type t = int * int [@@deriving compare, sexp]
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
  module T = struct
    type t = int

    let (names: string Int.Table.t) = Int.Table.create ()
    let (counter: int ref) = ref 0
    
    let (compare: t -> t -> int) = Int.compare
    let (equal: t -> t -> bool) = Int.equal

    let create (name: string) : t =
      let id = incr counter; !counter in
      match Int.Table.add names ~key:id ~data:name with
      | `Ok -> id
      | `Duplicate -> failwiths "BUG: Symbol counter overflowed." (names, !counter)
                        [%sexp_of:string Int.Table.t * int]

    let to_string s =
      match Int.Table.find names s with
      | Some name -> name
      | None -> failwiths (sprintf "BUG: Looking up name of symbol '%d' failed." s)
                  names [%sexp_of:string Int.Table.t]
    
    let sexp_of_t (s: t) : Sexp.t = Sexp.Atom (to_string s)

    let t_of_sexp (s: Sexp.t) : t =
      let open Sexp in
      match s with
      | Atom name ->
        let m_id =
          Int.Table.to_alist names
          |> List.find_map ~f:(fun (id, name') -> if String.equal name name' then Some id else None)
        in
        begin match m_id with
          | Some id -> id
          | None -> create name
        end
      | _ -> raise (Sexp.Of_sexp_error (Failure "Sexp has the wrong format.", s))
  end

  include T
  include Comparable.Make(T)
end

module Hole = struct
  module Id = Int
  
  type t = {
    id  : Id.t;
    ctx : Type.t StaticDistance.Map.t;
    type_ : Type.t;
    symbol : Symbol.t;
  } [@@deriving sexp, compare]

  let counter = ref 0

  let equal h1 h2 = compare h1 h2 = 0
  let equal_id h1 h2 = Id.equal h1.id h2.id
  
  let to_string h = Sexp.to_string_hum (sexp_of_t h)

  let create ?ctx:(ctx = StaticDistance.Map.empty) type_ symbol = begin
    incr counter;
    if !counter < 0 then failwith "Hole id counter overflowed.";
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
  module Id = struct
    module T = struct
      type t = 
        | StaticDistance of StaticDistance.t
        | Name of string
      [@@deriving compare, sexp]
    end

    include T
    include Comparable.Make(T)
  end

  type 'a t =
    | Num_h of int * 'a
    | Bool_h of bool * 'a
    | List_h of 'a t list * 'a
    | Tree_h of 'a t Tree.t * 'a
    | Id_h of Id.t * 'a
    | Let_h of ('a t * 'a t) * 'a
    | Lambda_h of (int * 'a t) * 'a
    | Apply_h of ('a t * ('a t list)) * 'a
    | Op_h of (Expr.Op.t * ('a t list)) * 'a
    | Hole_h of Hole.t * 'a
  [@@deriving compare, sexp]

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
    | Id_h (Id.StaticDistance x, _) -> StaticDistance.to_string x
    | Id_h (Id.Name x, _) -> x
    | List_h (x, _) -> sprintf "[%s]" (list_to_string x)
    | Tree_h (x, _) -> Tree.to_string x ~str:ts
    | Op_h ((op, args), _) -> sprintf "(%s %s)" (Expr.Op.to_string op) (list_to_string args)
    | Let_h ((bound, body), _) -> sprintf "(let *1* %s %s)" (ts bound) (ts body)
    | Apply_h ((x, y), _) -> sprintf "(%s %s)" (ts x) (list_to_string y)
    | Lambda_h ((num_args, body), _) -> sprintf "(lambda *%d* %s)" num_args (ts body)
    | Hole_h (h, _) -> sprintf "?%d" h.Hole.id

  let to_expr :
    ?ctx:Expr.t StaticDistance.Map.t
    -> ?fresh_name:(unit -> string)
    -> ?of_hole:(Hole.t -> Expr.t)
    -> 'a t
    -> Expr.t =
    fun ?(ctx = StaticDistance.Map.empty) ?fresh_name ?of_hole s ->
      let of_hole = match of_hole with
        | Some f -> f
        | None -> fun _ ->
          failwiths "Unexpected hole." s (fun s -> [%sexp_of:string] (to_string_hum s))
      in
      let fresh_name = match fresh_name with
        | Some fresh -> fresh
        | None -> Fresh.mk_fresh_name_fun ()
      in
      let rec to_expr ctx s =
        match s with
        | Num_h (x, _) -> `Num x
        | Bool_h (x, _) -> `Bool x
        | Id_h (Id.StaticDistance x, _) ->
          (match StaticDistance.Map.find ctx x with
           | Some expr -> expr
           | None ->
             failwiths "Context does not contain coordinate." (s, x, ctx) 
               (Tuple.T3.sexp_of_t
                  (sexp_of_t (fun _ -> Sexp.Atom "?"))
                  [%sexp_of:StaticDistance.t]
                  [%sexp_of:Expr.t StaticDistance.Map.t]))
        | Id_h (Id.Name x, _) -> `Id x
        | List_h (elems, _) -> `List (List.map elems ~f:(to_expr ctx))
        | Tree_h (elems, _) -> `Tree (Tree.map elems ~f:(to_expr ctx))
        | Let_h ((bound, body), _) ->
          let name = fresh_name () in
          let ctx =
            StaticDistance.map_increment_scope ctx
            |> StaticDistance.Map.add
              ~key:(StaticDistance.create ~distance:1 ~index:1)
              ~data:(`Id name)
          in
          `Let (name, to_expr ctx bound, to_expr ctx body)
        | Lambda_h ((num_args, body), _) ->
          let ctx = StaticDistance.map_increment_scope ctx in
          let arg_names = List.init num_args ~f:(fun _ -> fresh_name ()) in
          let ctx = List.fold (List.zip_exn arg_names (StaticDistance.args num_args)) ~init:ctx
              ~f:(fun ctx (name, sd) -> Map.add ctx ~key:sd ~data:(`Id name))
          in
          `Lambda (arg_names, to_expr ctx body)
        | Apply_h ((func, args), _) -> `Apply (to_expr ctx func, List.map ~f:(to_expr ctx) args)
        | Op_h ((op, args), _) -> `Op (op, List.map ~f:(to_expr ctx) args)
        | Hole_h (x, _) -> of_hole x
      in
      to_expr ctx s

  let to_expr_exn ?(ctx = StaticDistance.Map.empty) ?(fresh_name) s =
    match fresh_name with
    | Some fresh ->
      to_expr ~ctx ~fresh_name:fresh s
    | None -> to_expr ~ctx s

  let of_expr spec e =
    let rec of_expr ctx = function
      | `Num x -> Num_h (x, spec)
      | `Bool x -> Bool_h (x, spec)
      | `Id id ->
        (match String.Map.find ctx id with
         | Some sd -> Id_h (Id.StaticDistance sd, spec)
         | None -> Id_h (Id.Name id, spec))
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

  let of_string : 'a. 'a -> string -> 'a t Or_error.t = fun spec str ->
    let module Let_syntax = Or_error.Let_syntax.Let_syntax in
    let%map expr = Expr.of_string str in
    of_expr spec expr

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

  let default x s = (x, s)
  let map
      ?(num = default)
      ?(bool = default)
      ?(id = default)
      ?(hole = default)
      ?(list = default)
      ?(tree = default)
      ?(let_ = default)
      ?(lambda = default)
      ?(op = default)
      ?(apply = default)
      skel =
    let rec ps = function
      | Num_h (x, s) ->
        let (x', s') = num x s in
        Num_h (x', s')      
      | Bool_h (x, s) ->
        let (x', s') = bool x s in
        Bool_h (x', s')      
      | Id_h (x, s) ->
        let (x', s') = id x s in
        Id_h (x', s')      
      | Hole_h (x, s) ->
        let (x', s') = hole x s in
        Hole_h (x', s')      
      | List_h (x, s) ->
        let (x', s') = list x s in
        let x'' = List.map x' ~f:ps in
        List_h (x'', s')
      | Tree_h (x, s) ->
        let (x', s') = tree x s in
        let x'' = Tree.map x' ~f:ps in
        Tree_h (x'', s')
      | Let_h (x, s) ->
        let ((bound, body), s') = let_ x s in
        let bound' = ps bound in
        let body' = ps body in
        Let_h ((bound', body'), s')
      | Lambda_h (x, s) ->
        let ((num_args, body), s') = lambda x s in
        let body' = ps body in
        Lambda_h ((num_args, body'), s')
      | Op_h (x, s) ->
        let ((op, args), s') = op x s in
        let args' = List.map args ~f:ps in
        Op_h ((op, args'), s')
      | Apply_h (x, s) ->
        let ((func, args), s') = apply x s in
        let func' = ps func in
        let args' = List.map args ~f:ps in
        Apply_h ((func', args'), s')
    in
    ps skel

  let rec map_hole ~f s =
    match s with
    | Num_h _
    | Bool_h _
    | Id_h _ -> s
    | Hole_h (h, s) -> f (h, s)
    | List_h (x, s) -> List_h (List.map ~f:(map_hole ~f) x, s)
    | Tree_h (x, s) -> Tree_h (Tree.map ~f:(map_hole ~f) x, s)
    | Let_h ((x, y), s) -> Let_h ((map_hole ~f x, map_hole ~f y), s)
    | Lambda_h ((x, y), s) -> Lambda_h ((x, map_hole ~f y), s)
    | Apply_h ((x, y), s) -> Apply_h ((map_hole ~f x, List.map ~f:(map_hole ~f) y), s)
    | Op_h ((x, y), s) -> Op_h ((x, List.map ~f:(map_hole ~f) y), s)

  let rec fill_hole hole ~parent:p ~child:c =
    map_hole p ~f:(fun (hole', spec) ->
        if Hole.equal_id hole hole' then (map_annotation c ~f:(fun _ -> spec))
        else Hole_h (hole', spec))

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

module CostModel = struct
  type t = {
    num : int -> int;
    bool : bool -> int;
    hole : Hole.t -> int;
    id : Skeleton.Id.t -> int;
    list : 'a. 'a list -> int;
    tree : 'a. 'a Collections.Tree.t -> int;
    _let : 'a. 'a -> 'a -> int;
    lambda : 'a. int -> 'a -> int;
    apply : 'a. 'a -> 'a list -> int;
    op : 'a. Expr.Op.t -> 'a list -> int;
  }

  let constant x = {
    num = (fun _ -> x);
    bool = (fun _ -> x);
    hole = (fun _ -> x);
    lambda = (fun _ _ -> x);
    _let = (fun _ _ -> x);
    list = (fun _ -> x);
    tree = (fun _ -> x);
    apply = (fun _ _ -> x);
    op = (fun _ _ -> x);
    id = (fun _ -> x);
  }

  let zero = constant 0

  let cost_of_skeleton cm sk =
    let module Sk = Skeleton in
    let rec cost = function
      | Sk.Num_h (x, _) -> cm.num x
      | Sk.Bool_h (x, _) -> cm.bool x
      | Sk.Hole_h (x, _) -> cm.hole x
      | Sk.Id_h (x, _) -> cm.id x
      | Sk.List_h (x, _) -> cm.list x + List.int_sum (List.map x ~f:cost)
      | Sk.Tree_h (x, _) -> cm.tree x + List.int_sum (List.map (Tree.flatten x) ~f:cost)
      | Sk.Let_h ((x, y), _) -> cm._let x y + cost x + cost y
      | Sk.Lambda_h ((x, y), _) -> cm.lambda x y + cost y
      | Sk.Apply_h ((x, y), _) -> cm.apply x y + cost x + List.int_sum (List.map y ~f:cost)
      | Sk.Op_h ((x, y), _) -> cm.op x y + List.int_sum (List.map y ~f:cost)
    in
    cost sk
end

module PerFunctionCostModel = struct
  module CM = CostModel
    
  type t = {
    num : int;
    bool: int;
    hole: int;
    lambda: int;
    _let: int;
    list: int;
    tree: int;
    var : int;
    call: int String.Map.t;
    call_default: int;
  }

  let to_cost_model t =
    let lookup_func op = 
      match String.Map.find t.call op with
      | Some cost -> cost
      | None -> t.call_default
    in
    {
      CM.num = (fun _ -> t.num);
      CM.bool = (fun _ -> t.bool);
      CM.hole = (fun _ -> t.hole);
      CM.lambda = (fun _ _ -> t.lambda);
      CM._let = (fun _ _ -> t._let);
      CM.list = (fun _ -> t.list);
      CM.tree = (fun _ -> t.tree);
      CM.apply = (fun _ _ -> 0);
      CM.op = (fun op _ -> lookup_func (Expr.Op.to_string op));
      CM.id = (function
          | Skeleton.Id.Name op -> lookup_func op
          | Skeleton.Id.StaticDistance sd -> t.var);
    }
  
  let to_json t =
    let call_to_json m =
      String.Map.to_alist m
      |> List.map ~f:(fun (k, v) -> k, `Int v)
    in
    `Assoc [
      "num", `Int t.num;
      "bool", `Int t.bool;
      "hole", `Int t.hole;
      "lambda", `Int t.lambda;
      "let", `Int t._let;
      "list", `Int t.list;
      "tree", `Int t.tree;
      "var", `Int t.var;
      "call", `Assoc (call_to_json t.call);
      "call_default", `Int t.call_default;
    ]

  let of_json : Json.json -> t = fun json ->
    let call_of_json m =
      List.map m ~f:(fun (k, v_json) ->
          match v_json with
          | `Int v -> k, v
          | _ -> failwiths "Expected an Int." v_json [%sexp_of:Json.json])
      |> String.Map.of_alist_exn
    in
    let lookup key assoc =
      match List.Assoc.find assoc ~equal:String.equal key with
      | Some v -> v
      | None -> failwiths "Missing key." (key, assoc) [%sexp_of:string * (string * Json.json) list]
    in
    let int = function
      | `Int x -> x
      | json -> failwiths "Expected an int." json [%sexp_of:Json.json]
    in
    let string_int_map = function
      | `Assoc x -> call_of_json x
      | json -> failwiths "Expected a mapping from string to int." json [%sexp_of:Json.json]
    in
      
    match json with
    | `Assoc kv ->
      {
        num = lookup "num" kv |> int;
        bool = lookup "bool" kv |> int;
        hole = lookup "hole" kv |> int;
        lambda = lookup "lambda" kv |> int;
        _let = lookup "let" kv |> int;
        list = lookup "list" kv |> int;
        tree = lookup "tree" kv |> int;
        var = lookup "var" kv |> int;
        call = lookup "call" kv |> string_int_map;
        call_default = lookup "call_default" kv |> int;
      }
    | _ -> failwiths "Unexpected JSON." json [%sexp_of:Json.json]
end

module Specification = struct
  module Examples = struct
    module Input = struct
      module T = struct
        type t = Ast.value StaticDistance.Map.t [@@deriving sexp, compare]
      end
      include T
      include Comparable.Make(T)
    end

    type example = (Input.t * Ast.value) [@@deriving sexp, compare]
    type t = example list [@@deriving sexp, compare]

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

    let singleton : example -> t = fun ex -> [ex]
    let of_list_exn exs = of_list exs |> Or_error.ok_exn
    let to_list t = t

    let context = function
      | [] -> []
      | (inp, out)::_ -> StaticDistance.Map.keys inp
  end

  module FunctionExamples = struct
    module Input = struct
      module T = struct
        type t = Ast.value StaticDistance.Map.t * Ast.value list [@@deriving sexp, compare]
      end
      include T
      include Comparable.Make(T)
    end

    type example = (Input.t * Ast.value) [@@deriving sexp, compare]
    type t = example list [@@deriving sexp, compare]

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

    let singleton : example -> t = fun ex -> [ex]
    let of_list_exn exs = of_list exs |> Or_error.ok_exn    
    let to_list t = t
  end

  module T = struct 
    type t =
      | Bottom
      | Top
      | Examples of Examples.t
      | FunctionExamples of FunctionExamples.t
      [@@deriving compare, sexp]
  end
  include T

  let hash = Hashtbl.hash
  let compare = compare_t
  let equal s1 s2 = compare s1 s2 = 0

  let to_string s = Sexp.to_string (sexp_of_t s)

  let verify : ?library:Library.t -> t -> 'a Skeleton.t -> bool =
    fun ?(library=Library.empty) spec skel -> match spec with
      | Top -> true
      | Bottom -> false
      | Examples exs ->
        (try
           List.for_all exs ~f:(fun (in_ctx, out) ->
               let fresh_name = Fresh.mk_fresh_name_fun () in
               let name_ctx = StaticDistance.Map.map in_ctx ~f:(fun _ -> fresh_name ()) in
               let id_ctx = StaticDistance.Map.map name_ctx ~f:(fun name -> `Id name) in
               let expr = Skeleton.to_expr_exn ~ctx:id_ctx ~fresh_name skel in
               let value_ctx =
                 StaticDistance.Map.to_alist in_ctx
                 |> List.map ~f:(fun (k, v) -> StaticDistance.Map.find_exn name_ctx k, v)
                 |> Ctx.of_alist_exn
                 |> Ctx.merge_right (Ctx.of_string_map library.Library.value_ctx)
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
               let id_ctx = StaticDistance.Map.map name_ctx ~f:(fun name -> `Id name) in
               let expr =
                 `Apply (Skeleton.to_expr_exn ~ctx:id_ctx ~fresh_name skel,
                         List.map in_args ~f:Expr.of_value)
               in
               let value_ctx =
                 StaticDistance.Map.to_alist in_ctx
                 |> List.map ~f:(fun (k, v) -> StaticDistance.Map.find_exn name_ctx k, v)
                 |> Ctx.of_alist_exn
                 |> Ctx.merge_right (Ctx.of_string_map library.Library.value_ctx)
               in
               Eval.eval ~recursion_limit:100 value_ctx expr = out)
         with
         | Eval.HitRecursionLimit
         | Eval.RuntimeError _ -> false)

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

  include Comparable.Make(T)
end

module Hypothesis = struct
  module Sk = Skeleton
  module Sp = Specification
    
  type skeleton = Sp.t Sk.t

  let compare_skel : skeleton -> skeleton -> int = Sk.compare Sp.compare
  
  module Table = Hashcons.Make(struct
      type t = skeleton
      let equal h1 h2 = compare_skel h1 h2 = 0
      let hash = Sk.hash
    end)

  type kind =
    | Abstract
    | Concrete
    [@@deriving sexp]

  (* module HoleList = SortedList.Make_using_comparator(struct *)
  (*     type t = Hole.t * Sp.t *)
  (*     include Comparator.Make (struct *)
  (*         type t = Hole.t * Sp.t [@@deriving sexp] *)
  (*         let compare (h1, _) (h2, _) = Hole.compare h1 h2 *)
  (*       end) *)
  (*   end) *)

  type t = {
    skeleton : skeleton Hashcons.hash_consed;
    cost : int;
    kind : kind;
    holes : (Hole.t * Sp.t) list;
  }

  let table = Table.create 100

  let skeleton h = h.skeleton.Hashcons.node
  let cost h = h.cost
  let kind h = h.kind
  let holes h = h.holes
  let spec h = Sk.annotation (skeleton h)

  let sexp_of_t h =
    let open Sexp in
    List [
      List [ Atom "skeleton"; Sk.sexp_of_t Sp.sexp_of_t (skeleton h) ];
      List [ Atom "cost"; sexp_of_int h.cost ];
      List [ Atom "kind"; sexp_of_kind h.kind ];
      List [
        Atom "holes";
        sexp_of_list (fun (hole, spec) ->
            List [ Hole.sexp_of_t hole; Sp.sexp_of_t spec ]) h.holes
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
        skeleton = Table.hashcons table ([%of_sexp:Sp.t Sk.t] skel_s);
        cost = Int.t_of_sexp cost_s;
        kind = kind_of_sexp kind_s;
        holes = [%of_sexp:(Hole.t * Sp.t) list] holes_s;
      }
    | _ -> raise (Sexp.Of_sexp_error (Failure "Sexp has the wrong format.", s))

  let compare_skeleton h1 h2 = compare_skel h1.skeleton.Hashcons.node h2.skeleton.Hashcons.node
  let compare_cost h1 h2 = Int.compare h1.cost h2.cost

  let to_expr (h: t) : Expr.t =
    match h.kind with
    | Abstract -> failwith "Tried to convert an abstract hypothesis to an expression."
    | Concrete -> Sk.to_expr_exn (skeleton h)

  let to_string h = Sexp.to_string_hum (sexp_of_t h)
  let to_string_hum h = Sk.to_string_hum (skeleton h)

  let apply_unifier h u =
    {
      h with
      holes = List.map h.holes ~f:(fun (h, s) -> (Hole.apply_unifier u h, s));
      skeleton = Table.hashcons table
          (Sk.map_hole (skeleton h) ~f:(fun (hole, spec) -> 
               Sk.Hole_h (Hole.apply_unifier u hole, spec)))
    }

  let fill_hole cm hole ~parent:p ~child:c = begin
    if not (List.exists p.holes ~f:(fun (h, _) -> Hole.equal_id h hole)) then
      failwith "Hypothesis does not contain the specified hole.";
    let holes =
      (List.filter p.holes ~f:(fun (h, _) -> not (Hole.equal_id h hole))) @ c.holes
    in
    {
      skeleton = Table.hashcons table
          (Sk.fill_hole hole ~parent:(skeleton p) ~child:(skeleton c));
      cost = p.cost + c.cost - cm.CostModel.hole hole;
      kind = if List.length holes = 0 then Concrete else Abstract;
      holes;
    }
  end

  let verify : ?library:Library.t -> t -> bool =
    fun ?(library = Library.empty) h -> Sp.verify ~library (spec h) (skeleton h)

  let of_skeleton cm s =
    let holes = Sk.holes s in
    {
      skeleton = Table.hashcons table s;
      kind = if List.length holes = 0 then Concrete else Abstract;
      cost = CostModel.cost_of_skeleton cm s;
      holes;
    }

  module C = CostModel
  
  let num cm x s : t = {
    skeleton = Table.hashcons table (Sk.Num_h (x, s));
    cost = cm.C.num x;
    kind = Concrete;
    holes = [];
  }
  let bool cm x s : t = {
    skeleton = Table.hashcons table (Sk.Bool_h (x, s));
    cost = cm.C.bool x;
    kind = Concrete;
    holes = [];
  }
  let id_sd cm x s : t =
    let id = Sk.Id.StaticDistance x in
    {
      skeleton = Table.hashcons table (Sk.Id_h (id, s));
      cost = cm.C.id id;
      kind = Concrete;
      holes = [];
    }
  let hole cm x s : t = {
    skeleton = Table.hashcons table (Sk.Hole_h (x, s));
    cost = cm.C.hole x;
    kind = Abstract;
    holes = [ (x, s) ];
  }
  let list cm (x: t list) s : t =
    let skel_x = List.map x ~f:skeleton in
    {
      skeleton = Table.hashcons table (Sk.List_h (skel_x, s));
      cost = cm.C.list skel_x + List.int_sum (List.map x ~f:cost);
      kind = if List.exists x ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat_map x ~f:holes;
    }
  let tree cm x s : t =
    let flat = Tree.flatten x in
    let skel_tree = Tree.map x ~f:skeleton in
    {
      skeleton = Table.hashcons table (Sk.Tree_h (skel_tree, s));
      cost = cm.C.tree skel_tree + List.int_sum (List.map flat ~f:cost);
      kind = if List.exists flat ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat_map flat ~f:holes;
    }
  let _let cm bound body s : t =
    let sk_bound, sk_body = skeleton bound, skeleton body in
    {
      skeleton = Table.hashcons table (Sk.Let_h ((sk_bound, sk_body), s));
      cost = cm.C._let sk_bound sk_body + bound.cost + body.cost;
      kind = if bound.kind = Abstract || body.kind = Abstract then Abstract else Concrete;
      holes = bound.holes @ body.holes;
    }
  let lambda cm num_args body s : t =
    let sk_body = skeleton body in
    {
      skeleton = Table.hashcons table (Sk.Lambda_h ((num_args, sk_body), s));
      cost = cm.C.lambda num_args sk_body + body.cost;
      kind = if body.kind = Abstract then Abstract else Concrete;
      holes = body.holes;
    }
  let apply cm func args s : t =
    let sk_func, sk_args = skeleton func, List.map args ~f:skeleton in
    {
      skeleton = Table.hashcons table
          (Sk.Apply_h ((sk_func, sk_args), s));
      cost = cm.C.apply sk_func sk_args + cost func + List.int_sum (List.map args ~f:cost);
      kind =
        if func.kind = Abstract || List.exists args ~f:(fun h -> h.kind = Abstract) then
          Abstract else Concrete;
      holes = func.holes @ (List.concat_map args ~f:holes);
    }
  let id_name cm x s : t = {
    skeleton = Table.hashcons table (Sk.Id_h (Sk.Id.Name x, s));
    cost = cm.C.id (Sk.Id.Name x);
    kind = Concrete;
    holes = [];
  }
  let op cm op args s : t =
    let sk_args = List.map args ~f:skeleton in
    {
      skeleton = Table.hashcons table (Sk.Op_h ((op, List.map args ~f:skeleton), s));
      cost = cm.C.op op sk_args + List.int_sum (List.map args ~f:cost);
      kind = if List.exists args ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat_map args ~f:holes;
    }
end
