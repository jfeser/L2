open Core
open Core_extended.Std

open Collections
open Infer
open Util

module StaticDistance = struct
  module T = struct
    type t = int * int [@@deriving compare, sexp]
  end

  include T

  module C = Comparable.Make(T)
  include (C : module type of C with module Map := C.Map)
    
  let create ~distance ~index =
    let open Int in
    if distance <= 0 || index <= 0 then
      raise (Invalid_argument "Argument out of range.")
    else
      (distance, index)

  let distance x = let (a, _) = x in a
  let index x = let (_, b) = x in b

  let increment_scope x =
    let (a, b) = x in
    (a + 1, b)

  let args num =
    List.range ~stride:1 ~start:`inclusive ~stop:`inclusive 1 num
    |> List.map ~f:(fun i -> (1, i))

  let to_string x =
    let (a, b) = x in
    sprintf "%d_%d" a b

  module Map = struct
    include C.Map

    let increment_scope : 'a t -> 'a t = fun x ->
      to_alist x
      |> List.map ~f:(fun (k, v) -> (increment_scope k, v))
      |> of_alist_exn

    let to_string : ('a -> string) -> 'a t -> string = fun ts m ->
      let str =
        to_alist m
        |> List.map ~f:(fun (k, v) -> sprintf "%s : %s" (to_string k) (ts v))
        |> String.concat ~sep:", "
      in
      "{ " ^ str ^ " }"
  end
  
  let map_increment_scope = Map.increment_scope
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
  type t = {
    id  : int;
    ctx : Type.t StaticDistance.Map.t;
    type_ : Type.t;
    symbol : Symbol.t;
  } [@@deriving sexp, compare]

  let counter = ref 0

  let equal h1 h2 = compare h1 h2 = 0
  let equal_id h1 h2 = h1.id = h2.id
  let hash = Hashtbl.hash
  
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

    let hash = Hashtbl.hash

    include T
    include Comparable.Make(T)
  end

  type spec_data = ..

  type ast =
    | Num    of int
    | Bool   of bool
    | List   of t list
    | Tree   of t Tree.t
    | Id     of Id.t
    | Hole   of Hole.t
    | Let    of { bound : t; body : t }
    | Lambda of { num_args : int; body : t }
    | Apply  of { func : t; args : t list }
    | Op     of { op : Expr.Op.t; args : t list }
  and spec = {
    verify : Library.t -> t -> bool;
    compare : spec -> int;
    to_sexp : unit -> Sexp.t;
    to_string : unit -> string;
    data : spec_data;
  }
  and skel = {
    spec : spec;
    ast : ast;
  }
  and t = skel Hashcons.hash_consed

  let compare s1 s2 = Int.compare s1.Hashcons.tag s2.Hashcons.tag
  let equal s1 s2 = compare s1 s2 = 0

  let compare_spec : spec -> spec -> int = fun s1 s2 ->
    (* Each specification variant has a comparison function that
       puts a total order on specifications of that variant. To get a
       total order on all specifications, we need an order on
       variants. Here, we use the extension ids to get that
       ordering. *)
    let get_id spec = spec |> Obj.extension_constructor |> Obj.extension_id in
    let cmp = Int.compare (get_id s1.data) (get_id s2.data) in
    if cmp = 0 then s1.compare s2 else cmp
      
  let equal_spec s1 s2 = compare_spec s1 s2 = 0
  
  let rec sexp_of_ast =
    let module S = Sexp in
    function
    | Num x -> S.List [S.Atom "Num"; [%sexp_of:int] x]
    | Bool x -> S.List [S.Atom "Bool"; [%sexp_of:bool] x]
    | List x -> S.List [S.Atom "List"; [%sexp_of:t list] x]
    | Tree x -> S.List [S.Atom "Tree"; [%sexp_of:t Tree.t] x]
    | Id x -> S.List [S.Atom "Id"; [%sexp_of:Id.t] x]
    | Hole x -> S.List [S.Atom "Hole"; [%sexp_of:Hole.t] x]
    | Let { bound; body } ->
      S.List [S.Atom "Let"; [%sexp_of:t] bound; [%sexp_of:t] body]
    | Lambda { num_args; body } ->
      S.List [S.Atom "Lambda"; [%sexp_of:int] num_args; [%sexp_of:t] body]
    | Apply { func; args } ->
      S.List [S.Atom "Apply"; [%sexp_of:t] func; [%sexp_of:t list] args]
    | Op { op; args } ->
      S.List [S.Atom "Op"; [%sexp_of:Expr.Op.t] op; [%sexp_of:t list] args]
                 
  and sexp_of_spec sp = sp.to_sexp ()

  and sexp_of_skel : skel -> Sexp.t =
    let open Sexp in
    fun { spec; ast } ->
      List [ [%sexp_of:ast] ast; [%sexp_of:spec] spec ]
    
  and sexp_of_t : t -> Sexp.t =
    fun sk -> [%sexp_of:skel] sk.Hashcons.node

  let t_of_sexp _ = failwith "Implement me!"

  (** Hashconsing table for storing skeletons. *)
  module Table = struct
      let counter =
        let c = Counter.empty () in
        let n = Counter.add_zero c in
        n "equal" "Number of calls to Skeleton.equal.";
        n "equal_true" "Number of calls to Skeleton.equal returning true.";
        n "equal_false" "Number of calls to Skeleton.equal returning true.";
        n "hash" "Number of calls to Skeleton.hash.";
        n "hashcons" "Number of calls to Hypothesis.Table.hashcons.";
        c

      include Hashcons.Make(struct
          type t = skel

          (* Can only use physical equality on sub-terms. *)
          let equal_t = phys_equal

          let equal_ast h1 h2 =
            match h1, h2 with
            | Num x, Num y -> x = y
            | Bool x, Bool y -> x = y
            | Id x, Id y -> x = y
            | Hole x, Hole y -> Hole.equal_id x y
            | List x, List y -> List.equal x y ~equal:equal_t
            | Tree x, Tree y -> Tree.equal x y ~equal:equal_t
            | Let { bound = x1; body = x2 },
              Let { bound = y1; body = y2 } -> equal_t x1 y1 && equal_t x2 y2
            | Lambda { num_args = x1; body = x2 },
              Lambda { num_args = y1; body = y2 } ->
              equal_t x1 y1 && equal_t x2 y2
            | Apply { func = x1; args = x2 }, Apply { func = y1; args = y2 } ->
              equal_t x1 y1 && List.equal x2 y2 ~equal:equal_t
            | Op { op = x1; args = x2 }, Op { op = y1; args = y2 } ->
              equal_t x1 y1 && List.equal x2 y2 ~equal:equal_t
            | _ -> false

          let equal_skel s1 s2 =
            equal_ast s1.ast s2.ast && equal_spec s1.spec s2.spec

          let hash_t s = s.Hashcons.hkey
                           
          let hash_spec = Hashtbl.hash
                            
          let hash_ast = function
            | Num x -> Int.hash x
            | Bool x -> Bool.hash x
            | List x -> List.hash x ~hash_elem:hash_t
            | Tree x -> Tree.hash x ~hash_elem:hash_t
            | Id x -> Id.hash x
            | Hole x -> Hole.hash x
            | Let { bound; body } -> Hash.combine (hash_t bound) (hash_t body)
            | Lambda { num_args; body } ->
              Hash.combine (Int.hash num_args) (hash_t body)
            | Apply { func; args } ->
              Hash.combine (hash_t func) (List.hash args ~hash_elem:hash_t)
            | Op { op; args } ->
              Hash.combine (Expr.Op.hash op) (List.hash args ~hash_elem:hash_t)
                
          let hash_skel sk = Hash.combine (hash_spec sk.spec) (hash_ast sk.ast)
              
          let equal h1 h2 =
            Counter.incr counter "equal";
            let ret = equal_skel h1 h2 in
            if ret then
              Counter.incr counter "equal_true"
            else
              Counter.incr counter "equal_false";
            ret

          let hash h = 
            Counter.incr counter "hash";
            hash_skel h
        end)

    let hashcons t k =
      Counter.incr counter "hashcons"; hashcons t k
  end
  let table = Table.create 49157
  let () =
    let nf = Counter.add_func Table.counter in
    nf "table_len" "" (fun () -> let (x, _, _, _, _, _) = Table.stats table in x);
    nf "num_entries" "" (fun () -> let (_, x, _, _, _, _) = Table.stats table in x);
    nf "sum_bucket_len" "" (fun () -> let (_, _, x, _, _, _) = Table.stats table in x);
    nf "min_bucket_len" "" (fun () -> let (_, _, _, x, _, _) = Table.stats table in x);
    nf "med_bucket_len" "" (fun () -> let (_, _, _, _, x, _) = Table.stats table in x);
    nf "max_bucket_len" "" (fun () -> let (_, _, _, _, _, x) = Table.stats table in x)

  (** Accessor functions for record fields. *)
  let ast sk = sk.Hashcons.node.ast
  let spec sk = sk.Hashcons.node.spec

  (** Constructor functions which correctly compute hashes. *)
  let node sk = sk.Hashcons.node

  let num x s = Table.hashcons table { ast = Num x; spec = s }
  let bool x s = Table.hashcons table { ast = Bool x; spec = s }
  let list x s = Table.hashcons table { ast = List x; spec = s }
  let tree x s = Table.hashcons table { ast = Tree x; spec = s }
  let id x s = Table.hashcons table { ast = Id x; spec = s }
  let hole x s = Table.hashcons table { ast = Hole x; spec = s }
  let let_ bound body s =
    Table.hashcons table { ast = Let { bound; body }; spec = s }
  let lambda num_args body s =
    Table.hashcons table { ast = Lambda { num_args; body }; spec = s }
  let apply func args s =
    Table.hashcons table { ast = Apply { func; args }; spec = s }
  let op op args s =
    Table.hashcons table { ast = Op { op; args }; spec = s }

  (** Replacement functions for record fields. *)
  let replace_spec sk spec = Table.hashcons table { sk.Hashcons.node with spec }
  
  let rec to_pp : ?indent:int -> t -> Pp.t =
    let module SD = StaticDistance in
    let module O = Expr.Op in
    let open Pp in
    fun ?(indent=4) ->
      let fresh_name = Util.Fresh.mk_fresh_name_fun () in
      
      let rec to_pp ?(parens = false) names sk =
        let apply_parens pp = if parens then text "(" $ pp $ text ")" else pp in
        
        let infix_op op x1 x2 =
          let pp =
            to_pp ~parens:true names x1 $/
            text op $/
            to_pp ~parens:true names x2
          in
          apply_parens pp
        in
        
        match ast sk with
        | Num x -> text (Int.to_string x)
        | Bool x -> text (Bool.to_string x)
        | List l -> text "[" $ list ~sep:(text ";" $ break) ~f:(to_pp names) l $ text "]"
        | Tree _ -> text "<tree>"
        | Id (Id.StaticDistance x) ->
          begin match Map.find names x with
            | Some name -> text name
            | None -> text (SD.to_string x)
          end
        | Id (Id.Name x) -> text x
                              
        | Let { bound; body } ->
          let name = fresh_name () in
          let names =
            SD.map_increment_scope names
            |> Map.add ~key:(SD.create ~distance:1 ~index:1) ~data:name
          in
          let pp =
            text "let" $/ text name $/ text "=" $/
            nest indent (to_pp names bound) $/ text "in" $/
            to_pp names body
          in
          apply_parens pp
            
        | Lambda { num_args; body } ->
          let new_names =
            List.init num_args ~f:(fun i ->
                SD.create ~distance:1 ~index:(i + 1), fresh_name ())
          in
          let names =
            List.fold ~f:(fun m (sd, name) -> Map.add m ~key:sd ~data:name)
              new_names ~init:(SD.map_increment_scope names)
          in
          let pp =
            text "fun" $/ list ~sep:break ~f:(fun (_, n) -> text n) new_names $/ text "->" $/
            nest indent (to_pp names body)
          in
          apply_parens pp
            
        | Apply { func; args } ->
          let pp =
            to_pp names func $/ list ~sep:break ~f:(to_pp ~parens:true names) args
          in
          apply_parens pp

        | Op { op = O.Plus as op; args = [x1; x2] }
        | Op { op = O.Minus as op; args = [x1; x2] }
        | Op { op = O.Mul as op; args = [x1; x2] }
        | Op { op = O.Div as op; args = [x1; x2] }
        | Op { op = O.Mod as op; args = [x1; x2] }
        | Op { op = O.Eq as op; args = [x1; x2] }
        | Op { op = O.Neq as op; args = [x1; x2] }
        | Op { op = O.Gt as op; args = [x1; x2] }
        | Op { op = O.Geq as op; args = [x1; x2] }
        | Op { op = O.Lt as op; args = [x1; x2] }
        | Op { op = O.Leq as op; args = [x1; x2] } ->
          infix_op (Expr.Op.to_string op) x1 x2
        | Op { op = O.Cons; args = [x1; x2] } -> infix_op "::" x1 x2
        | Op { op = O.RCons; args = [x1; x2] } -> infix_op "::" x2 x1
        | Op { op = O.And; args = [x1; x2] } -> infix_op "&&" x1 x2
        | Op { op = O.Or; args = [x1; x2] } -> infix_op "||" x1 x2
        | Op { op = O.Not; args = [x] } ->
          let pp = text "not" $/ to_pp ~parens:true names x in
          apply_parens pp
        | Op { op = O.If; args = [x1; x2; x3] } ->
          let pp =
            text "if" $/ to_pp ~parens:true names x1 $/
            text "then" $/ to_pp ~parens:true names x2 $/
            text "else" $/ to_pp ~parens:true names x3
          in
          apply_parens pp
        | Op { op; args } -> 
          let pp =
            text (Expr.Op.to_string op) $/
            list ~sep:break ~f:(to_pp ~parens:true names) args
          in
          apply_parens pp

        | Hole hole -> text ((Int.to_string hole.Hole.id) ^ "?")
      in
      to_pp SD.Map.empty

  let rec to_string_hum : t -> string =
    fun s -> to_pp s |> Pp.to_string
  
  let to_expr :
    ?ctx:Expr.t StaticDistance.Map.t
    -> ?fresh_name:(unit -> string)
    -> ?of_hole:(Hole.t -> Expr.t)
    -> t
    -> Expr.t =
    let module SD = StaticDistance in
    fun ?(ctx = SD.Map.empty) ?fresh_name ?of_hole s ->
      let of_hole = match of_hole with
        | Some f -> f
        | None -> fun _ ->
          failwiths "Unexpected hole." s (fun s -> [%sexp_of:string] (to_string_hum s))
      in
      let fresh_name = match fresh_name with
        | Some f -> f
        | None -> Fresh.mk_fresh_name_fun ()
      in

      let rec to_expr ctx sk =
        match ast sk with
        | Num x -> `Num x
        | Bool x -> `Bool x
        | Id (Id.StaticDistance x) ->
          begin
            match Map.find ctx x with
            | Some expr -> expr
            | None ->
              failwiths "Context does not contain coordinate." (s, x, ctx) 
                (Tuple.T3.sexp_of_t
                   (fun _ -> Sexp.Atom "Implement sexp_of_skeleton")
                   [%sexp_of:SD.t]
                   [%sexp_of:Expr.t SD.Map.t])
          end
        | Id (Id.Name x) -> `Id x
        | List elems -> `List (List.map elems ~f:(to_expr ctx))
        | Tree elems -> `Tree (Tree.map elems ~f:(to_expr ctx))
        | Let { bound; body } ->
          let name = fresh_name () in
          let ctx =
            SD.Map.increment_scope ctx
            |> Map.add ~key:(SD.create ~distance:1 ~index:1) ~data:(`Id name)
          in
          `Let (name, to_expr ctx bound, to_expr ctx body)
        | Lambda { num_args; body } ->
          let ctx = SD.Map.increment_scope ctx in
          let arg_names = List.init num_args ~f:(fun _ -> fresh_name ()) in
          let ctx =
            List.fold2_exn arg_names (SD.args num_args) ~init:ctx
              ~f:(fun ctx name sd -> Map.add ctx ~key:sd ~data:(`Id name))
          in
          `Lambda (arg_names, to_expr ctx body)
        | Apply { func; args } ->
          `Apply (to_expr ctx func, List.map ~f:(to_expr ctx) args)
        | Op { op; args } ->
          `Op (op, List.map ~f:(to_expr ctx) args)
        | Hole x -> of_hole x
      in
      to_expr ctx s

  let to_expr_exn ?(ctx = StaticDistance.Map.empty) ?(fresh_name) s =
    to_expr ~ctx ?fresh_name s
      
  let rec map_hole ~f sk =
    let spec = spec sk in
    match ast sk with
    | Num _
    | Bool _
    | Id _ -> sk
    | List x -> let x' = List.map ~f:(map_hole ~f) x in list x' spec
    | Tree x -> let x' = Tree.map ~f:(map_hole ~f) x in tree x' spec
    | Let { bound; body } -> let_ (map_hole ~f bound) (map_hole ~f body) spec
    | Lambda { num_args; body } -> lambda num_args (map_hole ~f body) spec
    | Apply { func; args } ->
      apply (map_hole ~f func) (List.map ~f:(map_hole ~f) args) spec
    | Op { op = op'; args } -> op op' (List.map ~f:(map_hole ~f) args) spec
    | Hole h -> hole (f h) spec

  let fill_hole h ~parent ~child =
    let rec fill h ~child parent = 
      let spec = spec parent in
      match ast parent with
      | Num _
      | Bool _
      | Id _ -> parent
      | List x -> list (List.map ~f:(fill h ~child) x) spec
      | Tree x -> tree (Tree.map ~f:(fill h ~child) x) spec
      | Let { bound; body } ->
        let_ (fill h ~child bound) (fill h ~child body) spec
      | Lambda { num_args; body } -> lambda num_args (fill h ~child body) spec
      | Apply { func; args } ->
        apply (fill h ~child func) (List.map ~f:(fill h ~child) args) spec
      | Op { op = op'; args } ->
        op op' (List.map ~f:(fill h ~child) args) spec
      | Hole h' -> if Hole.equal_id h h' then child else parent
    in
    fill h parent ~child
      
  let rec holes sk =
    match ast sk with
    | Num _
    | Bool _
    | Id _ -> []
    | List x -> List.concat_map x ~f:holes
    | Tree x -> Tree.flatten x |> List.concat_map ~f:holes
    | Let { bound; body } -> (holes bound) @ (holes body)
    | Lambda { body } -> holes body
    | Apply { func; args } -> (holes func) @ (List.concat_map args ~f:holes)
    | Op { args } -> List.concat_map args ~f:holes
    | Hole hole -> [ (hole, spec sk) ]
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
    let open Skeleton in
    let rec cost sk =
      match ast sk with
      | Num x -> cm.num x
      | Bool x -> cm.bool x
      | Hole x -> cm.hole x
      | Id x -> cm.id x
      | List x -> cm.list x + List.int_sum (List.map x ~f:cost)
      | Tree x -> cm.tree x + List.int_sum (List.map (Tree.flatten x) ~f:cost)
      | Let { bound = x; body = y } -> cm._let x y + cost x + cost y
      | Lambda { num_args = x; body = y } -> cm.lambda x y + cost y
      | Apply { func = x; args = y } ->
        cm.apply x y + cost x + List.int_sum (List.map y ~f:cost)
      | Op { op = x; args = y } ->
        cm.op x y + List.int_sum (List.map y ~f:cost)
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

module Specification0 = struct
  module T = struct 
    type data = Skeleton.spec_data = ..

    type t = Skeleton.spec = {
      verify : Library.t -> Skeleton.t -> bool;
      compare : t -> int;
      to_sexp : unit -> Sexp.t;
      to_string : unit -> string;
      data : data;
    }

    let sexp_of_t : t -> Sexp.t = fun t -> t.Skeleton.to_sexp ()
    let t_of_sexp : Sexp.t -> t = fun _ -> failwith "Unimplemented."
    let compare : t -> t -> int = Skeleton.compare_spec
    let equal : t -> t -> bool = Skeleton.equal_spec
  end
  include T

  type data +=
    | Top
    | Bottom

  let to_string s = s.to_string ()

  let verify : 'a. t -> ?library:Library.t -> Skeleton.t -> bool =
    fun spec ?(library=Library.empty) skel -> spec.verify library skel

  let data : t -> data = fun t -> t.data

  let top =
    let verify _ _ = true in
    let compare t = match t.data with
      | Top -> 0
      | _ -> failwith "BUG: Unexpected spec variant."
    in
    let to_string () = "T" in
    let to_sexp () = Sexp.Atom "Top" in
    let data = Top in
    { verify; compare; to_sexp; to_string; data }

  let bottom =
    let verify _ _ = false in
    let compare t = match t.data with
      | Bottom -> 0
      | _ -> failwith "BUG: Unexpected spec variant."
    in
    let to_string () = "⊥" in
    let to_sexp () = Sexp.Atom "Bottom" in
    let data = Bottom in
    { verify; compare; to_sexp; to_string; data }
end

module Examples = struct
  module S = Specification0
  module SD = StaticDistance
    
  module Input = struct
    module T = struct
      type t = Ast.value SD.Map.t [@@deriving sexp, compare]
    end
    include T
    include Comparable.Make(T)
  end

  type example = (Input.t * Ast.value) [@@deriving sexp, compare]

  type t = example list [@@deriving sexp, compare]

  type S.data += Examples of t

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

  let singleton : example -> t = fun ex -> [ex]
  
  let context = function
    | [] -> []
    | (inp, out)::_ -> Map.keys inp

  let to_spec : t -> S.t = fun exs ->
    let verify library skel =
      try
        List.for_all exs ~f:(fun (in_ctx, out) ->
            let fresh_name = Fresh.mk_fresh_name_fun () in
            let name_ctx = Map.map in_ctx ~f:(fun _ -> fresh_name ()) in
            let id_ctx = Map.map name_ctx ~f:(fun name -> `Id name) in
            let expr = Skeleton.to_expr_exn ~ctx:id_ctx ~fresh_name skel in
            let value_ctx =
              Map.to_alist in_ctx
              |> List.map ~f:(fun (k, v) -> Map.find_exn name_ctx k, v)
              |> Ctx.of_alist_exn
              |> Ctx.merge_right (Ctx.of_string_map library.Library.value_ctx)
            in
            Eval.eval ~recursion_limit:100 value_ctx expr = out)
      with
      | Eval.HitRecursionLimit
      | Eval.RuntimeError _ -> false
    in

    let compare t = match t.S.data with
      | Examples exs' -> compare exs exs'
      | _ -> failwith "BUG: Unexpected spec variant."
    in

    let to_sexp () = sexp_of_t exs in
    let to_string () =
      List.map exs ~f:(fun (i, o) ->
          sprintf "%s -> %s" (SD.Map.to_string Value.to_string i) (Value.to_string o))
      |> String.concat ~sep:"\n"
    in
    let data = Examples exs in

    { S.verify; S.compare; S.to_sexp; S.to_string; S.data }
end

module FunctionExamples = struct
  module S = Specification0

  module SD = StaticDistance
    
  module Input = struct
    module T = struct
      type t = Ast.value SD.Map.t * Ast.value list [@@deriving sexp, compare]
    end
    include T
    include Comparable.Make(T)
  end

  type example = (Input.t * Ast.value) [@@deriving sexp, compare]
  type t = example list [@@deriving sexp, compare]
  type S.data += FunctionExamples of t

  let of_list exs =
    let module I = Input in
    let open Or_error in
    List.fold exs ~init:(Ok I.Map.empty) ~f:(fun m ((ctx, args), ret) ->
        let key = (ctx, args) in
        m >>= fun m ->
        match Map.find m key with
        | Some ret' when ret' = ret -> Ok m
        | Some _ -> error_string "Different return value for same input."
        | None -> Ok (Map.add m ~key ~data:ret))
    |> ignore
    >>| fun () -> List.dedup ~compare:compare_example exs
  let of_list_exn exs = of_list exs |> Or_error.ok_exn    

  let of_input_output_list : (Value.t list * Value.t) list -> t Or_error.t =
    fun io ->
      List.map io ~f:(fun (i, o) -> (SD.Map.empty, i), o)
      |> of_list
  let of_input_output_list_exn : (Value.t list * Value.t) list -> t = 
    fun io -> of_input_output_list io |> Or_error.ok_exn
  
  let singleton : example -> t = fun ex -> [ex]
  let to_list t = t

  let to_spec : t -> S.t = fun exs ->
    let verify library skel =
      try
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
      | Eval.RuntimeError _ -> false
    in

    let compare t = match t.S.data with
      | FunctionExamples exs' -> compare exs exs'
      | _ -> failwith "BUG: Unexpected spec variant."
    in

    let to_sexp () = sexp_of_t exs in

    let to_string () =
      List.map exs ~f:(fun ((ctx, args), o) ->
          let ctx = SD.Map.to_string Value.to_string ctx in
          let args =
            List.map args ~f:Value.to_string
            |> String.concat ~sep:", "
          in
          sprintf "%s (%s) -> %s" ctx args (Value.to_string o))
      |> String.concat ~sep:"\n"
    in

    let data = FunctionExamples exs in

    { S.verify; S.compare; S.to_sexp; S.to_string; S.data }
end

module Inputs = struct
  module S = Specification0
  module SD = StaticDistance

  type t = Value.t SD.Map.t list [@@deriving sexp, compare]

  type S.data += Inputs of t

  let of_examples : Examples.t -> t = fun exs ->
    exs |> List.map ~f:Tuple.T2.get1

  let signature : Library.t -> Skeleton.t -> t -> Value.t list option =
    fun library skel exs ->
      try
        List.map exs ~f:(fun ctx ->
            let fresh_name = Fresh.mk_fresh_name_fun () in
            let name_ctx = Map.map ctx ~f:(fun _ -> fresh_name ()) in
            let id_ctx = Map.map name_ctx ~f:(fun name -> `Id name) in
            let expr = Skeleton.to_expr_exn ~ctx:id_ctx ~fresh_name skel in
            let value_ctx =
              Map.to_alist ctx
              |> List.map ~f:(fun (k, v) -> Map.find_exn name_ctx k, v)
              |> Ctx.of_alist_exn
              |> Ctx.merge_right (Ctx.of_string_map library.Library.value_ctx)
            in
            Eval.eval ~recursion_limit:100 value_ctx expr)
        |> Option.some
      with
      | Eval.HitRecursionLimit
      | Eval.RuntimeError _ -> None
  
  let to_spec : t -> S.t = fun exs ->
    let verify library skel = signature library skel exs |> Option.is_some in

    let compare t = match t.S.data with
      | Inputs exs' -> compare exs exs'
      | _ -> failwith "BUG: Unexpected spec variant."
    in

    let to_sexp () = sexp_of_t exs in
    let to_string () =
      List.map exs ~f:(fun ctx ->
          sprintf "%s" (SD.Map.to_string Value.to_string ctx))
      |> String.concat ~sep:"\n"
    in
    let data = Inputs exs in

    { S.verify; S.compare; S.to_sexp; S.to_string; S.data }
end

module Specification = struct
  include Specification0

  let increment_scope : t -> t = fun sp -> match sp.data with
    | Examples.Examples exs ->
      let exs =
        List.map exs ~f:(fun (in_ctx, out) ->
            let in_ctx =
              StaticDistance.Map.to_alist in_ctx
              |> List.map ~f:(fun (k, v) -> (StaticDistance.increment_scope k, v))
              |> StaticDistance.Map.of_alist_exn
            in
            (in_ctx, out))
      in
      Examples.to_spec exs
    | FunctionExamples.FunctionExamples exs ->
      let exs =
        List.map exs ~f:(fun ((in_ctx, in_args), out) ->
            let in_ctx =
              StaticDistance.Map.to_alist in_ctx
              |> List.map ~f:(fun (k, v) -> (StaticDistance.increment_scope k, v))
              |> StaticDistance.Map.of_alist_exn
            in
            ((in_ctx, in_args), out))
      in
      FunctionExamples.to_spec exs
    | _ -> sp

  include Comparable.Make(T)
end

module Hypothesis = struct
  module Sk = Skeleton
  module Sp = Specification
    
  type kind =
    | Abstract
    | Concrete
    [@@deriving sexp]

  type t = {
    skeleton : Sk.t;
    cost : int;
    kind : kind;
    holes : (Hole.t * Sp.t) list;
  } [@@deriving fields]

  let spec h = Sk.spec h.skeleton

  let sexp_of_t h =
    let open Sexp in
    List [
      List [ Atom "skeleton"; [%sexp_of:Sk.t] (skeleton h) ];
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
        skeleton = [%of_sexp:Sk.t] skel_s;
        cost = Int.t_of_sexp cost_s;
        kind = kind_of_sexp kind_s;
        holes = [%of_sexp:(Hole.t * Sp.t) list] holes_s;
      }
    | _ -> raise (Sexp.Of_sexp_error (Failure "Sexp has the wrong format.", s))

  let compare_skeleton h1 h2 = Sk.compare h1.skeleton h2.skeleton
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
      skeleton = skeleton h |> Sk.map_hole ~f:(Hole.apply_unifier u)
    }

  let fill_hole cm hole ~parent:p ~child:c = begin
    if not (List.exists p.holes ~f:(fun (h, _) -> Hole.equal_id h hole)) then
      failwith "Hypothesis does not contain the specified hole.";
    let holes =
      (List.filter p.holes ~f:(fun (h, _) -> not (Hole.equal_id h hole))) @ c.holes
    in
    {
      skeleton = Sk.fill_hole hole ~parent:(skeleton p) ~child:(skeleton c);
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
      skeleton = s;
      kind = if List.length holes = 0 then Concrete else Abstract;
      cost = CostModel.cost_of_skeleton cm s;
      holes;
    }

  module C = CostModel
  
  let num cm x s : t = {
    skeleton = Sk.num x s;
    cost = cm.C.num x;
    kind = Concrete;
    holes = [];
  }
  let bool cm x s : t = {
    skeleton = Sk.bool x s;
    cost = cm.C.bool x;
    kind = Concrete;
    holes = [];
  }
  let id_sd cm x s : t =
    let id = Sk.Id.StaticDistance x in
    {
      skeleton = Sk.id id s;
      cost = cm.C.id id;
      kind = Concrete;
      holes = [];
    }
  let hole cm x s : t = {
    skeleton = Sk.hole x s;
    cost = cm.C.hole x;
    kind = Abstract;
    holes = [ (x, s) ];
  }
  let list cm (x: t list) s : t =
    let skel_x = List.map x ~f:skeleton in
    {
      skeleton = Sk.list skel_x s;
      cost = cm.C.list skel_x + List.int_sum (List.map x ~f:cost);
      kind = if List.exists x ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat_map x ~f:holes;
    }
  let tree cm x s : t =
    let flat = Tree.flatten x in
    let skel_tree = Tree.map x ~f:skeleton in
    {
      skeleton = Sk.tree skel_tree s;
      cost = cm.C.tree skel_tree + List.int_sum (List.map flat ~f:cost);
      kind = if List.exists flat ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat_map flat ~f:holes;
    }
  let _let cm bound body s : t =
    let sk_bound, sk_body = skeleton bound, skeleton body in
    {
      skeleton = Sk.let_ sk_bound sk_body s;
      cost = cm.C._let sk_bound sk_body + bound.cost + body.cost;
      kind = if bound.kind = Abstract || body.kind = Abstract then Abstract else Concrete;
      holes = bound.holes @ body.holes;
    }
  let lambda cm num_args body s : t =
    let sk_body = skeleton body in
    {
      skeleton = Sk.lambda num_args sk_body s;
      cost = cm.C.lambda num_args sk_body + body.cost;
      kind = if body.kind = Abstract then Abstract else Concrete;
      holes = body.holes;
    }
  let apply cm func args s : t =
    let sk_func, sk_args = skeleton func, List.map args ~f:skeleton in
    {
      skeleton = Sk.apply sk_func sk_args s;
      cost = cm.C.apply sk_func sk_args + cost func + List.int_sum (List.map args ~f:cost);
      kind =
        if func.kind = Abstract || List.exists args ~f:(fun h -> h.kind = Abstract) then
          Abstract else Concrete;
      holes = func.holes @ (List.concat_map args ~f:holes);
    }
  let id_name cm x s : t = {
    skeleton = Sk.id (Sk.Id.Name x) s;
    cost = cm.C.id (Sk.Id.Name x);
    kind = Concrete;
    holes = [];
  }
  let op cm op args s : t =
    let sk_args = List.map args ~f:skeleton in
    {
      skeleton = Sk.op op sk_args s;
      cost = cm.C.op op sk_args + List.int_sum (List.map args ~f:cost);
      kind = if List.exists args ~f:(fun h -> h.kind = Abstract) then Abstract else Concrete;
      holes = List.concat_map args ~f:holes;
    }
end
