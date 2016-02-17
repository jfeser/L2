open Core.Std

open Collections
open Infer

let sexp_of_z3_expr z3_expr = String.sexp_of_t (Z3.Expr.to_string z3_expr)
let sexp_of_z3_sort z3_sort = String.sexp_of_t (Z3.Sort.to_string z3_sort)

module Z3_Defs = struct
  module Symbols = struct
    let list zctx = Z3.Symbol.mk_string zctx "Lst"
    let string zctx = Z3.Symbol.mk_string zctx "Str"
    let len zctx = Z3.Symbol.mk_string zctx "Len"
    let subset zctx = Z3.Symbol.mk_string zctx "Subset"
    let superset zctx = Z3.Symbol.mk_string zctx "Superset"
  end
  
  module Sorts = struct
    let int = Z3.Arithmetic.Integer.mk_sort
    let bool = Z3.Boolean.mk_sort
    let list zctx = Z3.Sort.mk_uninterpreted zctx (Symbols.list zctx)
    let string zctx = Z3.Sort.mk_uninterpreted zctx (Symbols.string zctx)

    let mapping zctx = [
      Symbols.list zctx, list zctx;
      Symbols.string zctx, string zctx;
    ]
  end
  
  module Functions = struct
    let len zctx = Z3.FuncDecl.mk_func_decl zctx (Symbols.len zctx) [Sorts.list zctx] (Sorts.int zctx)
    let subset zctx = Z3.FuncDecl.mk_func_decl zctx (Symbols.subset zctx)
        [Sorts.list zctx; Sorts.list zctx] (Sorts.bool zctx)
    let superset zctx = Z3.FuncDecl.mk_func_decl zctx (Symbols.superset zctx)
        [Sorts.list zctx; Sorts.list zctx] (Sorts.bool zctx)

    let mapping zctx = [
      Symbols.len zctx, len zctx;
      Symbols.subset zctx, subset zctx;
      Symbols.superset zctx, superset zctx;
    ]
  end
end

module Sort = struct
  type t = Component0.sort =
    | Int
    | Bool
    | List
    | String
  [@@deriving sexp, compare]

  open Or_error.Monad_infix

  module T = Type

  let equal s1 s2 = compare s1 s2 = 0
    
  let of_type = function
    | T.Const_t Ast.Num_t -> Ok Int
    | T.Const_t Ast.Bool_t -> Ok Bool
    | T.App_t ("list", _) -> Ok List
    | t -> error "Unsupported type." t Type.sexp_of_t
  
  let of_value = function
    | `Num _ -> Ok Int
    | `Bool _ -> Ok Bool
    | `List _ -> Ok List
    | v -> error "Unsupported value." v Ast.sexp_of_value

  let of_values = function
    | [] -> Or_error.error_string "The empty list is not well sorted."
    | vs -> List.map vs ~f:of_value |> Or_error.all >>= fun sorts -> 
      if List.all_equal sorts then Ok (List.hd_exn sorts) else
        error "Values are not well sorted." vs [%sexp_of:Ast.value list]
  
  let to_z3 zctx = function
    | Int -> Z3_Defs.Sorts.int zctx
    | Bool -> Z3_Defs.Sorts.bool zctx
    | List -> Z3_Defs.Sorts.list zctx
    | String -> Z3_Defs.Sorts.list zctx
end

module Variable = struct
  module T = struct
    type t = Component0.variable =
      | Free of string
      | Input of int
      | Output
      [@@deriving sexp, compare]
  end

  include T
  include Comparable.Make(T)

  let to_z3 zctx sort v =
    let err = Or_error.try_with (fun () -> match v with
      | Free x -> Z3.Expr.mk_const_s zctx x sort
      | Input x -> Z3.Expr.mk_const_s zctx ("i" ^ (Int.to_string x)) sort
      | Output -> Z3.Expr.mk_const_s zctx "r" sort)
    in
    Or_error.tag_arg err "Variable.to_z3" v [%sexp_of:t]
end

module Constant = struct
  module T = struct
    type t = Component0.constant =
      | Bool of bool
      | Int of int
      | Variant of string * t list
      [@@deriving sexp, compare]
  end

  include T

  let rec of_value = function
    | `Num x -> Int x
    | `Bool x -> Bool x
    | `List x ->
      List.map x ~f:of_value
      |> List.fold_right ~init:(Variant ("Nil", [])) ~f:(fun e a -> Variant ("Cons", [e; a]))
    | v -> failwiths "Unsupported value." v [%sexp_of:Ast.value]

  let rec to_list_exn = function
    | Variant ("Nil", []) -> []
    | Variant ("Cons", [x; xs]) -> x::(to_list_exn xs)
    | c -> failwiths "Expected Nil or Cons." c [%sexp_of:t]

  let to_list c = Or_error.try_with (fun () -> to_list_exn c)

  let rec of_list = function
    | [] -> Variant ("Nil", [])
    | x::xs -> Variant ("Cons", [x; of_list xs])
  
  let to_z3 zctx c =
    let err c = error "Unexpected constant in constraint." c sexp_of_t in
    match c with
    | Bool true -> Ok (Z3.Boolean.mk_true zctx)
    | Bool false -> Ok (Z3.Boolean.mk_false zctx)
    | Int x -> Ok (Z3.Arithmetic.Integer.mk_numeral_i zctx x)
    | Variant _ -> err c

  include Comparable.Make(T)
end

module Term = struct
  module T = struct
    type t = Component0.term =
      | Constant of Constant.t
      | Variable of Variable.t
      | Apply of string * t list
      [@@deriving sexp, compare]

    let equal t1 t2 = compare t1 t2 = 0
  end

  include T

  module V = Variable
  module C = Constant
  open Or_error.Monad_infix
  
  let rec evaluate ctx term =
    match term with
    | Constant x -> Ok (Constant x)
                      
    | Variable v -> begin match V.Map.find ctx v with
        | Some x -> Ok x
        | None -> error "Unbound variable." (v, ctx) [%sexp_of:V.t * t V.Map.t]
      end
      
    | Apply (f, args) as apply ->
      let args = List.map args ~f:(evaluate ctx) in
      Or_error.all args >>= fun args -> begin
        let int_int_bool t1 op t2 = match t1, t2 with
          | Constant (C.Int x1), Constant (C.Int x2) -> Ok (Constant (C.Bool (op x1 x2)))
          | _ -> error "Unexpected arguments." (f, args) [%sexp_of:string * t list]
        in

        let list_list_bool t1 op t2 = match t1, t2 with
          | Constant x1, Constant x2 ->
            C.to_list x1 >>= fun x1_l ->
            C.to_list x2 >>| fun x2_l ->
            Constant (C.Bool (op x1_l x2_l))
          | _ -> error "Unexpected arguments." (f, args) [%sexp_of:string * t list]
        in

        match f, args with
        | "Len", [x] -> begin match x with
            | Constant xc -> C.to_list xc >>| fun x_list -> Constant (C.Int (List.length x_list))
            | _ -> failwith "Unexpected argument."
          end
        | "Superset", [t1; t2] ->
          let superset l1 l2 = C.Set.subset (C.Set.of_list l2) (C.Set.of_list l1) in
          list_list_bool t1 superset t2
        | "Subset", [t1; t2] ->
          let subset l1 l2 = C.Set.subset (C.Set.of_list l1) (C.Set.of_list l2) in
          list_list_bool t1 subset t2
        | "Eq", [x1; x2] -> Ok (Constant (C.Bool (x1 = x2)))
        | "Neq", [x1; x2] -> Ok (Constant (C.Bool (x1 <> x2)))
        | "Gt", [t1; t2] -> int_int_bool t1 (>) t2
        | "Lt", [t1; t2] -> int_int_bool t1 (<) t2
        | "Ge", [t1; t2] -> int_int_bool t1 (>=) t2
        | "Le", [t1; t2] -> int_int_bool t1 (<=) t2

        | _ -> error "Unknown function." apply sexp_of_t
      end

  include Comparable.Make(T)
  
  let rec simplify term =
    match term with
    | Apply (f, args) -> begin
        let args = List.map args ~f:simplify in
        match f, args with
        | "And", clauses ->
          let clause_set = Set.of_list clauses in

          (* Eliminate all true clauses. *)
          let clause_set = Set.remove clause_set (Constant (C.Bool true)) in

          (* Check for contradiction (using syntactic equality). *)
          let is_contra =
            Set.exists clause_set ~f:(fun c -> Set.mem clause_set (Apply ("Not", [c])))
          in
          if is_contra then Constant (C.Bool false) else
            begin match Set.to_list clause_set with
              | [] -> Constant (C.Bool true)
              | [x] -> x
              | xs -> Apply ("And", xs)
            end
        | _ -> term
      end
    | _ -> term      

  let rec substitute m = function
    | (Constant _ as t)
    | (Variable _ as t) ->
      begin match Map.find m t with
        | Some t' -> t'
        | None -> t
      end
    | Apply (func, args) as t ->
      begin match Map.find m t with
        | Some t' -> t'
        | None -> 
          let args = List.map args ~f:(substitute m) in
          Apply (func, args)
      end

  let rec substitute_var m = function
    | (Constant _ as t) -> t
    | (Variable v as t) -> 
      begin match V.Map.find m v with
        | Some v' -> Variable v'
        | None -> t
      end
    | Apply (func, args) ->
      let args = List.map args ~f:(substitute_var m) in
      Apply (func, args)

  let rec of_value x = Constant (C.of_value x)

  let abstract : (V.t * t) list -> t list = fun terms ->
    let predicates = [
      "Len", 1;
      "Superset", 2;
      "Subset", 2;
    ] in
    let (list_terms, other_terms) =
      List.partition_tf terms ~f:(fun (_, t) -> match t with
          | Constant (C.Variant ("Nil", _)) | Constant (C.Variant ("Cons", _)) -> true
          | _ -> false)
    in
    let abstract_list_terms =
      List.concat_map predicates ~f:(fun (name, arity) -> 
          Util.permutations_k list_terms arity
          |> List.filter_map ~f:(fun args ->
              let args_vars, args_values = List.unzip args in
              match evaluate V.Map.empty (Apply (name, args_values)) with
              | Ok (Constant _ as ret) ->
                let args_names = List.map args_vars ~f:(fun v -> Variable v) in
                Some (Apply ("Eq", [Apply (name, args_names); ret]))
              | Ok c -> failwiths "BUG: Got a non-constant value from predicate." c [%sexp_of:t]
              | Error err -> print_endline (Error.to_string_hum err); None))
    in
    let abstract_other_terms =
      List.map other_terms ~f:(fun (v, t) -> Apply ("Eq", [Variable v; t]))
    in
    abstract_other_terms @ abstract_list_terms

  let rec to_z3 sorts zctx t =
    let z3_app = Z3.FuncDecl.apply in

    let err = Or_error.try_with_join (fun () ->
        match t with
        | Constant c -> C.to_z3 zctx c
        | Variable var ->
          begin match V.Map.find sorts var with
            | Some sort ->
              let z3_sort = Sort.to_z3 zctx sort in
              V.to_z3 zctx z3_sort var
            | None -> error "No sort available for variable." (var, sorts)
                        [%sexp_of:V.t * Sort.t V.Map.t]
          end
        | Apply (func, args) ->
          List.map args ~f:(to_z3 sorts zctx) |> Or_error.all >>= fun z3_args ->
          begin match func, z3_args with
            | "Not", [x] -> Ok (Z3.Boolean.mk_not zctx x)
            | "And", xs -> Ok (Z3.Boolean.mk_and zctx xs)
            | "Or", xs -> Ok (Z3.Boolean.mk_or zctx xs)
            | "Len", [x] -> Ok (z3_app (Z3_Defs.Functions.len zctx) [x])
            | "Superset", [x1; x2] -> Ok (z3_app (Z3_Defs.Functions.superset zctx) [x1; x2])
            | "Subset", [x1; x2] -> Ok (z3_app (Z3_Defs.Functions.subset zctx) [x1; x2])
            | "Sub", [x1; x2] -> Ok (Z3.Arithmetic.mk_sub zctx [x1; x2])
            | "Add", [x1; x2] -> Ok (Z3.Arithmetic.mk_add zctx [x1; x2])
            | "Eq", [x1; x2] ->
              let s1 = Z3.Expr.get_sort x1 in
              let s2 = Z3.Expr.get_sort x2 in
              if Z3.Sort.equal s1 s2 then
                Ok (Z3.Boolean.mk_eq zctx x1 x2)
              else
                error "Sorts are not equal."
                  (Z3.Sort.to_string s1, Z3.Sort.to_string s2) [%sexp_of:string * string]
            | "Gt", [x1; x2] -> Ok (Z3.Arithmetic.mk_gt zctx x1 x2)
            | "Ge", [x1; x2] -> Ok (Z3.Arithmetic.mk_ge zctx x1 x2)
            | "Lt", [x1; x2] -> Ok (Z3.Arithmetic.mk_lt zctx x1 x2)
            | "Le", [x1; x2] -> Ok (Z3.Arithmetic.mk_le zctx x1 x2)
            | _ -> error "Unexpected function or arguments." (func, args) [%sexp_of:string * t list]
          end)
    in
    Or_error.tag_arg err "Term.to_z3" t [%sexp_of:t]
end

  (* let to_z3 sorts zctx p = *)
  (*   let z3_app = Z3.FuncDecl.apply in *)
  (*   let z3_not = Z3.Boolean.mk_not in *)
  (*   let m_z3 = match p with *)
  (*     | Binary (pred, x1, x2) -> *)
  (*       Term.to_z3 sorts zctx x1 >>= fun x1 -> *)
  (*       Term.to_z3 sorts zctx x2 >>= fun x2 -> *)
  (*       let m_z3 = Or_error.try_with (fun () -> match pred with *)
  (*           | Eq -> Z3.Boolean.mk_eq zctx x1 x2 *)
  (*           | Neq -> Z3.Boolean.mk_not zctx (Z3.Boolean.mk_eq zctx x1 x2) *)
  (*           | Gt -> Z3.Arithmetic.mk_gt zctx x1 x2 *)
  (*           | Lt -> Z3.Arithmetic.mk_lt zctx x1 x2 *)
  (*           | Ge -> Z3.Arithmetic.mk_ge zctx x1 x2 *)
  (*           | Le -> Z3.Arithmetic.mk_le zctx x1 x2 *)
  (*           | Superset -> z3_app (Z3_Defs.Functions.superset zctx) [x1; x2] *)
  (*           | Subset -> z3_app (Z3_Defs.Functions.subset zctx) [x1; x2] *)
  (*           | NotSuperset -> z3_not zctx (z3_app (Z3_Defs.Functions.superset zctx) [x1; x2]) *)
  (*           | NotSubset -> z3_not zctx (z3_app (Z3_Defs.Functions.subset zctx) [x1; x2])) *)
  (*       in *)
  (*       Or_error.tag_arg m_z3 "Binary predicate arguments" *)
  (*         ((x1, Z3.Expr.get_sort x1), (x2, Z3.Expr.get_sort x2)) *)
  (*         (Tuple.T2.sexp_of_t *)
  (*            (Tuple.T2.sexp_of_t sexp_of_z3_expr sexp_of_z3_sort) *)
  (*            (Tuple.T2.sexp_of_t sexp_of_z3_expr sexp_of_z3_sort)) *)
  (*   in *)
  (*   Or_error.tag_arg m_z3 "Predicate.to_z3 inputs" (p, sorts) *)
  (*     <:sexp_of<t * Sort.t Variable.Map.t>> *)

module Specification = struct
  module T = struct
    type t = {
      _constraint : Term.t;
      sorts : Sort.t Variable.Map.t;
    } [@@deriving sexp, compare]
  end

  include T

  open Or_error.Monad_infix

  module Te = Term
  module V = Variable
  module C = Constant
  module S = Sort

  (* let one_arg_predicates = [ *)
  (*   "Len(i1) = 0"; *)
  (*   "Len(i1) != 0"; *)
  (*   "Len(i1) > 0"; *)
  (*   "Len(i1) < 0"; *)
  (*   "Len(i1) >= 0"; *)
  (*   "Len(i1) <= 0"; *)
  (*   "i1 = 0"; *)
  (*   "i1 != 0"; *)
  (*   "i1 > 0"; *)
  (*   "i1 < 0"; *)
  (*   "i1 >= 0"; *)
  (*   "i1 <= 0"; *)
  (* ] |> List.map ~f:(fun s -> P.of_string s |> Or_error.ok_exn) *)
  
  (* let two_arg_predicates = [ *)
  (*   "Len(i1) = Len(r)"; *)
  (*   "Len(i1) != Len(r)"; *)
  (*   "Len(i1) > Len(r)"; *)
  (*   "Len(i1) < Len(r)"; *)
  (*   "Len(i1) >= Len(r)"; *)
  (*   "Len(i1) <= Len(r)"; *)
  (*   "i1 ⊄ r"; *)
  (*   "i1 ⊅ r"; *)
  (* ] |> List.map ~f:(fun s -> P.of_string s |> Or_error.ok_exn) *)

  let equal s1 s2 = compare s1 s2 = 0

  let of_string s =
    let lexbuf = Lexing.from_string s in
    let parsed =
      try Ok (Component_parser.specification_eof Component_lexer.token lexbuf) with
      | Component_parser.Error -> error "Failed to parse." s String.sexp_of_t
      | Component_lexer.SyntaxError err ->
        error "Failed to parse." (s, err) [%sexp_of:string * string]
      | Parsing.Parse_error -> error "Failed to parse." s String.sexp_of_t
    in
    parsed >>= fun (_constraint, sorts_list) ->
    let sorts = List.fold sorts_list ~init:(Ok V.Map.empty) ~f:(fun map (var, sort) ->
        map >>= fun map ->
        if V.Map.find map var |> Option.is_some then
          error "Multiple bindings for variable." var V.sexp_of_t
        else
          Ok (V.Map.add map ~key:var ~data:sort))
    in
    sorts >>| fun sorts -> { _constraint; sorts }

  let to_z3 zctx s =
    let z3_or_error =
      match s._constraint with
      | Te.Apply ("And", conjuncts) -> List.map conjuncts ~f:(Te.to_z3 s.sorts zctx)
      | t -> [ Te.to_z3 s.sorts zctx t ]
    in
    Or_error.all z3_or_error

  let substitute_var m s =
    let module Let_syntax = Or_error.Let_syntax in
    let _constraint = Te.substitute_var m s._constraint in

    let%map sorts =
      V.Map.to_alist s.sorts
      |> List.fold_left ~init:(Ok V.Map.empty) ~f:(fun m_sorts (var, sort) ->
          let%bind sorts = m_sorts in
          let var' = Option.value (V.Map.find m var) ~default:var in
          match V.Map.find sorts var' with
          | Some sort' ->
            if Sort.equal sort sort' then Ok sorts else
              error "Conflicting sorts after renaming." (var, var', sort, sort')
                [%sexp_of:V.t * V.t * S.t * S.t]
          | None -> Ok (V.Map.add sorts ~key:var' ~data:sort))
    in
    { _constraint; sorts; }

  let background zctx =
    let background_str =
      "(assert (forall ((x Lst)) (>= (Len x) 0))) \
       (assert (forall ((x Lst) (y Lst) (z Lst)) (=> (and (Subset x y) (Subset y z)) (Subset x z)))) \
       (assert (forall ((x Lst) (y Lst) (z Lst)) (=> (and (Superset x y) (Superset y z)) (Superset x z)))) \
       (assert (forall ((x Lst) (y Lst)) (=> (Subset x y) (Superset y x)))) \
       (assert (forall ((x Lst) (y Lst)) (=> (Superset x y) (Subset y x)))) \
       (assert (forall ((x Lst) (y Lst)) (=> (and (Subset x y) (Subset y x)) (= x y)))) \
       (assert (forall ((x Lst) (y Lst)) (=> (and (Superset x y) (Superset y x)) (= x y)))) \
       (assert (forall ((x Lst) (y Lst)) (=> (> (Len x) (Len y)) (not (Superset y x))))) \
       (assert (forall ((x Lst) (y Lst)) (=> (= (Len x) 0) (Superset y x))))"
    in
    let (sort_symbols, sorts) = List.unzip (Z3_Defs.Sorts.mapping zctx) in
    let (func_symbols, funcs) = List.unzip (Z3_Defs.Functions.mapping zctx) in
    Z3.SMT.parse_smtlib2_string zctx background_str sort_symbols sorts func_symbols funcs

  let top = {
    _constraint = Te.Constant (C.Bool true);
    sorts = V.Map.empty;
  }

  let bottom = {
    _constraint = Te.Constant (C.Bool false);
    sorts = V.Map.empty;
  }

  let clauses s = match s._constraint with
    | Te.Apply ("And", cl) -> cl
    | cl -> [cl]

  let negate s = { s with _constraint = Te.Apply ("Not", [s._constraint]) }

  let entails zctx s1 s2 =
    to_z3 zctx s1 >>= fun z1 -> 
    to_z3 zctx (negate s2) >>= fun z2 ->
    let z1_and_not_z2 = Z3.Boolean.mk_and zctx (z1 @ z2) in
    let solver = Z3.Solver.mk_simple_solver zctx in
    Z3.Solver.add solver [background zctx; z1_and_not_z2];
    match Z3.Solver.check solver [] with
    | Z3.Solver.SATISFIABLE -> Ok false
    | Z3.Solver.UNSATISFIABLE -> Ok true
    | Z3.Solver.UNKNOWN -> error "Solver returned unknown." (s1, s2) [%sexp_of:t * t]
                 
  let conjoin : t -> t -> t Or_error.t = fun s1 s2 ->
    let module Let_syntax = Or_error.Let_syntax in
    let%map merged_sorts = Or_error.try_with (fun () ->
        Variable.Map.merge s1.sorts s2.sorts ~f:(fun ~key -> function
            | `Left sort | `Right sort -> Some sort
            | `Both (sort1, sort2) ->
              if Sort.equal sort1 sort2 then Some sort1 else
                failwiths "Sorts are not compatible." (s1, s2) [%sexp_of:t * t]))
    in
    let _constraint =
      Te.Apply ("And", clauses s1 @ clauses s2)
      |> Te.simplify
    in
    { _constraint; sorts = merged_sorts }

  let is_valid : Z3.context -> t -> bool Or_error.t = fun zctx s -> entails zctx top s

  include Comparable.Make(T)
end

module T = struct
  type t = {
    name : string;
    arity : int;
    spec : Specification.t;
    type_ : Type.t;
  } [@@deriving compare, sexp]
end

include T

let create ~name ~spec ~type_ =
  let open Or_error.Monad_infix in
  Specification.of_string spec >>| fun spec ->
  let t = Type.of_string type_ in
  { name; spec; type_ = t; arity = Type.arity t; }

include Comparable.Make(T)

let stdlib = Set.of_list ([
    create "drop"
      "And(Ge(i2, 0), Ge(Len(i1), i2), Eq(Sub(Len(i1), i2), Len(r)), Superset(i1, r)) where i1: list, i2: int, r: list"
      "(list[a], num) -> list[a]";

    create "take"
      "And(Ge(i2, 0), Ge(Len(i1), i2), Eq(i2, Len(r)), Superset(i1, r)) where i1: list, i2: int, r: list"
      "(list[a], num) -> list[a]";

    create "merge"
      "And(Superset(r, i1), Superset(r, i2), Eq(Len(r), Add(Len(i1), Len(i2)))) where i1: list, i2: list, r: list"
      "(list[num], list[num]) -> list[num]";

    create "zip"
      "And(Eq(Len(i1), Len(i2)), Eq(Len(r), Len(i1))) where i1: list, i2: list, r: list"
      "(list[a], list[a]) -> list[list[a]]";

    create "car"
      "Gt(Len(i1), 0) where i1: list"
      "(list[a]) -> a";

    create ~name:"concat" ~spec:"#t where r: list" ~type_:"(list[list[a]]) -> list[a]";

    create "cons"
      "And(Eq(Add(Len(i2), 1), Len(r)), Subset(i2, r)) where i2: list, r: list"
      "(a, list[a]) -> list[a]";

    (* create "rcons" *)
    (*   "Plus(Len(i1), 1) = Len(r) ^ i1 ⊂ r where i1: list, r: list" *)
    (*   "(list[a], a) -> list[a]"; *)

    create "cdr"
      "And(Gt(Len(i1), 0), Eq(Sub(Len(i1), 1), Len(r)), Superset(i1, r)) where i1: list, r: list"
      "(list[a]) -> list[a]";

    (* create "intersperse" *)
    (*   "Len(i1) <= Len(r) where i1: list, r: list" *)
    (*   "(list[a], a) -> list[a]"; *)

    create "reverse"
      "And(Eq(Len(i1), Len(r)), Subset(i1, r), Superset(i1, r)) where i1: list, r: list"
      "(list[a]) -> list[a]";

    create "sort"
      "And(Eq(Len(i1), Len(r)), Subset(i1, r), Superset(i1, r)) where i1: list, r: list"
      "(list[num]) -> list[num]";

    (* create "dedup" *)
    (*   "Len(i1) >= Len(r) ^ i1 ⊃ r where i1: list, r: list" *)
    (*   "(list[a]) -> list[a]"; *)

    (* create "append" *)
    (*   "Plus(Len(i1), Len(i2)) = Len(r) ^ i1 ⊂ r ^ i2 ⊂ r where i1: list, i2: list, r: list" *)
    (*   "(list[a], list[a]) -> list[a]"; *)
  ] |> Or_error.all |> Or_error.ok_exn)
