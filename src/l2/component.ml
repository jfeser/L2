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
  with sexp, compare

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
        error "Values are not well sorted." vs <:sexp_of<Ast.value list>>
  
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
    with sexp, compare
  end

  include T
  include Comparable.Make(T)

  let to_z3 zctx sort = function
    | Free x -> Z3.Expr.mk_const_s zctx x sort
    | Input x -> Z3.Expr.mk_const_s zctx ("i" ^ (Int.to_string x)) sort
    | Output -> Z3.Expr.mk_const_s zctx "r" sort
end

module Constant = struct
  type t = Component0.constant =
    | Bool of bool
    | Int of int
    | Nil
    | Bottom
  with sexp, compare
  
  let to_z3 zctx c =
    let err c = error "Unexpected constant in constraint." c sexp_of_t in
    match c with
    | Bool true -> Ok (Z3.Boolean.mk_true zctx)
    | Bool false -> Ok (Z3.Boolean.mk_false zctx)
    | Int x -> Ok (Z3.Arithmetic.Integer.mk_numeral_i zctx x)
    | Nil -> err Nil
    | Bottom -> err Bottom
end

module Term = struct
  module T = struct
    type t = Component0.term =
        | Constant of Constant.t
        | Variable of Variable.t
        | Apply of string * t list
    with sexp, compare
  end

  include T
  include Comparable.Make(T)

  module V = Variable
  module C = Constant
  open Or_error.Monad_infix
  
  let rec evaluate ctx = function
    | Constant x -> Ok (Constant x)
    | Variable v -> begin match V.Map.find ctx v with
        | Some x -> Ok x
        | None -> error "Unbound variable." (v, ctx) <:sexp_of<V.t * t V.Map.t>>
      end
    | Apply (f, args) as apply ->
      let args = List.map args ~f:(evaluate ctx) in
      Or_error.all args >>= fun args -> begin match f, args with
        | "Len", [x] -> 
          let rec len = function
            | Constant C.Nil -> Ok 0
            | Apply ("Cons", [_; xs]) -> len xs >>| fun len_xs -> 1 + len_xs
            | c -> error "Cannot take length of non-list." c sexp_of_t
          in
          len x >>| fun len_x -> Constant (C.Int len_x)
        | _ -> error "Unknown function." apply sexp_of_t
      end

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

  let rec to_list = function
    | Apply ("Cons", [x; xs]) -> to_list xs >>| fun xs -> x::xs
    | Constant C.Nil -> Ok []
    | c -> error "Not a list." c sexp_of_t

  let rec of_value = function
    | `Num x -> Constant (C.Int x)
    | `Bool x -> Constant (C.Bool x)
    | `List x ->
      List.map x ~f:of_value
      |> List.fold_right ~init:(Constant C.Nil) ~f:(fun e a -> Apply ("Cons", [e; a]))
    | v -> failwiths "Unsupported value." v <:sexp_of<Ast.value>>

  let rec to_z3 sorts zctx t =
    let z3_app = Z3.FuncDecl.apply in

    Or_error.try_with_join (fun () ->
        match t with
        | Constant c -> C.to_z3 zctx c
        | Variable var ->
          begin match V.Map.find sorts var with
            | Some sort ->
              let z3_sort = Sort.to_z3 zctx sort in
              Ok (V.to_z3 zctx z3_sort var)
            | None -> error "No sort available for variable." (var, sorts)
                        <:sexp_of<V.t * Sort.t V.Map.t>>
          end
        | Apply ("Len", [x]) -> to_z3 sorts zctx x >>| fun x -> z3_app (Z3_Defs.Functions.len zctx) [x]
        | Apply ("Sub", [x1; x2]) ->
          to_z3 sorts zctx x1 >>= fun x1 -> 
          to_z3 sorts zctx x2 >>| fun x2 -> 
          Z3.Arithmetic.mk_sub zctx [x1; x2]
        | Apply ("Plus", [x1; x2]) ->
          to_z3 sorts zctx x1 >>= fun x1 -> 
          to_z3 sorts zctx x2 >>| fun x2 -> 
          Z3.Arithmetic.mk_add zctx [x1; x2]
        | t -> error "Unsupported term." t sexp_of_t)
end

module Predicate = struct
  type operator = Component0.binary_operator =
    | Eq
    | Neq
    | Gt
    | Lt
    | Ge
    | Le
    | Superset
    | Subset
    | NotSuperset
    | NotSubset
  with sexp, compare

  type t = Component0.predicate =
    | Binary of operator * Term.t * Term.t
  with sexp, compare

  open Component0
  open Or_error.Monad_infix

  let of_string s =
    let lexbuf = Lexing.from_string s in
    try Ok (Component_parser.predicate_eof Component_lexer.token lexbuf) with
    | Component_parser.Error -> error "Failed to parse." s String.sexp_of_t
    | Component_lexer.SyntaxError err ->
      error "Failed to parse." (s, err) <:sexp_of<string * string>>
    | Parsing.Parse_error -> error "Failed to parse." s String.sexp_of_t

  let substitute m = function
    | Binary (p, x1, x2) -> Binary (p, Term.substitute m x1, Term.substitute m x2)

  let substitute_var m = function
    | Binary (p, x1, x2) ->
      Binary (p, Term.substitute_var m x1, Term.substitute_var m x2)

  let evaluate ctx p =
    let teval = Term.evaluate ctx in
    let int_int_pred pred x1 x2 =
      match x1, x2 with
      | Constant (Int x1), Constant (Int x2) -> Ok (pred x1 x2)
      | c1, c2 -> error "Expected an integer." (c1, c2) <:sexp_of<Term.t * Term.t>>
    in
    let set_set_pred pred x1 x2 =
      Term.to_list x1 >>= fun l1 -> Term.to_list x2 >>| fun l2 ->
      pred (Term.Set.of_list l1) (Term.Set.of_list l2)
    in
    let eval = function
      | Binary (f, x1, x2) ->
        teval x1 >>= fun x1 -> teval x2 >>= fun x2 -> begin match f with
          | Eq -> Ok (x1 = x2)
          | Neq -> Ok (x1 <> x2)
          | Gt -> int_int_pred (>) x1 x2
          | Lt -> int_int_pred (<) x1 x2
          | Ge -> int_int_pred (>=) x1 x2
          | Le -> int_int_pred (<=) x1 x2
          | Superset -> set_set_pred (fun s1 s2 -> Term.Set.subset s2 s1) x1 x2
          | Subset -> set_set_pred Term.Set.subset x1 x2
          | NotSuperset -> set_set_pred (fun s1 s2 -> not (Term.Set.subset s2 s1)) x1 x2
          | NotSubset -> set_set_pred (fun s1 s2 -> not (Term.Set.subset s1 s2)) x1 x2
        end
    in
    eval p >>| fun r -> Constant (Bool (r))

  let to_z3 sorts zctx p =
    let z3_app = Z3.FuncDecl.apply in
    let z3_not = Z3.Boolean.mk_not in
    let m_z3 = match p with
      | Binary (pred, x1, x2) ->
        Term.to_z3 sorts zctx x1 >>= fun x1 -> 
        Term.to_z3 sorts zctx x2 >>= fun x2 ->
        let m_z3 = Or_error.try_with (fun () -> match pred with
            | Eq -> Z3.Boolean.mk_eq zctx x1 x2
            | Neq -> Z3.Boolean.mk_not zctx (Z3.Boolean.mk_eq zctx x1 x2)
            | Gt -> Z3.Arithmetic.mk_gt zctx x1 x2
            | Lt -> Z3.Arithmetic.mk_lt zctx x1 x2
            | Ge -> Z3.Arithmetic.mk_ge zctx x1 x2
            | Le -> Z3.Arithmetic.mk_le zctx x1 x2
            | Superset -> z3_app (Z3_Defs.Functions.superset zctx) [x1; x2]
            | Subset -> z3_app (Z3_Defs.Functions.subset zctx) [x1; x2]
            | NotSuperset -> z3_not zctx (z3_app (Z3_Defs.Functions.superset zctx) [x1; x2])
            | NotSubset -> z3_not zctx (z3_app (Z3_Defs.Functions.subset zctx) [x1; x2]))
        in
        Or_error.tag_arg m_z3 "Binary predicate arguments"
          ((x1, Z3.Expr.get_sort x1), (x2, Z3.Expr.get_sort x2))
          (Tuple.T2.sexp_of_t
             (Tuple.T2.sexp_of_t sexp_of_z3_expr sexp_of_z3_sort)
             (Tuple.T2.sexp_of_t sexp_of_z3_expr sexp_of_z3_sort))
    in
    Or_error.tag_arg m_z3 "Predicate.to_z3 inputs" (p, sorts)
      <:sexp_of<t * Sort.t Variable.Map.t>>
end  

module Specification = struct
  type t = {
    constraints : Predicate.t list;
    sorts : Sort.t Variable.Map.t;
  } with sexp, compare

  open Or_error.Monad_infix

  module T = Term
  module V = Variable
  module C = Constant
  module S = Sort
  module P = Predicate

  let one_arg_predicates = [
    "Len(i1) = 0";
    "Len(i1) != 0";
    "Len(i1) > 0";
    "Len(i1) < 0";
    "Len(i1) >= 0";
    "Len(i1) <= 0";
    "i1 = 0";
    "i1 != 0";
    "i1 > 0";
    "i1 < 0";
    "i1 >= 0";
    "i1 <= 0";
  ] |> List.map ~f:(fun s -> P.of_string s |> Or_error.ok_exn)
  
  let two_arg_predicates = [
    "Len(i1) = Len(r)";
    "Len(i1) != Len(r)";
    "Len(i1) > Len(r)";
    "Len(i1) < Len(r)";
    "Len(i1) >= Len(r)";
    "Len(i1) <= Len(r)";
    "i1 ⊄ r";
    "i1 ⊅ r";
  ] |> List.map ~f:(fun s -> P.of_string s |> Or_error.ok_exn)

  let equal s1 s2 = compare s1 s2 = 0

  let of_string s =
    let lexbuf = Lexing.from_string s in
    let parsed =
      try Ok (Component_parser.specification_eof Component_lexer.token lexbuf) with
      | Component_parser.Error -> error "Failed to parse." s String.sexp_of_t
      | Component_lexer.SyntaxError err ->
        error "Failed to parse." (s, err) <:sexp_of<string * string>>
      | Parsing.Parse_error -> error "Failed to parse." s String.sexp_of_t
    in
    parsed >>= fun (constraints, sorts_list) ->
    let sorts = List.fold sorts_list ~init:(Ok V.Map.empty) ~f:(fun map (var, sort) ->
        map >>= fun map ->
        if V.Map.find map var |> Option.is_some then
          error "Multiple bindings for variable." var V.sexp_of_t
        else
          Ok (V.Map.add map ~key:var ~data:sort))
    in
    sorts >>| fun sorts -> { constraints; sorts }
  
  let top = { constraints = []; sorts = V.Map.empty }
  
  let of_examples ?(predicates = two_arg_predicates) exs =
    let module H = Hypothesis in
    let module Sp = H.Specification in
    let module SD = H.StaticDistance in
    (* Create a mapping from names in the example context to the set
       of values that the name takes. *)
    let values_by_name =
      List.fold (Sp.Examples.to_list exs) ~init:SD.Map.empty ~f:(fun vals (in_ctx, out) ->
        SD.Map.merge in_ctx vals ~f:(fun ~key:_ x -> match x with
            | `Both (v, vs) -> Some ((v, out)::vs)
            | `Left v -> Some [(v, out)]
            | `Right vs -> Some vs))
    in

    (* Use predicates to summarize the values for each name *)
    Or_error.try_with (fun () ->
        SD.Map.map values_by_name ~f:(fun values ->
            let constraints =
              List.fold values ~init:predicates ~f:(fun preds (inp, out) ->
                  let ctx =
                    V.Map.of_alist_exn [V.Input 1, T.of_value inp; V.Output, T.of_value out]
                  in
                  List.filter preds ~f:(fun p -> match P.evaluate ctx p with
                      | Ok (T.Constant (C.Bool true)) -> true
                      | Ok _ | Error _ -> false))
            in

            let inputs, outputs = List.unzip values in
            let input_sort = Sort.of_values inputs |> ok_exn in
            let output_sort = Sort.of_values outputs |> ok_exn in
            { constraints;
              sorts = V.Map.of_alist_exn [V.Input 1, input_sort; V.Output, output_sort]
            }))

  let to_z3 zctx s =
    List.map s.constraints ~f:(P.to_z3 s.sorts zctx)
    |> Or_error.all

  let substitute_var m s = {
    constraints = List.map s.constraints ~f:(P.substitute_var m);
    sorts = V.Map.to_alist s.sorts
            |> List.map ~f:(fun (v, s) -> Option.value (V.Map.find m v) ~default:v, s)
            |> V.Map.of_alist_exn;
  }
end

type t = {
  name : string;
  spec : Specification.t;
  type_ : Type.t;
} with sexp

let create name spec type_ =
  let open Or_error.Monad_infix in
  Specification.of_string spec >>| fun spec ->
  { name; spec; type_ = Type.of_string type_; }

let stdlib = [
  create "drop"
    "i2 >= 0 ^ Len(i1) >= i2 ^ Sub(Len(i1), i2) = Len(r) ^ i1 ⊃ r \
     where i1: list, i2: int, r: list"
    "(list[a], int) -> list[a]";

  create "take"
    "i2 >= 0 ^ Len(i1) >= i2 ^ i2 = Len(r) ^ i1 ⊃ r where i1: list, i2: int, r: list"
    "(list[a], int) -> list[a]";

  create "merge"
    "r ⊃ i1 ^ r ⊃ i2 ^ Len(r) = Plus(Len(i1), Len(i2)) where i1: list, i2: list, r: list"
    "(list[num], list[num]) -> list[num]";

  create "zip"
    "Len(i1) = Len(i2) ^ Len(r) = Len(i1) where i1: list, i2: list, r: list"
    "(list[a], list[a]) -> list[list[a]]";

  create "car"
    "Len(i1) > 0 where i1: list"
    "(list[a]) -> a";

  Ok {
    name = "concat";
    spec = {
      Specification.constraints = [];
      Specification.sorts = Variable.Map.of_alist_exn [Variable.Output, Sort.List];
    };
    type_ = "(list[list[a]]) -> list[a]" |> Type.of_string
  };

  create "cons"
    "Plus(Len(i2), 1) = Len(r) ^ i2 ⊂ r where i2: list, r: list"
    "(a, list[a]) -> list[a]";

  create "rcons"
    "Plus(Len(i1), 1) = Len(r) ^ i1 ⊂ r where i1: list, r: list"
    "(list[a], a) -> list[a]";

  create "cdr"
    "Len(i1) > 0 ^ Sub(Len(i1), 1) = Len(r) ^ i1 ⊃ r where i1: list, r: list"
    "(list[a]) -> list[a]";

  create "intersperse"
    "Len(i1) <= Len(r) where i1: list, r: list"
    "(list[a], a) -> list[a]";

  create "reverse"
    "Len(i1) = Len(r) ^ i1 ⊂ r ^ i1 ⊃ r where i1: list, r: list"
    "(list[a]) -> list[a]";

  create "sort"
    "Len(i1) = Len(r) ^ i1 ⊂ r ^ i1 ⊃ r where i1: list, r: list"
    "(list[num]) -> list[num]";

  create "dedup"
    "Len(i1) >= Len(r) ^ i1 ⊃ r where i1: list, r: list"
    "(list[a]) -> list[a]";

  create "append"
    "Plus(Len(i1), Len(i2)) = Len(r) ^ i1 ⊂ r ^ i2 ⊂ r where i1: list, i2: list, r: list"
    "(list[a], list[a]) -> list[a]";
] |> List.map ~f:(fun m_c -> let c = Or_error.ok_exn m_c in c.name, c)
  |> String.Map.of_alist_exn
