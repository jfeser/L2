open Core
open Core_extended.Std
open Collections
open Hypothesis
open Infer
module Sp = Specification
module Sk = Skeleton

let timer =
  let t = Timer.empty () in
  let n = Timer.add_zero t in
  n "lookup" "Total time spent scanning abstract example lists." ;
  n "lifting" "Total time spent lifting concrete expressions." ;
  n "lowering" "Total time spent lowering abstract expressions." ;
  n "eval" "Total time spent evaluating exprs." ;
  n "infer" "Time spent inferring new examples." ;
  n "total" "Total time spent in this deduction routine." ;
  t

let run_with_time name f = Timer.run_with_time timer name f

let counter =
  let t = Counter.empty () in
  let n = Counter.add_zero t in
  n "eval_calls" "" ;
  n "eval_failure" "" ;
  n "eval_success" "" ;
  n "recursionlimit_failure" "" ;
  n "conversion_failure" "" ;
  n "no_match" "No matching example in table." ;
  n "have_examples" "Number of hypotheses where we have examples and can deduce." ;
  n "no_examples" "Number of hypotheses where we have no examples." ;
  n "abstract_specs" "Number of specs pushed to Top for being abstract." ;
  t

let cincr = Counter.incr counter

module Seq = Sequence

module Abstract_int = struct
  type value = Int of int | Omega [@@deriving compare, sexp]

  type domain = {lower: int; upper: int} [@@deriving sexp]

  let equal x y =
    match (x, y) with Int x, Int y -> `Bool (x = y) | _, Omega | Omega, _ -> `Top

  let join i1 i2 =
    match (i1, i2) with
    | Int x, Int y -> if x = y then `AbsInt (Int x) else `Top
    | Int _, Omega | Omega, Int _ -> `Top
    | Omega, Omega -> `Top

  let enumerate : domain -> value Seq.t =
   fun {lower; upper} ->
    Seq.range ~start:`inclusive ~stop:`inclusive lower upper
    |> Seq.map ~f:(fun x -> Int x)
    |> Seq.append (Seq.of_list [Omega])

  let lift0 : domain -> int -> value =
   fun {lower; upper} x -> if x < lower || x > upper then Omega else Int x

  let lift1 : domain -> (int -> int) -> value -> value =
   fun d f -> function Int x -> lift0 d (f x) | oob -> oob

  let lift2 : domain -> (int -> int -> int) -> value -> value -> value =
   fun d f -> function Int x -> lift1 d (f x) | oob -> fun _ -> oob
end

module Abstract_eq = struct
  type value = Elem of int | Omega [@@deriving compare, sexp]

  type domain = {max_distinct: int} [@@deriving sexp]

  let equal x y =
    match (x, y) with
    | Elem x, Elem y -> `Bool (x = y)
    | Elem _, Omega | Omega, Elem _ -> `Bool false
    | Omega, Omega -> `Top

  let join i1 i2 =
    match (i1, i2) with
    | Elem x, Elem y -> if x = y then `AbsEq (Elem x) else `Top
    | Elem _, Omega | Omega, Elem _ -> `Top
    | Omega, Omega -> `AbsEq Omega

  let enumerate : domain -> value Seq.t =
   fun {max_distinct} ->
    Seq.range ~start:`inclusive ~stop:`exclusive 0 max_distinct
    |> Seq.map ~f:(fun x -> Elem x)
    |> Seq.append (Seq.singleton Omega)
end

module Abstract_list = struct
  type 'a value = List of 'a list | Omega [@@deriving compare, sexp]

  type domain = {max_length: int} [@@deriving sexp]

  let rec equal ~equal:eq x y =
    match (x, y) with
    | List [], List [] -> `Bool true
    | List (x :: xs), List (y :: ys) -> (
      match eq x y with
      | `Top -> `Top
      | `Bottom -> `Bottom
      | `Bool true -> equal ~equal:eq (List xs) (List ys)
      | `Bool false -> `Bool false )
    | _, Omega | Omega, _ -> `Top
    | _ -> `Bool false

  let join ~join x y =
    match (x, y) with
    | List x, List y ->
        if List.length x = List.length y then
          `AbsList (List (List.map2_exn x y ~f:join))
        else `Top
    | List _, Omega | Omega, List _ -> `Top
    | Omega, Omega -> `AbsList Omega

  let map : f:('a -> 'b) -> 'a value -> 'b value =
   fun ~f -> function List l -> List (List.map ~f l) | Omega -> Omega

  let enumerate : 'a. domain -> 'a list -> 'a value Seq.t =
   fun {max_length} values ->
    (* Enumerate all list lengths. *)
    let x = Seq.singleton Omega in
    let xs =
      Seq.range ~start:`inclusive ~stop:`inclusive 0 max_length
      |> Seq.concat_map ~f:(fun len ->
             Combinat.combinations_with_replacement len values |> Seq.of_list )
      |> Seq.concat_map ~f:(fun values ->
             Combinat.permutations_poly (Array.of_list values) )
      |> Seq.map ~f:(fun v -> List (Array.to_list v))
    in
    Seq.append x xs

  let lift : domain -> 'a list -> 'a value =
   fun {max_length} l -> if List.length l > max_length then Omega else List l
end

module Abstract_expr = struct
  type t =
    [ `AbsInt of Abstract_int.value
    | `AbsEq of Abstract_eq.value
    | `AbsList of t Abstract_list.value
    | `Num of int
    | `Bool of bool
    | `List of t list
    | `Tree of t Tree.t
    | `Id of string
    | `Let of string * t * t
    | `Lambda of string list * t
    | `Apply of t * t list
    | `Op of Expr.Op.t * t list ]
  [@@deriving compare, sexp]

  let rec of_expr : Expr.t -> t = function
    | `Num x -> `Num x
    | `Bool x -> `Bool x
    | `Id x -> `Id x
    | `Let (x, y, z) -> `Let (x, of_expr y, of_expr z)
    | `Lambda (x, y) -> `Lambda (x, of_expr y)
    | `Apply (x, y) -> `Apply (of_expr x, List.map ~f:of_expr y)
    | `Op (x, y) -> `Op (x, List.map ~f:of_expr y)
    | `List x -> `List (List.map x ~f:of_expr)
    | `Tree x -> `Tree (Tree.map x ~f:of_expr)
end

type domain =
  {int: Abstract_int.domain; list: Abstract_list.domain; eq: Abstract_eq.domain}
[@@deriving sexp]

module Abstract_value = struct
  type t =
    [ `AbsInt of Abstract_int.value
    | `AbsEq of Abstract_eq.value
    | `AbsList of t Abstract_list.value
    | `Bool of bool
    | `List of t list
    | `Tree of t Tree.t
    | `Closure of Abstract_expr.t * t Ctx.t
    | `Bottom
    | `Top ]
  [@@deriving compare, sexp]

  exception HitRecursionLimit

  let rec list_equal ~equal:eq x y =
    match (x, y) with
    | [], [] -> `Bool true
    | x :: xs, y :: ys -> (
      match eq x y with
      | `Top -> `Top
      | `Bottom -> `Bottom
      | `Bool true -> list_equal ~equal:eq xs ys
      | `Bool false -> `Bool false )
    | _ -> `Bool false

  let rec equal x y =
    match (x, y) with
    | `AbsInt x, `AbsInt y -> Abstract_int.equal x y
    | `AbsEq x, `AbsEq y -> Abstract_eq.equal x y
    | `AbsList x, `AbsList y -> Abstract_list.equal ~equal x y
    | `AbsList (Abstract_list.List x), `List y
     |`List y, `AbsList (Abstract_list.List x) ->
        list_equal ~equal x y
    | `Bool x, `Bool y -> `Bool (x = y)
    | `List x, `List y -> `Bool (x = y)
    | `Tree x, `Tree y -> `Bool (x = y)
    | `Bottom, `Bottom -> `Bottom
    | `Top, `Top -> `Top
    | `Closure _, `Closure _ -> raise (Invalid_argument "Comparing closures.")
    | _ -> `Bool false

  let list_join ~join x y =
    if List.length x = List.length y then
      `AbsList (Abstract_list.List (List.map2_exn x y ~f:join))
    else `Top

  let rec join x y =
    match (x, y) with
    | `AbsInt x, `AbsInt y -> Abstract_int.join x y
    | `AbsEq x, `AbsEq y -> Abstract_eq.join x y
    | `AbsList x, `AbsList y -> Abstract_list.join ~join x y
    | `AbsList (Abstract_list.List x), `List y
     |`List y, `AbsList (Abstract_list.List x) ->
        list_join ~join x y
    | `Bool x, `Bool y -> if x = y then `Bool x else `Top
    | `List x, `List y -> list_join ~join x y
    | `Tree _, _ | _, `Tree _ | `Closure _, _ | _, `Closure _ ->
        failwith "Unsupported"
    | `Bottom, `Bottom -> `Bottom
    | _ -> `Top

  let rec to_string = function
    | `AbsInt (Abstract_int.Int x) -> Int.to_string x
    | `AbsEq (Abstract_eq.Elem x) -> sprintf "e%d" x
    | `AbsList (Abstract_list.List x) | `List x ->
        List.map x ~f:to_string |> String.concat ~sep:"; " |> sprintf "[%s]"
    | `AbsEq Abstract_eq.Omega
     |`AbsList Abstract_list.Omega
     |`AbsInt Abstract_int.Omega ->
        "ω"
    | `Top -> "⊤"
    | `Bottom -> "⊥"
    | `Bool true -> "true"
    | `Bool false -> "false"
    | `Tree _ -> "<tree>"
    | `Closure _ -> "<closure>"

  let rec of_value : int_domain:Abstract_int.domain -> Value.t -> t =
   fun ~int_domain -> function
    | `Num x -> `AbsInt (Abstract_int.lift0 int_domain x)
    | `Bool x -> `Bool x
    | `List x -> `List (List.map x ~f:(of_value ~int_domain))
    | `Tree x -> `Tree (Tree.map x ~f:(of_value ~int_domain))
    | `Closure (expr, ctx) ->
        `Closure (Abstract_expr.of_expr expr, Ctx.map ctx ~f:(of_value ~int_domain))
    | `Unit -> `Bottom

  let rec to_expr : t -> Abstract_expr.t = function
    | `AbsInt x -> `AbsInt x
    | `AbsEq x -> `AbsEq x
    | `AbsList x -> `AbsList (Abstract_list.map ~f:to_expr x)
    | `Bool x -> `Bool x
    | `List x -> `List (List.map ~f:to_expr x)
    | `Tree x -> `Tree (Tree.map ~f:to_expr x)
    | v -> failwiths "Unsupported value." v [%sexp_of: t]

  let eval :
         ?recursion_limit:[`Unlimited | `Limited of int]
      -> ?ctx:t Ctx.t
      -> int_domain:Abstract_int.domain
      -> list_domain:Abstract_list.domain
      -> Abstract_expr.t
      -> t =
   fun ?recursion_limit:(limit = `Unlimited) ?(ctx = Ctx.empty ()) ~int_domain
       ~list_domain expr ->
    let rec ev ctx count expr =
      let continue =
        match limit with `Unlimited -> true | `Limited lim -> count < lim
      in
      if not continue then (
        printf "Hit recursion limit.\n" ;
        `Top )
      else
        let count = count + 1 in
        match expr with
        | `AbsInt x -> `AbsInt x
        | `AbsEq x -> `AbsEq x
        | `AbsList (Abstract_list.List xs) ->
            `AbsList (Abstract_list.List (List.map xs ~f:(ev ctx count)))
        | `AbsList Abstract_list.Omega -> `AbsList Abstract_list.Omega
        | `Num x -> `AbsInt (Abstract_int.lift0 int_domain x)
        | `Bool x -> `Bool x
        | `List x -> `List (List.map x ~f:(ev ctx count))
        | `Tree x -> `Tree (Tree.map x ~f:(ev ctx count))
        | `Lambda _ as lambda -> `Closure (lambda, ctx)
        | `Id id -> ( match Ctx.lookup ctx id with Some v -> v | None -> `Bottom )
        | `Let (name, bound, body) ->
            let ctx' = ref (Ctx.to_string_map ctx) in
            Ctx.update ctx' name (ev ctx' count bound) ;
            ev ctx' count body
        | `Apply (func, raw_args) -> (
            let args = List.map ~f:(ev ctx count) raw_args in
            match ev ctx count func with
            | `Closure (`Lambda (arg_names, body), enclosed_ctx) -> (
              match List.zip arg_names args with
              | Some bindings ->
                  let ctx' =
                    List.fold_left bindings ~init:enclosed_ctx
                      ~f:(fun ctx' (arg_name, value) -> Ctx.bind ctx' arg_name value
                    )
                  in
                  ev ctx' count body
              | None -> `Bottom )
            | _ -> `Top )
        | `Op (Expr.Op.If, args) -> (
          match args with
          | [ux; uy; uz] -> (
            match ev ctx count ux with
            | `Bool x -> if x then ev ctx count uy else ev ctx count uz
            | `Bottom -> `Bottom
            | _ -> `Top )
          | _ -> `Bottom )
        | `Op (op, args) -> (
            let args = List.map ~f:(ev ctx count) args in
            if List.mem ~equal:( = ) args `Bottom then `Bottom
            else
              let module O = Expr.Op in
              let module AI = Abstract_int in
              let module AL = Abstract_list in
              match op with
              | O.Plus -> (
                match args with
                | [`AbsInt AI.Omega; `AbsInt _] | [`AbsInt _; `AbsInt AI.Omega] ->
                    `Top
                | [`AbsInt x; `AbsInt y] -> `AbsInt (AI.lift2 int_domain ( + ) x y)
                | _ -> `Top )
              | O.Minus -> (
                match args with
                | [`AbsInt AI.Omega; _] -> `Top
                | [`AbsInt x; `AbsInt y] ->
                    `AbsInt (Abstract_int.lift2 int_domain ( - ) x y)
                | _ -> `Top )
              | O.Mul -> (
                match args with
                | [`AbsInt AI.Omega; `AbsInt _] | [`AbsInt _; `AbsInt AI.Omega] ->
                    `Top
                | [`AbsInt x; `AbsInt y] ->
                    `AbsInt (Abstract_int.lift2 int_domain (fun x y -> x * y) x y)
                | _ -> `Top )
              | O.Div -> (
                match args with
                | [_; `AbsInt (Abstract_int.Int 0)] -> `Bottom
                | [`AbsInt AI.Omega; `AbsInt _] | [`AbsInt _; `AbsInt AI.Omega] ->
                    `Top
                | [`AbsInt x; `AbsInt y] ->
                    `AbsInt (Abstract_int.lift2 int_domain ( / ) x y)
                | _ -> `Top )
              | O.Mod -> (
                match args with
                | [_; `AbsInt (Abstract_int.Int 0)] -> `Bottom
                | [`AbsInt AI.Omega; `AbsInt _] | [`AbsInt _; `AbsInt AI.Omega] ->
                    `Top
                | [`AbsInt x; `AbsInt y] ->
                    `AbsInt (Abstract_int.lift2 int_domain ( % ) x y)
                | _ -> `Top )
              | O.Eq -> (
                match args with
                | [x; y] -> (
                  match equal x y with
                  | `Bool x -> `Bool x
                  | `Bottom -> `Bottom
                  | `Top -> `Top )
                | _ -> `Bottom )
              | O.Neq -> (
                match args with
                | [x; y] -> (
                  match equal x y with
                  | `Bool x -> `Bool (not x)
                  | `Bottom -> `Bottom
                  | `Top -> `Top )
                | _ -> `Bottom )
              | O.Lt -> (
                match args with
                | [`AbsInt (AI.Int x); `AbsInt (AI.Int y)] -> `Bool (x < y)
                | _ -> `Top )
              | O.Gt -> (
                match args with
                | [`AbsInt (AI.Int x); `AbsInt (AI.Int y)] -> `Bool (x > y)
                | _ -> `Top )
              | O.Leq -> (
                match args with
                | [`AbsInt (AI.Int x); `AbsInt (AI.Int y)] -> `Bool (x <= y)
                | _ -> `Top )
              | O.Geq -> (
                match args with
                | [`AbsInt (AI.Int x); `AbsInt (AI.Int y)] -> `Bool (x >= y)
                | _ -> `Top )
              | O.And -> (
                match args with
                | [`Bool x; `Bool y] -> `Bool (x && y)
                | [`Bool true; x] | [x; `Bool true] -> x
                | [`Bool false; _] | [_; `Bool false] -> `Bool false
                | _ -> `Top )
              | O.Or -> (
                match args with
                | [`Bool x; `Bool y] -> `Bool (x || y)
                | [`Bool false; x] | [x; `Bool false] -> x
                | [`Bool true; _] | [_; `Bool true] -> `Bool true
                | _ -> `Top )
              | O.Not -> (
                match args with [`Bool x] -> `Bool (not x) | _ -> `Top )
              | O.Cons -> (
                match args with
                | [x; `AbsList (AL.List xs)] ->
                    if List.length xs >= list_domain.AL.max_length then
                      `AbsList Abstract_list.Omega
                    else `AbsList (AL.List (x :: xs))
                | [_; `AbsList Abstract_list.Omega] -> `AbsList Abstract_list.Omega
                | [x; `List y] -> `List (x :: y)
                | _ -> `Top )
              | O.RCons -> (
                match args with
                | [`AbsList (AL.List xs); x] ->
                    if List.length xs >= list_domain.AL.max_length then
                      `AbsList Abstract_list.Omega
                    else `AbsList (AL.List (x :: xs))
                | [`AbsList Abstract_list.Omega; _] -> `AbsList Abstract_list.Omega
                | [`List y; x] -> `List (x :: y)
                | _ -> `Top )
              | O.Car -> (
                match args with
                | [`AbsList (AL.List (x :: _))] -> x
                | [`AbsList Abstract_list.Omega] -> `Top
                | [`List (x :: _)] -> x
                | [`AbsList (AL.List [])] -> `Bottom
                | [`List []] -> `Bottom
                | _ -> `Top )
              | O.Cdr -> (
                match args with
                | [`AbsList (AL.List (_ :: xs))] -> `AbsList (AL.List xs)
                | [`AbsList Abstract_list.Omega] -> `Top
                | [`List (_ :: xs)] -> `List xs
                | [`AbsList (AL.List [])] -> `Bottom
                | [`List []] -> `Bottom
                | _ -> `Top )
              | O.Value -> (
                match args with
                | [`Tree Tree.Empty] -> `Bottom
                | [`Tree (Tree.Node (x, _))] -> x
                | _ -> `Top )
              | O.Children -> (
                match args with
                | [`Tree Tree.Empty] -> `List []
                | [`Tree (Tree.Node (_, x))] ->
                    `List (List.map x ~f:(fun e -> `Tree e))
                | _ -> `Top )
              | O.Tree -> (
                match args with
                | [x; `List y] ->
                    let y' =
                      List.map y ~f:(fun e ->
                          match e with `Tree t -> t | _ -> Tree.Node (e, []) )
                    in
                    `Tree (Tree.Node (x, y'))
                | _ -> `Top )
              | O.If -> failwith "Unreachable." )
    in
    ev ctx 0 expr

  let lift :
      ?ctx:int Value.Map.t -> domain -> Type.t -> Value.t -> t * int Value.Map.t =
    let module T = Type in
    fun ?(ctx = Value.Map.empty) d t v ->
      let count = ref 0 in
      let ctx = ref ctx in
      let rec lift d t v =
        match (t, v) with
        | T.Const_t T.Num_t, `Num x -> `AbsInt (Abstract_int.lift0 d.int x)
        | T.Const_t T.Bool_t, `Bool x -> `Bool x
        | T.App_t ("list", [elem_t]), `List x ->
            let x' = List.map ~f:(lift d elem_t) x in
            `AbsList (Abstract_list.lift d.list x')
        | T.Var_t _, v -> (
          match Map.find !ctx v with
          | Some id -> `AbsEq (Abstract_eq.Elem id)
          | None ->
              if !count <= d.eq.Abstract_eq.max_distinct then (
                let id = !count in
                ctx := Map.set !ctx ~key:v ~data:id ;
                incr count ;
                `AbsEq (Abstract_eq.Elem id) )
              else `AbsEq Abstract_eq.Omega )
        | t, v ->
            failwiths "Unsupported or ill-typed." (t, v)
              [%sexp_of: Type.t * Value.t]
      in
      let ret = lift d t v in
      (ret, !ctx)

  exception TopValue

  exception BottomValue

  let lower : ?ctx:Value.t Int.Map.t -> t -> Value.t =
   fun ?(ctx = Int.Map.empty) v ->
    let rec lower = function
      | `AbsInt (Abstract_int.Int x) -> `Num x
      | `AbsEq (Abstract_eq.Elem x) -> (
        match Map.find ctx x with
        | Some v' -> v'
        | None -> failwith "No backwards mapping for equality element." )
      | `AbsList (Abstract_list.List x) | `List x -> `List (List.map ~f:lower x)
      | `Bool x -> `Bool x
      | `Top -> raise TopValue
      | `Bottom -> raise BottomValue
      | `AbsInt Abstract_int.Omega
       |`AbsEq Abstract_eq.Omega
       |`AbsList Abstract_list.Omega ->
          raise TopValue
      | `Closure _ | `Tree _ -> raise TopValue
    in
    lower v
end

module Abstract_example = struct
  module T = struct
    type t = Abstract_value.t list * Abstract_value.t [@@deriving compare, sexp]

    let hash = Hashtbl.hash
  end

  include Hashable.Make_and_derive_hash_fold_t (T)
  include T

  let to_string (ins, out) =
    let ins_str =
      List.map ins ~f:Abstract_value.to_string |> String.concat ~sep:", "
    in
    let out_str = Abstract_value.to_string out in
    "(" ^ ins_str ^ ") -> " ^ out_str

  let lift : domain -> Type.t -> Value.t list * Value.t -> t * Value.t Int.Map.t =
    let open Type in
    fun domain type_ (ins, out) ->
      match type_ with
      | Arrow_t (ins_t, out_t) ->
          let ins_rev, ctx =
            List.fold2_exn ins ins_t
              ~f:(fun (ins, ctx) v t ->
                let v', ctx = Abstract_value.lift ~ctx domain t v in
                (v' :: ins, ctx) )
              ~init:([], Value.Map.empty)
          in
          let out, ctx = Abstract_value.lift ~ctx domain out_t out in
          let ins = List.rev ins_rev in
          let ctx =
            Map.to_alist ctx |> List.map ~f:Tuple.T2.swap |> Int.Map.of_alist_exn
          in
          ((ins, out), ctx)
      | _ -> failwith "Unexpected type."

  let lift x y = Timer.run_with_time timer "lifting" (fun () -> lift x y)

  let lower :
         Value.t Int.Map.t
      -> t
      -> [ `Ex of [`Value of Value.t | `Top] list * [`Value of Value.t | `Top]
         | `Bottom ] =
   fun ctx (ins, out) ->
    try
      let ins =
        List.map ins ~f:(fun i ->
            try `Value (Abstract_value.lower ~ctx i)
            with Abstract_value.TopValue -> `Top )
      in
      let out =
        try `Value (Abstract_value.lower ~ctx out) with Abstract_value.TopValue ->
          `Top
      in
      `Ex (ins, out)
    with Abstract_value.BottomValue -> `Bottom

  let lower x y = Timer.run_with_time timer "lowering" (fun () -> lower x y)

  let join : t -> t -> t =
   fun (i1, o1) (i2, o2) ->
    (List.map2_exn i1 i2 ~f:Abstract_value.join, Abstract_value.join o1 o2)

  module V = struct
    module T = struct
      type t = Expr.t * Value.t String.Map.t [@@deriving sexp, compare]

      let hash = Hashtbl.hash
    end

    include T
    include Hashable.Make_and_derive_hash_fold_t (T)
  end

  let eval : Value.t String.Map.t -> Expr.t -> Value.t =
    let table = V.Table.create () in
    Counter.add_func counter "eval_distinct_args" "" (fun () -> Hashtbl.length table) ;
    fun ctx expr ->
      match Hashtbl.find table (expr, ctx) with
      | Some v -> v
      | None ->
          let v = Eval.eval ~recursion_limit:100 (ref ctx) expr in
          ignore (Hashtbl.add table ~key:(expr, ctx) ~data:v) ;
          v

  let of_spec_and_args :
         library:Library.t
      -> args:Sk.t list
      -> Type.t
      -> domain
      -> Examples.example
      -> t * Value.t Int.Map.t =
    let module AV = Abstract_value in
    let lift :
           Expr.t StaticDistance.Map.t
        -> Value.t String.Map.t
        -> domain
        -> Type.t
        -> Skeleton.t list
        -> Value.t
        -> t * Value.t Int.Map.t =
      let open Type in
      fun expr_ctx eval_ctx domain type_ ins out ->
        match type_ with
        | Arrow_t (ins_t, out_t) ->
            let ins_rev, ctx =
              List.fold2_exn ins ins_t
                ~f:(fun (ins, ctx) sk t ->
                  let v', ctx =
                    try
                      let e = Sk.to_expr ~ctx:expr_ctx sk in
                      run_with_time "eval" (fun () -> eval eval_ctx e)
                      |> AV.lift ~ctx domain t
                    with
                    | Eval.HitRecursionLimit ->
                        cincr "recursionlimit_failure" ;
                        (`Top, ctx)
                    | Eval.RuntimeError _ ->
                        cincr "eval_failure" ;
                        (`Bottom, ctx)
                  in
                  (v' :: ins, ctx) )
                ~init:([], Value.Map.empty)
            in
            let out, ctx = AV.lift ~ctx domain out_t out in
            let ins = List.rev ins_rev in
            let ctx =
              Map.to_alist ctx |> List.map ~f:Tuple.T2.swap |> Int.Map.of_alist_exn
            in
            ((ins, out), ctx)
        | _ -> failwith "Unexpected type."
    in
    fun ~library ~args type_ domain spec ->
      let ctx, ret = spec in
      let expr_ctx = StaticDistance.Map.map ctx ~f:Expr.of_value in
      lift expr_ctx library.Library.value_ctx domain type_ args ret
end

module Function_spec = struct
  module AE = Abstract_example
  module AV = Abstract_value

  type t = {examples: AE.t AE.Table.t; domain: domain} [@@deriving sexp]

  let to_string : t -> string =
   fun t ->
    AE.Table.to_alist t.examples
    |> List.map ~f:(fun (in_ex, out_ex) ->
           sprintf "%s => %s\n" (AE.to_string in_ex) (AE.to_string out_ex) )
    |> String.concat ~sep:"\n"

  let of_examples : domain -> AE.t list -> t =
    let module Seq = Sequence in
    fun domain exs ->
      let num_args = List.hd_exn exs |> Tuple.T2.get1 |> List.length in
      let table = AE.Table.create () in
      Seq.cartesian_product (Seq.range 0 num_args) (Seq.of_list exs)
      |> Seq.iter ~f:(fun (n, ex) ->
             let ins, out = ex in
             let key = (List.take ins n @ List.repeat (num_args - n) `Top, out) in
             Hashtbl.add_multi table ~key ~data:ex ) ;
      let table = Hashtbl.map table ~f:(List.fold_left1 ~f:AE.join) in
      {domain; examples= table}

  let of_file : string -> t = fun fn -> Sexp.load_sexp fn |> [%of_sexp: t]

  let to_file : t -> string -> unit =
   fun t fn -> [%sexp_of: t] t |> Sexp.save_mach fn

  let find : t -> AE.t -> AE.t =
   fun t ex ->
    match run_with_time "lookup" (fun () -> Hashtbl.find t.examples ex) with
    | Some ex' -> ex'
    | None ->
        cincr "no_match" ;
        let ins, out = ex in
        (List.repeat (List.length ins) `Bottom, out)
end

let infer_examples :
       library:Library.t
    -> specs:Function_spec.t String.Map.t
    -> op:[`Builtin of Expr.Op.t | `Func of string]
    -> args:Sk.t list
    -> Examples.t
    -> Sp.t list =
 fun ~library ~specs ~op ~args exs ->
  let arity = List.length args in
  let op_type =
    match op with
    | `Builtin op -> Expr.Op.typ op
    | `Func op -> Map.find_exn library.Library.type_ctx op
  in
  let op_str =
    match op with `Builtin op -> Expr.Op.to_string op | `Func op -> op
  in
  match Map.find specs op_str with
  | Some op_specs ->
      let exs = Examples.to_list exs in
      let ctxs = List.map exs ~f:Tuple.T2.get1 in
      let deduced_exs =
        List.map exs ~f:(fun ex ->
            let ax, m =
              Abstract_example.of_spec_and_args ~library ~args op_type
                op_specs.Function_spec.domain ex
            in
            Abstract_example.lower m (Function_spec.find op_specs ax) )
      in
      let arg_specs =
        List.map2_exn ctxs deduced_exs ~f:(fun ctx -> function
          | `Bottom -> List.repeat arity Sp.bottom
          | `Ex (ins, _) ->
              List.map ins ~f:(function
                | `Top -> Sp.top
                | `Value v -> Examples.singleton (ctx, v) |> Examples.to_spec ) )
      in
      let per_arg_specs = List.transpose_exn arg_specs in
      let arg_examples =
        List.map per_arg_specs ~f:(fun arg_spec ->
            if List.exists arg_spec ~f:(Sp.equal Sp.bottom) then Sp.bottom
            else
              let arg_exs =
                List.filter_map arg_spec ~f:(fun sp ->
                    match Sp.data sp with
                    | Sp.Top -> None
                    | Examples.Examples exs -> Some (Examples.to_list exs)
                    | _ -> failwith "BUG: Unexpected specification." )
                |> List.concat
              in
              match arg_exs with
              | [] -> Sp.top
              | _ -> (
                match Examples.of_list arg_exs with
                | Ok sp -> Examples.to_spec sp
                | Error _ -> Sp.bottom ) )
      in
      arg_examples
  | None -> List.repeat arity Sp.top

let push_specs_exn' :
    specs:Function_spec.t String.Map.t -> library:Library.t -> Sk.t -> Sk.t =
 fun ~specs ~library sk ->
  let rec push sk =
    let spec = Sk.spec sk in
    match Sk.ast sk with
    | Sk.Num _ | Sk.Bool _ | Sk.Id _ | Sk.Hole _ -> sk
    | Sk.List l -> Sk.list (List.map l ~f:push) spec
    | Sk.Tree t -> Sk.tree (Tree.map t ~f:push) spec
    | Sk.Let {bound; body} -> Sk.let_ (push bound) (push body) spec
    | Sk.Lambda {num_args; body} -> Sk.lambda num_args (push body) spec
    | Sk.Op {op; args} -> (
      match Sp.data spec with
      | Examples.Examples exs ->
          cincr "have_examples" ;
          let arg_specs =
            run_with_time "infer" (fun () ->
                infer_examples ~library ~specs ~op:(`Builtin op) ~args exs )
          in
          let args = List.map2_exn args arg_specs ~f:Sk.replace_spec in
          Sk.op op (List.map args ~f:push) spec
      | _ ->
          cincr "no_examples" ;
          Sk.op op (List.map args ~f:push) spec )
    | Sk.Apply {func; args} -> (
      match (Sp.data spec, Sk.ast func) with
      | Examples.Examples exs, Sk.Id (Sk.Id.Name name) ->
          cincr "have_examples" ;
          let arg_specs =
            run_with_time "infer" (fun () ->
                infer_examples ~library ~specs ~op:(`Func name) ~args exs )
          in
          let args = List.map2_exn args arg_specs ~f:Sk.replace_spec in
          (* printf "Runtime %s.\n" (Time.Span.to_string_hum runtime); *)
          (* printf "Pushing specifications for %s.\n" name; *)
          (* print_endline "Args:"; *)
          (* Util.print_sexp args [%sexp_of:Sp.t Sk.t list]; *)
          (* print_endline "Parent spec:"; *)
          (* Util.print_sexp s [%sexp_of:Sp.t]; *)
          (* print_endline "Arg specs:"; *)
          (* Util.print_sexp arg_specs [%sexp_of:Sp.t list]; *)
          (* print_newline (); *)
          Sk.apply func (List.map ~f:push args) spec
      | _ ->
          cincr "no_examples" ;
          Sk.apply func (List.map ~f:push args) spec )
  in
  run_with_time "total" (fun () -> push sk)

let create spec_dir library =
  let specs =
    if Sys.is_directory spec_dir = `Yes then
      let spec_files =
        Sys.ls_dir spec_dir |> List.map ~f:(fun f -> spec_dir ^ "/" ^ f)
      in
      List.map spec_files ~f:(fun sf ->
          let name = Filename.chop_suffix (Filename.basename sf) "-examples.sexp" in
          (name, Function_spec.of_file sf) )
      |> String.Map.of_alist_exn
    else failwith "Could not load component specifications."
  in
  fun sk -> Some (push_specs_exn' ~specs ~library sk)
