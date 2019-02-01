open Core
open Ast

type id = string

exception Non_unifiable

exception Translation_error

exception Unknown

type term = Var of id | Term of id * term list [@@deriving sexp]

type sterm =
  | Cons of sterm * sterm
  | K of id
  (* Konstant *)
  | V of id
  (* Variable *)
  | U of id * bool

(* Volatile? variable *)

type substitution = (id * term) list [@@deriving sexp]

let rec sterm_to_string (s : sterm) : string =
  let ts = sterm_to_string in
  match s with
  | Cons (x, xs) -> sprintf "Cons(%s, %s)" (ts x) (ts xs)
  | K x -> x
  | V x -> x
  | U (x, _) -> x

(* Convert an expression to a unifiable term. *)
let sterm_of_expr_value : ExprValue.t -> sterm option =
 fun e ->
  let rec f e =
    match e with
    | `Unit -> K "unit"
    | `Num x -> K (Int.to_string x)
    | `Bool x -> K (if x then "true" else "false")
    | `List [] -> K "[]"
    | `List (x :: xs) -> Cons (f x, f (`List xs))
    | `Id x -> V x
    | `Op (RCons, [xs; x]) | `Op (Ast.Cons, [x; xs]) -> Cons (f x, f xs)
    | `Apply _ -> V (ExprValue.to_string e)
    | `Closure _ | `Let _ | `Tree _ | `Lambda _ | `Op _ -> raise Unknown
  in
  try Some (f e) with Unknown -> None

let sterm_of_expr (e : Expr.t) : sterm option =
  let rec f e =
    match e with
    | `Num x -> K (Int.to_string x)
    | `Bool x -> K (if x then "true" else "false")
    | `List [] -> K "[]"
    | `List (x :: xs) -> Cons (f x, f (`List xs))
    | `Id x -> V x
    | `Op (RCons, [xs; x]) | `Op (Ast.Cons, [x; xs]) -> Cons (f x, f xs)
    | `Let _ | `Tree _ | `Apply _ | `Lambda _ | `Op _ -> raise Unknown
  in
  try Some (f e) with Unknown -> None

let sterm_of_value v =
  let rec f v =
    match v with
    | `Num x -> K (Int.to_string x)
    | `Bool x -> K (if x then "true" else "false")
    | `List [] -> K "[]"
    | `List (x :: xs) -> Cons (f x, f (`List xs))
    | `Unit | `Closure _ | `Tree _ -> raise Unknown
  in
  try Some (f v) with Unknown -> None

(* let sterm_of_result r = *)
(*   let fresh_name = Util.Fresh.mk_fresh_name_fun () in *)
(*   let open Symbolic_execution in *)
(*   let rec f r = match r with *)
(*     | Num_r x -> K (Int.to_string x) *)
(*     | Bool_r x -> K (if x then "true" else "false") *)
(*     | List_r [] -> K "[]" *)
(*     | List_r (x::xs) -> Cons (f x, f (List_r xs)) *)
(*     | Id_r (Skeleton.Id.StaticDistance sd) -> V (StaticDistance.to_string sd) *)
(*     | Id_r (Skeleton.Id.Name id) -> V id *)
(*     | Op_r (RCons, [xs; x]) *)
(*     | Op_r (Cons, [x; xs]) -> Cons (f x, f xs) *)
(*     | Symbol_r id -> V (Int.to_string id) *)
(*     | Apply_r _ -> V (fresh_name ()) *)
(*     | Closure_r _ *)
(*     | Tree_r _ *)
(*     | Op_r _ -> raise Unknown *)
(*   in try Some (f r) with Unknown -> None *)

(* the occurs check *)
let rec occurs (x : id) (t : term) : bool =
  match t with Var y -> x = y | Term (_, s) -> List.exists ~f:(occurs x) s

(* substitute term s for all occurrences of variable x in term t *)
let rec subst (s : term) (x : id) (t : term) : term =
  match t with
  | Var y -> if x = y then s else t
  | Term (f, u) -> Term (f, List.map ~f:(subst s x) u)

(* apply a substitution right to left *)
let apply (s : substitution) (t : term) : term =
  List.fold_right ~f:(fun (x, u) -> subst u x) s ~init:t

(* unify one pair *)
let rec unify_one (s : term) (t : term) : substitution =
  match (s, t) with
  | Var x, Var y -> if x = y then [] else [(x, t)]
  | Term (f, sc), Term (g, tc) ->
      if f = g && List.length sc = List.length tc then unify (List.zip_exn sc tc)
      else raise Non_unifiable
  | Var x, (Term (_, _) as t) | (Term (_, _) as t), Var x ->
      if occurs x t then raise Non_unifiable else [(x, t)]

(* unify a list of pairs *)
and unify (s : (term * term) list) : substitution =
  match s with
  | [] -> []
  | (x, y) :: t ->
      let t2 = unify t in
      let t1 = unify_one (apply t2 x) (apply t2 y) in
      t1 @ t2

let fvar = ref 0

let fresh () : string =
  fvar := !fvar + 1 ;
  "V" ^ string_of_int !fvar

(* Support code *)
let rec translate (s : sterm) : term =
  match s with
  | Cons (x, y) ->
      let t1 = translate x and t2 = translate y in
      Term ("Cons", [t1] @ [t2])
  | K c -> Term (c, [])
  | V c | U (c, _) -> Var c

let rec retranslate (t : term) : sterm =
  match t with
  | Var v -> V v
  | Term (k, []) -> K k
  | Term ("Cons", h :: t) -> (
    match t with
    | [tt] -> Cons (retranslate h, retranslate tt)
    | _ -> raise Translation_error )
  | _ -> raise Translation_error

let rec to_string (s : sterm) : string =
  match s with
  | Cons (h, t) -> "Cons(" ^ to_string h ^ "," ^ to_string t ^ ")"
  | K t | V t -> t
  | U (t, vol) -> if vol then raise Unknown (* sanity check *) else t

let sub_to_string (s : substitution) : string =
  List.map ~f:(fun (i, t) -> i ^ " = " ^ to_string (retranslate t)) s
  |> String.concat ~sep:","

and print_sub (s : substitution) =
  let ss = List.map ~f:(fun (i, t) -> i ^ " = " ^ to_string (retranslate t)) s in
  List.iter ~f:(fun t -> Printf.printf "%s\n" t) ss

(* End Support code *)

(* "concretize" one volatile term with the one from hypothesis *)
let rec make_one_concrete (s1 : sterm) (s3 : sterm) (made : bool) =
  if made then (made, s3)
  else
    match (s1, s3) with
    | Cons (h1, t1), Cons (h2, t2) ->
        let md1, sh = make_one_concrete h1 h2 made in
        let md2, st = make_one_concrete t1 t2 md1 in
        (md2, Cons (sh, st))
    | K _, K _ | V _, V _ | _, U (_, false) -> (false, s3)
    | K _, U (_, true) | V _, U (_, true) -> (true, s1)
    | Cons (_, _), U (_, true) ->
        (true, Cons (U (fresh (), true), U (fresh (), true)))
    | _, _ -> raise Unknown

(* the non-volatile term is now part of the core *)
let make_one_non_volatile (s3 : sterm) =
  let rec aux (ss : sterm) (made : bool) =
    if made then (made, ss)
    else
      match ss with
      | Cons (h, t) ->
          let md1, sh = aux h made in
          let md2, st = aux t md1 in
          (md2, Cons (sh, st))
      | K _ | V _ | U (_, false) -> (false, ss)
      | U (u, true) -> (true, U ("C" ^ u, false))
  in
  let _, ss3 = aux s3 false in
  ss3

(* concretize <-> unify loop until we cannot concretize anymore *)
let rec unifiable_core_aux (s1 : sterm) (s3 : sterm) (s2 : sterm) =
  try
    let made, s3' = make_one_concrete s1 s3 false in
    let sub = unify [(translate s3', translate s2)] in
    if not made then (s3', sub) else unifiable_core_aux s1 s3' s2
  with Non_unifiable -> unifiable_core_aux s1 (make_one_non_volatile s3) s2

(* Main *)
let unifiable_core (s1 : sterm) (s2 : sterm) =
  try
    let sub = unify [(translate s1, translate s2)] in
    (s1, sub)
  with Non_unifiable -> unifiable_core_aux s1 (U (fresh (), true)) s2
