type id = string

exception Non_unifiable
exception Translation_error

type term =
  | Var of id
  | Term of id * term list

type sterm =
  | Cons of sterm * sterm
  | K of id
  | V of id

type substitution = (id * term) list

(* the occurs check *)
let rec occurs (x : id) (t : term) : bool =
  match t with
  | Var y -> x = y
  | Term (_, s) -> List.exists (occurs x) s

(* substitute term s for all occurrences of variable x in term t *)
let rec subst (s : term) (x : id) (t : term) : term =
  match t with
  | Var y -> if x = y then s else t
  | Term (f, u) -> Term (f, List.map (subst s x) u)

(* apply a substitution right to left *)
let apply (s : substitution) (t : term) : term =
  List.fold_right (fun (x, u) -> subst u x) s t

(* unify one pair *)
let rec unify_one (s : term) (t : term) : substitution =
  match (s, t) with
  | (Var x, Var y) -> if x = y then [] else [(x, t)]
  | (Term (f, sc), Term (g, tc)) ->
      if f = g && List.length sc = List.length tc
      then unify (List.combine sc tc)
      else raise Non_unifiable
  | ((Var x, (Term (_, _) as t)) | ((Term (_, _) as t), Var x)) ->
      if occurs x t
      then raise Non_unifiable
      else [(x, t)]

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
  fvar := !fvar + 1; "V" ^ string_of_int !fvar

(* make one term symbolic *)
let rec make_one_symbolic (s: sterm) : sterm =
  match s with
  | Cons(h, t) ->
    (match h, t with
    | _, Cons(_,_) -> Cons(h, make_one_symbolic t)
    | Cons(_,_), _ -> Cons(make_one_symbolic h, t)
    | _, K(_)      -> Cons(h, V(fresh ()))
    | K(_), _      -> Cons(V(fresh ()), t)
    | _            -> V(fresh ()))
  | K(_) -> V(fresh ())
  | V(_) -> failwith "reached top-level unifier"

(* Support code *)
let rec translate (s: sterm) : term =
  match s with
  | Cons(x, y) -> 
      let t1 = translate x and t2 = translate y in
      Term("Cons", [t1] @ [t2])
  | K(c) -> Term(c, [])
  | V(c) -> Var(c)

let rec retranslate (t: term) : sterm =
  match t with
  | Var(v) -> V(v)
  | Term(k, []) -> K(k)
  | Term("Cons", h::t) ->
    (match t with
    | tt::[] -> Cons(retranslate h, retranslate tt)
    | _ -> raise Translation_error)
  | _ -> raise Translation_error

let rec to_string (s: sterm) : string =
  match s with
  | Cons(h, t) -> "Cons(" ^ (to_string h) ^ "," ^ (to_string t) ^ ")"
  | V(v) -> v
  | K(k) -> k

and print_sub (s: substitution) = 
  let ss = List.map (fun (i, t) -> i ^ " = " ^ (to_string (retranslate t))) s
  in List.iter (fun t -> Printf.printf "%s\n" t) ss





(* Main function *)
let rec unifiable_core (s1: sterm) (s2: sterm) =
  try 
    let sub = unify [translate s1, translate s2] in s1, sub
  with Non_unifiable -> unifiable_core (make_one_symbolic s1) s2

;;

begin
  (*let term1 = Cons(K("1"), Cons(K("2"), K("[]")))
  and term2 = Cons(K("7"), Cons(K("2"), Cons(K("3"), K("[]")))) in*)
  let term1 = Cons(K("1"), Cons(K("2"), K("[]")))
  and term2 = Cons(K("3"), Cons(K("4"), K("[]"))) in
  let core, sub = unifiable_core term1 term2 in
  Printf.printf "%s\n" (to_string core);
  print_sub sub;
end;
