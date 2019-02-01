open Core
open Collections
open Infer
open Util

type t = Expr.t * Expr.t [@@deriving sexp, compare]

(** Parse an example from a string. *)
let of_string_exn (s : string) : t =
  let lexbuf = Lexing.from_string s in
  try Parser_sexp.example_eof Lexer_sexp.token lexbuf with
  | Parser_sexp.Error -> raise (Ast.ParseError s)
  | Lexer_sexp.SyntaxError _ -> raise (Ast.ParseError s)
  | Parsing.Parse_error -> raise (Ast.ParseError s)

let of_string (s : string) : t Or_error.t =
  try Ok (of_string_exn s) with Ast.ParseError s ->
    error "Parsing Example.t failed." s [%sexp_of: string]

(** Convert an example to a string. *)
let to_string (ex : t) : string =
  let e1, e2 = ex in
  sprintf "%s -> %s" (Expr.to_string e1) (Expr.to_string e2)

let to_triple = function
  | `Apply (`Id name, inputs), result -> (name, inputs, result)
  | ex -> failwith (sprintf "Malformed example: %s" (to_string ex))

(** Get the name of the target function from a list of examples. *)
let name (exs : t list) : Ast.id =
  let names =
    List.map exs ~f:(fun ex ->
        let name, _, _ = to_triple ex in
        name )
    |> List.dedup_and_sort ~compare:String.compare
  in
  match names with
  | [] -> failwith "Example list is empty."
  | [name] -> name
  | _ :: _ -> failwith "Multiple target names in example list."

(** Split a list of examples into a list of lists of examples, each of
    which represents a distinct function. *)
let split (exs : t list) : (string * t list) list =
  List.map exs ~f:(fun ex ->
      let name, _, _ = to_triple ex in
      (name, ex) )
  |> List.group ~break:(fun (n1, _) (n2, _) -> n1 <> n2)
  |> List.map ~f:(fun exs ->
         match exs with
         | (name, _) :: _ -> (name, List.map exs ~f:Tuple.T2.get2)
         | _ -> failwith "Expected a non-empty list." )

(** Infer a function signature from input/output examples. *)
let signature ?(ctx = Ctx.empty ()) (examples : t list) : Type.t =
  let _, inputs, results = List.map examples ~f:to_triple |> unzip3 in
  let res_typ =
    match TypedExpr.to_type (infer_exn ctx (`List results)) with
    | Type.App_t ("list", [t]) -> t
    | t -> failwith (sprintf "Unexpected result type: %s" (Type.to_string t))
  in
  let typ =
    match inputs with
    | args :: _ ->
        let num_args = List.length args in
        Type.Arrow_t
          ( List.range 0 num_args |> List.map ~f:(fun _ -> Infer.fresh_free 0)
          , res_typ )
    | [] -> failwith "Example list is empty."
  in
  let ctx = Ctx.bind ctx (name examples) typ in
  let name' = name examples in
  List.iter inputs ~f:(fun input ->
      let _ = Infer.infer ctx (`Apply (`Id name', input)) in
      () ) ;
  typ

let to_vctx (example : t) (arg_names : string list) : Expr.t Ctx.t =
  let _, inputs, _ = to_triple example in
  List.zip_exn arg_names inputs |> Ctx.of_alist_exn

let check (examples : (t * Expr.t Ctx.t) list) : bool =
  (* Is there a pair of examples such that the outer contexts and LHSs
  are equal, but the RHSs are not? *)
  not
    (List.exists examples ~f:(fun ((lhs, rhs), vctx) ->
         List.exists examples ~f:(fun ((lhs', rhs'), vctx') ->
             Ctx.equal Expr.equal vctx vctx' && lhs = lhs' && rhs <> rhs' ) ))
