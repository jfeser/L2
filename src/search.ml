open Core.Std
open Printf
open Ast

open Infer
open Structure
open Util

module Stream = struct
  include Stream

  type 'a stream = 'a t
  type 'a matrix = ('a list) stream

  (* Concatenate two streams together. The second stream will not be
  inspected until the first stream is exhausted. *)
  let concat s1 s2 =
    from (fun _ ->
          match peek s1 with
          | Some _ -> Some (next s1)
          | None -> (match peek s2 with
                     | Some _ -> Some (next s2)
                     | None -> None))

  (* Map a function over a stream. *)
  let map s ~f = from (fun _ -> try Some (f (next s)) with Failure -> None)

  (* Map a function over a matrix. *)
  let map_matrix s ~f = map s ~f:(List.map ~f:f)

  (* Create an infinite stream of 'value'. *)
  let repeat (value: 'a) : 'a stream = from (fun _ -> Some value)

  (* Create a finite stream of 'value' of length 'n'. *)
  let repeat_n (n: int) (value: 'a) : 'a stream =
    List.range 0 n |> List.map ~f:(fun _ -> value) |> of_list

  let trans : (('a stream) list -> ('a list) stream) = function
    | [] -> repeat []
    | ss -> from (fun _ -> Some (List.map ss ~f:next))

  let diag (s: ('a stream) stream) : (('a list) stream) =
    from (fun i -> Some (List.map (npeek (i + 1) s) ~f:next))

  let join (x: ('a matrix) matrix) : 'a matrix =
    x |> map ~f:trans |> diag |> map ~f:(fun y -> y |> List.concat |> List.concat)

  let compose (f: 'a -> 'b matrix) (g: 'b -> 'c matrix) (x: 'a) : 'c matrix =
    x |> f |> (map ~f:(List.map ~f:g)) |> join

  let group s ~break =
    from (fun _ ->
          let rec collect () =
            match npeek 2 s with
            | [] -> None
            | [_] -> Some [next s]
            | [x; y] -> if break x y then Some [next s] else collect ()
            | _ -> failwith "Stream.npeek returned a larger list than expected."
          in collect ())

  let merge (ss: ('a matrix) list) : 'a matrix =
    from (fun _ ->
          Some (ss
                |> List.filter_map ~f:(fun s -> try Some (next s) with Failure -> None)
                |> List.concat))

  let rec drop s ~f = match peek s with
    | Some x -> if f x then (junk s; drop s ~f:f) else ()
    | None -> ()

  let flatten (m: 'a matrix) : 'a stream =
    let current = ref [] in
    from (fun _ -> match !current with
                   | x::xs -> current := xs; Some x
                   | [] -> drop m ~f:((=) []);
                           (try (match next m with
                                 | [] -> failwith "Failed to drop empty rows."
                                 | x::xs -> current := xs; Some x)
                            with Failure -> None))
end

module MemoStream = struct
  module Typ = struct type t = typ with compare, sexp end
  module TypMap = Map.Make(Typ)

  type memo_stream = {
    index: int ref;
    head: typed_expr list Int.Table.t;
    stream: typed_expr Stream.matrix;
  }

  type t = memo_stream TypMap.t ref

  let empty () = ref TypMap.empty

  (* Get access to a stream of results for 'typ'. *)
  let get memo typ stream : typed_expr Stream.matrix =
    let mstream = match TypMap.find !memo typ with
      | Some s -> s
      | None ->
         let s = { index = ref 0; head = Int.Table.create (); stream = stream (); } in
         memo := TypMap.add !memo ~key:typ ~data:s; s
    in
    Stream.from
      (fun i -> 
       let sc = i + 1 in
       if sc <= !(mstream.index) then Some (Int.Table.find_exn mstream.head sc)
       else (List.range ~stop:`inclusive (!(mstream.index) + 1) sc
             |> List.iter
                  ~f:(fun j ->
                      try Int.Table.add_exn mstream.head ~key:j ~data:(Stream.next mstream.stream);
                          incr mstream.index;
                      with Stream.Failure -> ());
             if sc = !(mstream.index) then Some (Int.Table.find_exn mstream.head sc) else None))
end

let rec enumerate memo init typ : typed_expr Stream.matrix =
  let open Stream in
  let arrow_error () = failwith "Operator is not of type Arrow_t." in

  (* printf "enumerate %s %s.\n" *)
  (*        (List.to_string init ~f:(fun e -> expr_to_string (expr_of_texpr e))) *)
  (*        (typ_to_string typ); *)

  (* Init is finite, so we can construct an init stream by breaking
  init into a list of size classes and returning that list as a
  stream. *)
  let (init_matrix: typed_expr matrix) =
    let init_sizes =
      List.filter init ~f:(fun e -> is_unifiable typ (typ_of_expr e))
      |> List.map ~f:(fun e -> e, size (expr_of_texpr e))
    in
    let max_size = List.fold_left init_sizes ~init:0 ~f:(fun x (_, y) -> if x > y then x else y) in
    List.range ~stop:`inclusive 1 max_size
    |> List.map ~f:(fun s -> List.filter_map init_sizes ~f:(fun (e, s') -> if s = s' then Some e else None))
    |> of_list
  in

  (* Generate an argument list matrix that conforms to the provided list of types. *)
  let args_matrix (arg_typs: typ list) =
    let choose (prev_args: typed_expr list) : (typed_expr list) matrix =
      (* Determine the type of the current argument from the types of
      the already selected arguments and the provided argument
      types. This handles the case where multiple arguments use the
      same polymorphic type variable. *)
      let ctx = Ctx.empty () in
      let prev_typs, (typ'::_) =
        List.split_n (List.map arg_typs ~f:(instantiate ~ctx:ctx (-1))) (List.length prev_args)
      in
      List.iter2_exn prev_args prev_typs
                     ~f:(fun parg ptyp ->
                         (* printf "%s %s %s\n" *)
                         (*        (expr_to_string (expr_of_texpr parg))  *)
                         (*        (typ_to_string (typ_of_expr parg))  *)
                         (*        (typ_to_string ptyp); *)
                         unify_exn (instantiate (-1) (typ_of_expr parg) ~ctx:ctx) ptyp);
      let typ = generalize (-1) typ' in

      (* Generate the argument matrix lazily so that it will not be
         created until the prefix classes are exhausted. *)
      slazy (fun () -> map_matrix (MemoStream.get memo typ (fun () -> enumerate memo init typ))
                                  ~f:(fun arg -> prev_args @ [arg]))
    in
    match arg_typs with
    | x::xs -> (List.fold_left xs ~init:choose ~f:(fun acc _ -> compose acc choose)) []
    | [] -> failwith "Cannot generate args matrix with no arguments."
  in

  let op_matrix op op_typ = match op_typ with
    | Arrow_t (arg_typs, ret_typ) ->
       let prefix = repeat_n (List.length arg_typs) [] in
       let matrix =
         slazy (fun () -> map_matrix (args_matrix arg_typs) ~f:(fun args -> Op ((op, args), ret_typ)))
       in
       concat prefix matrix
    | _ -> arrow_error ()
  in

  (* The op stream is infinite, so it needs more careful handling. *)
  let op_matrices =
    Op.metadata_by_op
    (* Filter all operators that can return the correct type. *)
    |> List.filter ~f:(fun (_, meta) ->
                       match meta.Op.typ with
                       | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
                       | _ -> arrow_error ())

    (* Unify the return type of the operator with the input type. By
    the side effects of unify, all the other free type variables in
    the operator type will reflect the substitution. Now we have
    correct types for the arguments. *)
    |> List.map ~f:(fun (op, meta) ->
                    match instantiate 0 typ, instantiate 0 meta.Op.typ with
                    | typ', (Arrow_t (_, ret_typ) as op_typ) ->
                       unify_exn typ' ret_typ;
                       op, normalize (generalize (-1) op_typ)
                    | _ -> arrow_error ())

    (* Generate a matrix for each operator. *)
    |> List.map ~f:(fun (op, op_typ) -> op_matrix op op_typ)
  in
  merge (init_matrix::op_matrices)
  |> map ~f:(List.filter ~f:(fun x ->
                             let e = expr_of_texpr x in
                             match Rewrite.rewrite e with
                             | Some e' -> e = e'
                             | None -> false))
  (* |> map ~f:(List.map ~f:(fun e -> print_endline (expr_to_string (expr_of_texpr e)); e)) *)

let solve_catamorphic_looped ?(init=[]) (examples: example list) : expr -> expr =
  let initial_spec =
    let target_name = get_target_name examples in
    let target ctx expr =
      let body = Ctx.lookup_exn ctx target_name in
      `Let (target_name, body, expr)
    in
    { target;
      holes = Ctx.of_alist_exn [(target_name, { signature = signature examples;
                                                examples = List.map examples ~f:(fun e -> e, Ctx.empty ());
                                                tctx = Ctx.empty ();
                                                depth = 2;
                               })];
    }
  in

  let rec generate_specs (specs: spec list) : spec list =
    match specs with
    | [] -> []
    | specs ->
       let child_specs = List.concat_map specs
                                         ~f:(fun parent ->
                                             (map_bodies parent)
                                             @ (filter_bodies parent)
                                             @ (fold_bodies parent)
                                             @ (foldt_bodies parent)
                                             @ (recurs_bodies parent)
                                            )
       in
       specs @ (generate_specs child_specs)
  in

  let specs = generate_specs [initial_spec] in

  (* print_endline "Completed structure analysis. Inferred structures:"; *)
  (* List.iter *)
  (*   specs *)
  (*   ~f:(fun spec -> *)
        (* let (hole_bodies: expr Ctx.t) = Ctx.mapi spec.holes ~f:(fun ~key:name ~data:_ -> `Id name) in *)
        (* printf "%s\n" (expr_to_string (spec.target hole_bodies (`Id "_"))); *)
  (*       Ctx.to_alist spec.holes *)
  (*       |> List.iter ~f:(fun (name, hole) -> *)
  (*                        printf "\t%s: %s\n" name (typ_to_string hole.signature); *)
  (*                        List.iter hole.examples ~f:(fun (ex, _) -> printf "\t\t%s\n" (example_to_string ex)))); *)
  (* print_newline (); *)

  let matrix_of_hole hole =
    let init' =
      (Ctx.to_alist hole.tctx |> List.map ~f:(fun (name, typ) -> Id (name, typ)))
      @ (List.map init ~f:(infer (Ctx.empty ())))
    in
    match hole.signature with
    | Arrow_t (arg_typs, ret_typ) ->
       let args = List.map arg_typs ~f:(fun typ -> Fresh.name "x", typ) in
       let arg_names, _ = List.unzip args in
       let init'' = init' @ (List.map args ~f:(fun (name, typ) -> Id (name, typ))) in
       enumerate (MemoStream.empty ()) init'' ret_typ 
       |> Stream.map_matrix ~f:(fun texpr -> 
                                (* printf "%s %s\n"  *)
                                (*        (typ_to_string hole.signature)  *)
                                (*        (expr_to_string (expr_of_texpr texpr)); *)
                                `Lambda (arg_names, expr_of_texpr texpr))
    | typ -> enumerate (MemoStream.empty ()) init' typ 
             |> Stream.map_matrix ~f:(fun tx -> 
                                      (* printf "%s %s\n"  *)
                                      (*        (typ_to_string hole.signature)  *)
                                      (*        (expr_to_string (expr_of_texpr tx)); *)
                                      (expr_of_texpr tx))
  in

  let choose name hole ctx : (expr Ctx.t) Stream.matrix =
    Stream.map_matrix (matrix_of_hole hole) ~f:(Ctx.bind ctx name)
  in

  let solver_of_spec spec =
    let ctx_matrix = match Ctx.to_alist spec.holes with
      | [] -> failwith "Specification has no holes."
      | (name, hole)::hs ->
         (List.fold_left hs
                        ~init:(choose name hole)
                        ~f:(fun matrix (name', hole') -> Stream.compose matrix (choose name' hole')))
           (Ctx.empty ())
    in
    ctx_matrix
    |> Stream.map_matrix ~f:(fun ctx -> let target = spec.target ctx in
                                        print_endline (expr_to_string (target (`Id "_")));
                                        if Verify.verify_examples target examples
                                        then Some target else None)
  in

  let solutions = List.map specs ~f:solver_of_spec |> Stream.merge |> Stream.flatten in

  with_return 
    (fun r ->
     let depth = ref 1 in
     while true do
       List.iter specs 
                 ~f:(fun spec ->
                     let solver = solver_of_spec spec in
                     for i = 1 to !depth do
                       List.iter (Stream.next solver) ~f:(Option.iter ~f:r.return)
                     done;
                     (* let hole_bodies = Ctx.mapi spec.holes ~f:(fun ~key:name ~data:_ -> `Id name) in *)
                     (* printf "Searched %s to depth %d." *)
                     (*        (expr_to_string (spec.target hole_bodies (`Id "_"))) *)
                     (*        !depth; *)
                     (* print_newline () *)
                    );
       Int.incr depth;
     done;
     failwith "Exited solve loop without finding a solution.")
