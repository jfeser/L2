open Core.Std
open Printf

open Ast
open Infer
open Structure
open Util

let rec enumerate ?(ops=Expr.Op.all) 
                  ?(memo=Sstream.Memoizer.empty ()) 
                  init 
                  typ 
        : typed_expr Sstream.matrix =
  let open Sstream in
  let arrow_error () = failwith "Operator is not of type Arrow_t." in

  (* printf "enumerate %s %s.\n" *)
  (*        (List.to_string init ~f:(fun e -> Expr.to_string (expr_of_texpr e))) *)
  (*        (typ_to_string typ); *)

  (* Init is finite, so we can construct an init stream by breaking
  init into a list of size classes and returning that list as a
  stream. *)
  let (init_matrix: typed_expr matrix) =
    let init_sizes =
      List.filter init ~f:(fun e -> is_unifiable typ (typ_of_expr e))
      |> List.map ~f:(fun e -> e, Expr.size (expr_of_texpr e))
    in
    let max_size = List.fold_left init_sizes ~init:0 ~f:(fun x (_, y) -> if x > y then x else y) in
    List.range ~stop:`inclusive 1 max_size
    |> List.map ~f:(fun s -> List.filter_map init_sizes ~f:(fun (e, s') -> if s = s' then Some e else None))
    |> of_list
  in

  (* Generate an argument list matrix that conforms to the provided list of types. *)
  let args_matrix (arg_typs: typ list) =
    let choose (prev_args: typed_expr list) : (typed_expr list) matrix =
      (* Split the argument type list into the types of the arguments
      that have already been selected and the head of the list of
      remaining types (which will be the type of the current
      argument). *)
      let prev_arg_typs, (current_typ::_) =
        (* Instantiate the argument types in the same context. Free
        type variables should be shared across arguments. For example,
        when instantiating the argument types for equals: (a, a) ->
        bool, both a's should map to the same free type. *)
        let arg_typs' =
          let ctx = Ctx.empty () in
          List.map arg_typs ~f:(instantiate ~ctx:ctx 0)
        in
        List.split_n arg_typs' (List.length prev_args)
      in

      (* Unify the types of the previous arguments with the actual
      selected types. By the size effects of unify, this should fill
      in any type variables in the current type that have already been
      bound. *)
      let prev_selected_typs =
        let ctx = Ctx.empty () in
        List.map prev_args ~f:(fun arg -> instantiate ~ctx:ctx 0 (typ_of_expr arg))
      in
      List.iter2_exn prev_arg_typs prev_selected_typs ~f:unify_exn;

      let current_typ' = normalize (generalize (-1) current_typ) in

      (* Generate the argument matrix lazily so that it will not be
         created until the prefix classes are exhausted. *)
      slazy (fun () -> 
             map_matrix (Memoizer.get memo current_typ' 
                                      (fun () -> enumerate ~memo:memo init current_typ'))
                        ~f:(fun arg -> prev_args @ [arg]))
    in
    match arg_typs with
    | _::xs -> (List.fold_left xs ~init:choose ~f:(fun acc _ -> compose acc choose)) []
    | [] -> failwith "Cannot generate args matrix with no arguments."
  in

  let callable_matrix apply_callable callable_typ = match callable_typ with
    | Arrow_t (arg_typs, ret_typ) ->
       let prefix = repeat_n (List.length arg_typs) [] in
       let matrix = slazy (fun () -> map_matrix (args_matrix arg_typs) ~f:(apply_callable ret_typ)) in
       concat prefix matrix
    | _ -> arrow_error ()
  in
  let op_matrix op op_typ =
    callable_matrix (fun ret_typ args -> Op ((op, args), ret_typ)) op_typ
  in
  let apply_matrix func func_typ =
    callable_matrix (fun ret_typ args -> Apply ((func, args), ret_typ)) func_typ
  in

  (* The op stream is infinite, so it needs more careful handling. *)
  let op_matrices =
    List.map ops ~f:(fun op -> op, Expr.Op.meta op)
    (* Filter all operators that can return the correct type. *)
    |> List.filter ~f:(fun (_, meta) ->
                       match meta.Expr.Op.typ with
                       | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
                       | _ -> arrow_error ())

    (* Unify the return type of the operator with the input type. By
    the side effects of unify, all the other free type variables in
    the operator type will reflect the substitution. Now we have
    correct types for the arguments. *)
    |> List.map ~f:(fun (op, meta) ->
                    match instantiate 0 typ, instantiate 0 meta.Expr.Op.typ with
                    | typ', (Arrow_t (_, ret_typ) as op_typ) ->
                       unify_exn typ' ret_typ;
                       op, normalize (generalize (-1) op_typ)
                    | _ -> arrow_error ())

    (* Generate a matrix for each operator. *)
    |> List.map ~f:(fun (op, op_typ) -> op_matrix op op_typ)
  in

  let apply_matrices =
    init
    |> List.filter ~f:(fun texpr -> 
                       match typ_of_expr texpr with
                       | Arrow_t (_, ret_typ) -> is_unifiable typ ret_typ
                       | _ -> false)
    |> List.map ~f:(fun texpr ->
                    match instantiate 0 typ, instantiate 0 (typ_of_expr texpr) with
                    | typ', (Arrow_t (_, ret_typ) as func_typ) ->
                       unify_exn typ' ret_typ;
                       texpr, normalize (generalize (-1) func_typ)
                    | _ -> arrow_error ())
    |> List.map ~f:(fun (func, func_typ) -> apply_matrix func func_typ)
  in
  merge (init_matrix::(op_matrices @ apply_matrices))
  |> map ~f:(List.filter ~f:(fun x ->
                             let e = expr_of_texpr x in
                             match Rewrite.rewrite e with
                             | Some e' -> e = e'
                             | None -> false))
  (* |> map ~f:(List.map ~f:(fun e -> print_endline (Expr.to_string (expr_of_texpr e)); e)) *)

let solve_single ?(init=[])
                 ?(verify=Verify.verify_examples ~ctx:(Ctx.empty ()))
                 (examples: example list) =
  let initial_spec =
    let target_name = Example.name examples in
    let target ctx expr =
      let body = Ctx.lookup_exn ctx target_name in
      `Let (target_name, body, expr)
    in
    { Spec.target;
      Spec.holes =
        Ctx.of_alist_exn [
                  target_name, 
                  { examples = List.map examples ~f:(fun ex -> ex, Ctx.empty ());
              signature = Example.signature examples;
                    tctx = Ctx.empty ();
                    depth = 2;
                  };
                ];
    }
  in

  let rec generate_specs (specs: Spec.t list) : Spec.t list =
    match specs with
    | [] -> []
    | specs ->
       let child_specs = List.concat_map specs
                                         ~f:(fun parent ->
                                             (Spec.map_bodies parent)
                                             @ (Spec.filter_bodies parent)
                                             @ (Spec.fold_bodies parent)
                                             @ (Spec.foldt_bodies parent)
                                             @ (Spec.recurs_bodies parent)
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
        (* printf "%s\n" (Expr.to_string (spec.target hole_bodies (`Id "_"))); *)
  (*       Ctx.to_alist spec.holes *)
  (*       |> List.iter ~f:(fun (name, hole) -> *)
  (*                        printf "\t%s: %s\n" name (typ_to_string hole.signature); *)
  (*                        List.iter hole.examples ~f:(fun (ex, _) -> printf "\t\t%s\n" (Expr.example_to_string ex)))); *)
  (* print_newline (); *)

  let matrix_of_hole hole =
    let init' =
      (Ctx.to_alist hole.tctx |> List.map ~f:(fun (name, typ) -> Id (name, typ))) @ init
    in
    match hole.signature with
    | Arrow_t (arg_typs, ret_typ) ->
       let args = List.map arg_typs ~f:(fun typ -> Fresh.name "x", typ) in
       let arg_names, _ = List.unzip args in
       let init'' = init' @ (List.map args ~f:(fun (name, typ) -> Id (name, typ))) in
       enumerate init'' ret_typ 
       |> Sstream.map_matrix ~f:(fun texpr -> 
                                (* printf "%s %s\n"  *)
                                (*        (typ_to_string hole.signature)  *)
                                (*        (Expr.to_string (expr_of_texpr texpr)); *)
                                `Lambda (arg_names, expr_of_texpr texpr))
    | typ -> enumerate init' typ 
             |> Sstream.map_matrix ~f:(fun tx -> 
                                      (* printf "%s %s\n"  *)
                                      (*        (typ_to_string hole.signature)  *)
                                      (*        (Expr.to_string (expr_of_texpr tx)); *)
                                      (expr_of_texpr tx))
  in

  let choose name hole ctx : (expr Ctx.t) Sstream.matrix =
    Sstream.map_matrix (matrix_of_hole hole) ~f:(Ctx.bind ctx name)
  in

  let solver_of_spec spec =
    let ctx_matrix = match Ctx.to_alist spec.Spec.holes with
      | [] -> failwith "Specification has no holes."
      | (name, hole)::hs ->
         (List.fold_left hs
                        ~init:(choose name hole)
                        ~f:(fun matrix (name', hole') -> Sstream.compose matrix (choose name' hole')))
           (Ctx.empty ())
    in
    ctx_matrix
    |> Sstream.map_matrix ~f:(fun ctx -> 
                             let target = spec.target ctx in
                             (* print_endline (Expr.to_string (target (`Id "_"))); *)
                             if verify target examples
                             then Some target else None)
  in

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
                     (*        (Expr.to_string (spec.target hole_bodies (`Id "_"))) *)
                     (*        !depth; *)
                     (* print_newline () *)
                    );
       Int.incr depth;
     done;
     failwith "Exited solve loop without finding a solution.")

let default_init = ["0"; "1"; "[]"; "#f";] |> List.map ~f:parse_expr

let solve ?(init=default_init) (examples: example list) : expr Ctx.t =
  (* Split examples into separate functions. *)
  let func_examples = Example.split examples in

  (* Check that each set of examples represents a function. *)
  if List.for_all func_examples
                  ~f:(fun (_, exs) ->
                      let exs' = List.map exs ~f:(fun ex -> ex, Ctx.empty ()) in
                      Example.check exs')
  then
    let ectx, _, _, _ =
      List.fold_left
        func_examples
        ~init:(Ctx.empty (), 
               Eval.stdlib_vctx,
               Ctx.empty (), 
               List.map init ~f:(infer (Ctx.empty ())))
        ~f:(fun (ectx, vctx, tctx, init) (name, exs) ->
            let verify = Verify.verify_examples ~ctx:vctx in
            let result = (solve_single ~init:init ~verify:verify exs) (`Id "_") in
            (* printf "Solved %s: %s\n" name (Expr.to_string result); *)
            match result with
            | `Let (_, body, _) ->
               let ectx' = Ctx.bind ectx name body in
               let vctx' =
                 let vctx'' = Ctx.bind vctx name `Unit in
                 let value = `Closure (body, vctx'') in
                 Ctx.update vctx'' name value; vctx''
               in
               let typ = typ_of_expr (infer (Ctx.bind tctx name (fresh_free 0)) body) in
               let tctx' = Ctx.bind tctx name typ in
               let init' = (Id (name, typ))::init in
               ectx', vctx', tctx', init'
            | _ -> failwith (sprintf "Bad result from solve_single %s" (Expr.to_string result)))
    in ectx
  else failwith "Some example group does not represent a function."
