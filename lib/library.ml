open Core
open Infer
module SMap = String.Map

type t =
  { exprs: (string * Expr.t) list
  ; expr_ctx: Expr.t SMap.t
  ; value_ctx: Value.t SMap.t
  ; exprvalue_ctx: ExprValue.t SMap.t
  ; type_ctx: Type.t SMap.t
  ; builtins: Expr.Op.t list }

let empty =
  { exprs= []
  ; expr_ctx= SMap.empty
  ; value_ctx= SMap.empty
  ; exprvalue_ctx= SMap.empty
  ; type_ctx= SMap.empty
  ; builtins= [] }

let from_channel_exn : file:string -> In_channel.t -> t =
 fun ~file ch ->
  let exprs_and_builtins =
    let lexbuf = Lexing.from_channel ch in
    try Parser_ml.toplevel_ml_eof Lexer_ml.token lexbuf with
    | Parser_ml.Error | Parsing.Parse_error ->
        let err =
          let open Lexing in
          let pos = lexbuf.lex_curr_p in
          sprintf "Syntax error in library file '%s'. (line: %d, col: %d)"
            pos.pos_fname pos.pos_lnum (pos.pos_cnum - pos.pos_bol)
        in
        failwith err
    | Lexer_ml.SyntaxError err ->
        Error.failwiths "Parsing failed." (file, err) [%sexp_of: string * string]
  in
  let exprs, builtins =
    List.partition_map exprs_and_builtins ~f:(function
      | `Bind b -> `Fst b
      | `Builtin bs -> `Snd bs )
  in
  let builtins = List.concat builtins in
  let expr_ctx =
    List.fold_left exprs ~init:SMap.empty ~f:(fun m (n, e) ->
        SMap.set m ~key:n ~data:e )
  in
  let value_ctx =
    List.fold_left exprs ~init:SMap.empty ~f:(fun ctx (name, expr) ->
        let ctx_ref = ref ctx in
        let value = Eval.eval ctx_ref (`Let (name, expr, `Id name)) in
        SMap.set !ctx_ref ~key:name ~data:value )
  in
  let exprvalue_ctx =
    List.fold_left exprs ~init:SMap.empty ~f:(fun ctx (name, expr) ->
        let ctx_ref = ref ctx in
        let value =
          Eval.partial_eval ~ctx:ctx_ref
            (`Let (name, ExprValue.of_expr expr, `Id name))
        in
        SMap.set !ctx_ref ~key:name ~data:value )
  in
  let type_ctx =
    List.fold_left exprs ~init:SMap.empty ~f:(fun ctx (name, expr) ->
        let type_ =
          try
            let t, _ = Type.of_expr ~ctx (`Let (name, expr, `Id name)) in
            generalize (-1) t |> normalize
          with TypeError err -> Error.raise err
        in
        SMap.set ctx ~key:name ~data:type_ )
  in
  {exprs; expr_ctx; value_ctx; exprvalue_ctx; type_ctx; builtins}

let from_channel : file:string -> In_channel.t -> t Or_error.t =
 fun ~file ch -> Or_error.try_with (fun () -> from_channel_exn ~file ch)

let from_file_exn : string -> t =
 fun fn -> In_channel.with_file fn ~f:(from_channel_exn ~file:fn)

let from_file : string -> t Or_error.t =
 fun fn -> Or_error.try_with (fun () -> from_file_exn fn)

let filter_keys : t -> f:(string -> bool) -> t =
 fun t ~f ->
  { t with
    exprs= List.filter ~f:(fun (name, _) -> f name) t.exprs
  ; expr_ctx= Map.filter_keys t.expr_ctx ~f
  ; value_ctx= Map.filter_keys t.value_ctx ~f
  ; exprvalue_ctx= Map.filter_keys t.exprvalue_ctx ~f
  ; type_ctx= Map.filter_keys t.type_ctx ~f }
