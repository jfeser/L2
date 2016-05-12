open Core.Std

open Infer

module SMap = String.Map

type t = {
  expr_ctx : Expr.t SMap.t;
  value_ctx : Value.t SMap.t;
  exprvalue_ctx : ExprValue.t SMap.t;
  type_ctx : Type.t SMap.t;
}

let empty = {
  expr_ctx = SMap.empty;
  value_ctx = SMap.empty;
  exprvalue_ctx = SMap.empty;
  type_ctx = SMap.empty;
}

let from_channel_exn : file:string -> In_channel.t -> t = fun ~file ch ->
  let exprs =
    let lexbuf = Lexing.from_channel ch in
    try Parser.toplevel_ml_eof Lexer.token lexbuf with
    | Parser.Error
    | Parsing.Parse_error ->
      Error.failwiths "Parsing failed." file [%sexp_of:string]
    | Lexer.SyntaxError err ->
      Error.failwiths "Parsing failed." (file, err) [%sexp_of:string * string]
  in

  let expr_ctx = SMap.of_alist_exn exprs in
  
  let value_ctx = List.fold_left exprs ~init:SMap.empty ~f:(fun ctx (name, expr) ->
      let ctx_ref = ref ctx in
      let value = Eval.eval ctx_ref (`Let (name, expr, `Id name)) in
      SMap.add !ctx_ref ~key:name ~data:value)
  in
  
  let exprvalue_ctx = List.fold_left exprs ~init:SMap.empty ~f:(fun ctx (name, expr) ->
      let ctx_ref = ref ctx in
      let value = Eval.partial_eval ~ctx:ctx_ref (`Let (name, (ExprValue.of_expr expr), `Id name)) in
      SMap.add !ctx_ref ~key:name ~data:value)
  in

  let type_ctx = List.fold_left exprs ~init:SMap.empty ~f:(fun ctx (name, expr) ->
      let type_ =
        try
          let t, u = Type.of_expr ~ctx (`Let (name, expr, `Id name)) in
          generalize (-1) t |> normalize
        with TypeError err -> Error.raise err
      in
      SMap.add ctx ~key:name ~data:type_)
  in
  { expr_ctx; value_ctx; exprvalue_ctx; type_ctx }

let from_channel : file:string -> In_channel.t -> t Or_error.t = fun ~file ch ->
  Or_error.try_with (fun () -> from_channel_exn ~file ch)

let from_file_exn : string -> t = fun fn ->
  In_channel.with_file fn ~f:(from_channel_exn ~file:fn)

let from_file : string -> t Or_error.t = fun fn ->
  Or_error.try_with (fun () -> from_file_exn fn)
