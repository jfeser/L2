open Core.Std
module Json = Yojson.Safe

type case =
  | Examples of Example.t list * ((string * Expr.t) list)

type t = {
  name : string;
  desc : string;
  case : case;
}

let json_error str json = Or_error.error str (Json.pretty_to_string json) <:sexp_of<string>>

let examples_of_json j =
  let open Or_error.Monad_infix in
  match j with
  | `Assoc [
      "examples", `List exs_json;
      "background", `List bg_json;
    ] ->
    let exs = List.map exs_json ~f:(function
        | `String ex_str -> Example.of_string ex_str
        | ex_json -> json_error "Malformed example." ex_json)
              |> Or_error.combine_errors
    in
    let bg = List.map bg_json ~f:(function
        | `List [`String name; `String bg_str] -> Expr.of_string bg_str >>| fun bg -> (name, bg)
        | ex_json -> json_error "Malformed background." ex_json)
             |> Or_error.combine_errors
    in
    exs >>= fun exs ->
    bg >>| fun bg ->
    Examples (exs, bg)
  | _ -> json_error "Contents are malformed for kind 'examples'." j

let of_json j =
  let open Or_error.Monad_infix in
  match j with
  | `Assoc [
      "name", `String name;
      "description", `String desc;
      "kind", `String kind;
      "contents", contents;
    ] -> begin match kind with
      | "examples" -> examples_of_json contents >>| fun case -> { name; desc; case; }
      | _ -> error "Unexpected kind." (kind, Json.pretty_to_string j) <:sexp_of<string * string>>
    end
  | j -> json_error "Test case is malformed." j

let from_file ~filename:fn =
  try Json.from_file ~fname:fn fn |> of_json with
  | Yojson.Json_error err -> Or_error.error_string err

let to_json t =
  let rest = match t.case with
    | Examples (exs, bgs) -> [
        "kind", `String "examples";
        "contents", `Assoc [
          "examples", `List (List.map exs ~f:(fun ex -> `String (Example.to_string ex)));
          "background", `List (List.map bgs ~f:(fun (name, expr) ->
              `List [`String name; `String (Expr.to_string expr)]));
        ];
      ]
  in
  `Assoc ([
    "name", `String t.name;
    "description", `String t.desc;
  ] @ rest)

let to_file ~format:fmt ~filename:fn t =
  let json = to_json t in
  let ch = Out_channel.create fn in
  try
    match fmt with
    | `Pretty -> Ok (Json.pretty_to_channel ~std:true ch json)
    | `Compact -> Ok (Json.to_channel ~std:true ch json)
  with
  | Yojson.Json_error err -> Or_error.error_string err
    
let from_channel ch =
  try Json.from_channel ch |> of_json with
  | Yojson.Json_error err -> Or_error.error_string err
  
