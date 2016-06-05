open Core.Std
open Collections

type case =
  | Examples of Example.t list * ((string * Expr.t) list)

type t = {
  name : string;
  desc : string;
  case : case;
  blacklist : string list;
}

let json_error str json = Or_error.error str (Json.pretty_to_string json) [%sexp_of:string]

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
  let open Json.Util in
  Or_error.try_with (fun () -> {
        name = j |> member "name" |> to_string;
        desc = j |> member "description" |> to_string;
        blacklist = begin
          match j |> member "blacklist" with
          | `Null -> []
          | bj -> bj |> to_list |> List.map ~f:to_string
        end;
        case = begin
          match j |> member "kind" |> to_string with
          | "examples" -> j |> member "contents" |> examples_of_json |> ok_exn
          | kind -> failwiths "Unexpected kind." kind [%sexp_of:string]
        end;
      })

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
    "blacklist", `List (List.map t.blacklist ~f:(fun x -> `String x));
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
  
