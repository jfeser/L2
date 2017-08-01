open Core
open Collections

exception JsonDecodeError of { msg : string; json : Json.json }

type case =
  | Examples of Example.t list * ((string * Expr.t) list)

type t = {
  name : string;
  desc : string;
  case : case;
  blacklist : string list;
}

let json_error str json = raise (JsonDecodeError { msg = str; json })

let get_key_exn : ?default:Json.json -> Json.json -> string -> Json.json =
  fun ?default json key ->
    match json with
    | `Assoc kv ->
      begin match List.Assoc.find ~equal:(=) kv key, default with
        | Some v, _ | None, Some v -> v
        | None, None -> json_error (sprintf "Could not find key: %s" key) json
      end
    | _ -> json_error "Expected an object." json

let as_list_exn : Json.json -> Json.json list =
  function
  | `List l -> l
  | j -> json_error "Expected a list." j

let as_string_exn : Json.json -> string =
  function
  | `String s -> s
  | j -> json_error "Expected a string." j

let examples_of_json j =
  let exs_json = get_key_exn j "examples" in
  let bg_json = get_key_exn j "background" ~default:(`List []) in
  let exs =
    exs_json
    |> as_list_exn
    |> List.map ~f:as_string_exn
    |> List.map ~f:Example.of_string_exn
  in
  let bg =
    bg_json
    |> as_list_exn
    |> List.map ~f:(fun pair_json ->
        match as_list_exn pair_json with
        | [name_json; expr_json] ->
          (as_string_exn name_json, as_string_exn expr_json |> Expr.of_string_exn)
        | _ -> json_error "Expected name, expression pairs." pair_json)
  in
  Examples (exs, bg)

let of_json j =
  let open Json.Util in
  Or_error.try_with (fun () -> {
        name = j |> member "name" |> to_string;
        desc = get_key_exn j "description" ~default:(`String "") |> as_string_exn;
        blacklist =
          get_key_exn j "blacklist" ~default:(`List [])
          |> as_list_exn
          |> List.map ~f:as_string_exn;
        case = begin
          match j |> member "kind" |> to_string with
          | "examples" -> j |> member "contents" |> examples_of_json
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

let to_file ?format:(fmt = `Pretty) ~filename:fn t =
  let json = to_json t in
  Out_channel.with_file fn ~f:(fun ch ->
      try
        match fmt with
        | `Pretty -> Ok (Json.pretty_to_channel ~std:true ch json)
        | `Compact -> Ok (Json.to_channel ~std:true ch json)
      with
      | Yojson.Json_error err -> Or_error.error_string err)

let to_file_exn ?format:(fmt = `Pretty) ~filename:fn t =
  to_file ~format:fmt ~filename:fn t |> Or_error.ok_exn

let from_channel ch =
  try Json.from_channel ch |> of_json with
  | Yojson.Json_error err -> Or_error.error_string err
