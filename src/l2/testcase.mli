open Core.Std
module Json = Yojson.Safe

type case =
  | Examples of Example.t list * ((string * Expr.t) list)

type t = {
  name : string;
  desc : string;
  case : case;
}

val of_json : Json.json -> t Or_error.t
val to_json : t -> Json.json
val from_file : filename:string -> t Or_error.t
val to_file : format:[ `Pretty | `Compact ] -> filename:string -> t -> unit Or_error.t
val from_channel : In_channel.t -> t Or_error.t
