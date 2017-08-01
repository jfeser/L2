open Core

(** Custom collections. *)

module Json = struct
  include Yojson.Safe

  let sexp_of_json j = to_string j |> [%sexp_of:string]
end
