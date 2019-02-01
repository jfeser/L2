open Core

type t =
  { verbosity: int [@default 0] [@sexp_drop_default]
  ; untyped: bool [@default false] [@sexp_drop_default]
  ; deduction: bool [@default true] [@sexp_drop_default]
  ; infer_base: bool [@default true] [@sexp_drop_default]
  ; use_solver: bool [@default false] [@sexp_drop_default]
  ; max_exhaustive_depth: int [@default 7] [@sexp_drop_default]
  ; check_prob: float
  ; flat_cost: bool [@default false] [@sexp_drop_default] }
[@@deriving sexp]

let default =
  { verbosity= 0
  ; untyped= false
  ; deduction= true
  ; infer_base= true
  ; use_solver= false
  ; max_exhaustive_depth= 7
  ; check_prob= 1.5
  ; flat_cost= false }

let of_string (s : string) : t = t_of_sexp (Sexp.of_string (String.strip s))

let to_string (c : t) : string = Sexp.to_string_hum (sexp_of_t c)

let config = ref default
