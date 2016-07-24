open Core.Std
open Synthesis_common

let drop_prob = 0.05

let push_specs sk =
  if Random.float 1.0 <= drop_prob then None else Some sk
  
