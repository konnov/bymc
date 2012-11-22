(*
  Convenient representation of an (extended) Promela program to simplify
  analysis and transformation passes.

  Igor Konnov, 2012
 *)

module StringMap = Map.Make (String)

(* a program under analysis and transformation.  *)

type program

let program_of_units: Spin.token prog_unit -> program
let empty_program: program

val get_params: program -> var list
val set_params: program -> var list -> program

val get_shared: program -> var list
val set_shared: program -> var list -> program

val get_assumes: program -> Spin.token expr list
val set_assumes: program -> Spin.token expr list -> program

val get_procs: program -> Spin.token proc StringMap
val set_procs: program -> Spin.token proc StringMap -> program

val get_atomics: program -> Spin.token expr StringMap
val set_atomics: program -> Spin.token expr StringMap -> program

val get_ltl_forms: program -> Spin.token expr StringMap
val set_ltl_forms: program -> Spin.token expr StringMap -> program

