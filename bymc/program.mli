(*
  Convenient representation of an (extended) Promela program to simplify
  analysis and transformation passes.

  Igor Konnov, 2012
 *)

open SpinIr

module StringMap: Map.S with type key = string

(* a program under analysis and transformation.  *)

type program

val program_of_units: Spin.token prog_unit list -> program
val empty_program: program

val get_params: program -> var list
val set_params: program -> var list -> program

val get_shared: program -> var list
val set_shared: program -> var list -> program

val get_assumes: program -> Spin.token expr list
val set_assumes: program -> Spin.token expr list -> program

val get_procs: program -> (Spin.token proc) list
val set_procs: program -> (Spin.token proc) list -> program

val get_atomics: program -> (Spin.token atomic_expr) StringMap.t
val set_atomics: program -> (Spin.token atomic_expr) StringMap.t -> program

val get_ltl_forms: program -> (Spin.token expr) StringMap.t
val set_ltl_forms: program -> (Spin.token expr) StringMap.t -> program

