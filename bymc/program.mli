(*
  Convenient representation of an (extended) Promela program to simplify
  analysis and transformation passes.

  Igor Konnov, 2012
 *)

open SpinIr

module StringMap: Map.S with type key = string

(* a program under analysis and transformation.  *)

type program

type expr_t = Spin.token expr

val program_of_units: Spin.token prog_unit list -> program
val units_of_program: program -> Spin.token prog_unit list
val empty: program

val get_params: program -> var list
val set_params: var list -> program -> program

(* shared variables *)
val get_shared: program -> var list
val set_shared: var list -> program -> program

(* instrumental variables added by the abstractions,
   not part of the original problem *)
val get_instrumental: program -> var list
val set_instrumental: var list -> program -> program

val get_assumes: program -> expr_t list
val set_assumes: expr_t list -> program -> program

val get_unsafes: program -> string list
val set_unsafes: string list -> program -> program

val get_procs: program -> (Spin.token proc) list
val set_procs: (Spin.token proc) list -> program -> program

val get_atomics: program -> (Spin.token atomic_expr) StringMap.t
val set_atomics: (Spin.token atomic_expr) StringMap.t -> program -> program

val get_ltl_forms: program -> (expr_t) StringMap.t
val get_ltl_forms_as_hash: program -> (string, expr_t) Hashtbl.t
val set_ltl_forms: (expr_t) StringMap.t -> program -> program

val is_global: program -> var -> bool
val is_not_global: program -> var -> bool

val run_smt_solver: program -> Smt.yices_smt

