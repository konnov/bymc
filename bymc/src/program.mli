(*
  Convenient representation of an (extended) Promela program to simplify
  analysis and transformation passes.

  Igor Konnov, 2012
 *)

open SpinIr

module StringMap: Map.S with type key = string

(* a program under analysis and transformation.  *)

type program_t

type expr_t = Spin.token expr
type path_t = expr_t list list

val program_of_units: data_type_tab -> Spin.token prog_unit list -> program_t
val units_of_program: program_t -> Spin.token prog_unit list
val empty: program_t

val get_params: program_t -> var list
val set_params: var list -> program_t -> program_t

(* shared (global) variables *)
val get_shared: program_t -> var list
(* @deprecated this function sets initialization expression to NOP *)
val set_shared: var list -> program_t -> program_t

(* shared variables with the initialization expressions *)
val get_shared_with_init: program_t -> (var * expr_t) list
val set_shared_with_init: (var * expr_t) list -> program_t -> program_t

(* extract all local variables declared in processes (may be slow!) *)
val get_all_locals: program_t -> var list

(* get the datatype of a variable (or Program_error if no such variable) *)
val get_type: program_t -> var -> data_type

(* get/set data type table *)
val get_type_tab: program_t -> data_type_tab
val set_type_tab: data_type_tab -> program_t -> program_t

(* get the main symbols table *)
val get_sym_tab: program_t -> symb_tab

(* global instrumental variables added by the abstractions,
   not part of the original problem *)
val get_instrumental: program_t -> var list
val set_instrumental: var list -> program_t -> program_t

val get_assumes: program_t -> expr_t list
val set_assumes: expr_t list -> program_t -> program_t

val get_unsafes: program_t -> string list
val set_unsafes: string list -> program_t -> program_t

val get_procs: program_t -> (Spin.token proc) list
val set_procs: (Spin.token proc) list -> program_t -> program_t

val get_atomics: program_t -> (Spin.token atomic_expr) StringMap.t
val set_atomics: (Spin.token atomic_expr) StringMap.t -> program_t -> program_t

val get_ltl_forms: program_t -> (expr_t) StringMap.t
val get_ltl_forms_as_hash: program_t -> (string, expr_t) Hashtbl.t
val set_ltl_forms: (expr_t) StringMap.t -> program_t -> program_t

val is_global: program_t -> var -> bool
val is_not_global: program_t -> var -> bool

val run_smt_solver: program_t -> Smt.yices_smt


