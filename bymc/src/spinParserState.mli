(*
The internal state of the spin parser -- use with care and as little as possible.
As ocamlyacc exports nothing but the start non-terminals, we keep the global
state in this module.
 *)

open SpinIr

exception Not_implemented of string
exception Parse_error of string
exception State_error of string
exception Promela_semantic_err of string

type spin_parser_state_t

(* this make the module non-reentrant, as the current state is globally kept *)
val get_state: unit -> spin_parser_state_t
val reset_state: unit -> unit

val err_cnt: unit -> int
val inc_err_cnt: unit -> unit

val global_scope: unit -> symb_tab
val spec_scope: unit -> symb_tab

val top_scope: unit -> symb_tab
val push_scope: symb_tab -> unit
val pop_scope: unit -> unit

val type_tab: unit -> data_type_tab

