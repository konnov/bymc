(*
The internal state of the spin parser -- use with care and as little as possible.
As ocamlyacc exports nothing but the start non-terminals, we keep the global
state in this module.
 *)

open SpinIr

exception Not_implemented of string
exception Parse_error of string
exception State_error of string

type spin_parser_state_t

(* this make the module non-reentrant, as the current state is globally kept *)
val get_state: unit -> spin_parser_state_t
val reset_state: unit -> unit

val err_cnt: spin_parser_state_t -> int
val inc_err_cnt: spin_parser_state_t -> spin_parser_state_t

val global_scope: spin_parser_state_t -> symb_tab
val spec_scope: spin_parser_state_t -> symb_tab

val top_scope: spin_parser_state_t -> symb_tab
val push_scope: spin_parser_state_t -> symb_tab -> spin_parser_state_t
val pop_scope: spin_parser_state_t -> spin_parser_state_t

val type_tab: spin_parser_state_t -> data_type_tab

