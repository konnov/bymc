(** Symbolic skeleton (aka threshold automaton) and functions
   to manipulate it.

   @author Igor Konnov, 2014
 *)

module Sk: sig
    (** a location (node) *)
    type loc_t = int list (* variable assignments *)

    (** a rule (edge) *)
    type rule_t = {
        src: int; (** a source location (index in skel_t.locs) *)
        dst: int; (** a destination location (index in skel_t.locs) *)
        guard: Spin.token SpinIr.expr; (** a guard expression *)
        act: Spin.token SpinIr.expr list;
            (** an action expression, includes NEXT var *)
    }

    type skel_t = {
        name: string; (** just a name, e.g., the process type *)
        nlocs: int; (** the number of locations *)
        locs: loc_t list; (** the list of locations *)
        locals: SpinIr.var list; (** local variables *)
        shared: SpinIr.var list; (** shared variables *)
        params: SpinIr.var list; (** parameters *)
        nrules: int; (** the number of rules *)
        rules: rule_t list; (** the rules *)
        inits: Spin.token SpinIr.expr list; (** initialization expressions *)
        loc_vars: SpinIr.var Accums.IntMap.t;
            (** variables that correspond to locations,
               e.g., used in the initialization part *)
    }

    (** construct an empty skeleton *)
    val empty: SpinIr.var list -> SpinIr.var list -> SpinIr.var list
        -> skel_t

    (** get location by its number in skel_t.locs *)
    val loc_by_no: skel_t -> int -> loc_t

    (** get location name *)
    val locname: loc_t -> string

    (** get the counter assigned to a location *)
    val locvar: skel_t -> int -> SpinIr.var

    (** save skeleton to a file *)
    val to_file: string -> skel_t -> unit

    val print: out_channel -> skel_t -> unit
end


module SkB: sig
    (** the skeleton under construction *)
    type state_t

    (** context for a function that constructs locations and rules *)
    type context_t = {
        sym_tab: SpinIr.symb_tab;
        type_tab: SpinIr.data_type_tab;
        prev_next: (SpinIr.var * SpinIr.var) list;
        state: state_t ref;
    }

    (**
     Create an initial builder state.
     @param locals local variables
     @param shared shared variables
     @param params parameter variables
     @return initial builder state
     *)
    val empty: SpinIr.var list -> SpinIr.var list -> SpinIr.var list -> state_t

    (**
     Finish skeleton construction and return the complete skeleton.
     @param state builder state
     @param name skeleton name
     @return a complete skeleton
     *)
    val finish: state_t -> string -> Sk.skel_t

    (* get location index or allocate a new one *)
    val get_loci: state_t -> Sk.loc_t -> int

    val intro_loc_vars: state_t ref -> SpinIr.data_type_tab -> SpinIr.var list

    val add_loc: state_t ref -> Sk.loc_t -> int

    val get_nlocs: state_t ref -> int

    val add_rule: state_t ref -> Sk.rule_t -> int

    val add_init: state_t ref -> Spin.token SpinIr.expr -> unit
end


type builder_fun_t =
    SkB.context_t -> Spin.token SpinIr.expr
        -> (string, Spin.token SpinIr.expr) Hashtbl.t -> unit


val build_with:
    (** @param builder_fun a function that constructs locations and rules *)
    builder_fun_t
    (** @param rt runtime *)
    -> Runtime.runtime_t
    (** @param prog input program *)
    -> Program.program_t
    (** @param proc input process *)
    -> Spin.token SpinIr.proc
    (** @return the skeleton and the modified program *)
    -> Sk.skel_t * Program.program_t


(** Construct a symbolic skeleton given the transitions represented
   as (prev, next) pairs. This representation usually comes from
   an abstraction.
 *)
val state_pairs_to_rules:
    (** @param rt runtime *)
    Runtime.runtime_t
    (** @param prog input program *)
    -> Program.program_t 
    (** @param proc the original process *)
    -> Spin.token SpinIr.proc
    (** @param trs transitions as pairs of assignments
        to the previous and next locations *)
    -> ((SpinIr.var * int) list * (SpinIr.var * int) list) list
    (** @return the skeleton and the modified program *)
    -> Sk.skel_t * Program.program_t


(** Transform a program specifications into specification over
    the skeletons' counters.
  *)
val expand_props_in_ltl:
    Program.program_t    (** @param prog input program *)
    -> Sk.skel_t list (** @param skels input skeletons *)
    -> Spin.token SpinIr.expr
        (** @param LTL formula to expand *)
    -> Spin.token SpinIr.expr
        (* @result LTL formula with conditions over locations (counters) *)


(** Transform program specifications into specifications over
    the skeletons' counters.
  *)
val expand_props_in_ltl_forms:
    Program.program_t    (** @param prog input program *)
    -> Sk.skel_t list (** @param skels input skeletons *)
    -> (Spin.token SpinIr.expr) Accums.StrMap.t
        (** @param LTL formulas to expand *)
    -> (Spin.token SpinIr.expr) Accums.StrMap.t
        (* @result LTL formulas with conditions over locations (counters) *)

