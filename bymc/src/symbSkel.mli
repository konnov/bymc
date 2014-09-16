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
 
end


(** Construct a symbolic skeleton given the transitions represented
   as (prev, next) pairs. This representation usually comes from
   an abstraction.
 *)
val collect_constraints:
    (** @param rt runtime *)
    Runtime.runtime_t
    (** @param prog input program *)
    -> Program.program_t 
    (** @param proc the original process *)
    -> Spin.token SpinIr.proc
    (** @param primary_vars the local variables *)
    -> SpinIr.var list
    (** @param trs transitions as pairs of assignments
        to the previous and next locations *)
    -> ((SpinIr.var * int) list * (SpinIr.var * int) list) list
    (** @return the skeleton and the modified program *)
    -> Sk.skel_t * Program.program_t

