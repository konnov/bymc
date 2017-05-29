(**
 A new implementation of a schema-based model checker that supports LTL(F, G)
 over counters and shared variables.

 Igor Konnov, 2016
 *)

(**
 This exception is thrown when an unsupported is used
 *)
exception IllegalLtl_error of string


(**
 The statistics collected during the execution.
 *)
type stat_t = {
    m_nschemas: int;  (** the number of inspected schemas *)
    m_min_schema_len: int;  (** the minimal schema length encountered *)
    m_max_schema_len: int;  (** the maximal schema length encountered *)
    m_sum_schema_len: int;  (** the sum of all schema lengths (for the average) *)
    m_min_schema_time_sec: float;  (** the minimal time to check a schema *)
    m_max_schema_time_sec: float;  (** the maximum time to check a schema *)
    m_sum_schema_time_sec: float;  (** the sum of all schema times (for the average) *)

    (* internal stats *)
    m_reachopt_sec: float;   (* the time spent with the reachability optimization on *)
    m_noreachopt_sec: float; (* the time spent with the reachability optimization off *)
    m_reachopt_rounds: int;    (* rounds spent with the reachability optimization on *)
    m_noreachopt_rounds: int;  (* rounds spent with the reachability optimization off *)
    m_nrounds_to_switch: int; (* the number of rounds left before trying to adapt   *)
    m_reachability_on: bool;  (* is the reachability optimization on *)
}

(**
 An iterator over schemas used in the search
 *)
module SchemaIter: sig
    type search_iter_t

    (** Is the end reached? *)
    val iter_is_end: search_iter_t -> bool

    (**
      Get the next iterator value.

      @param iter current value (see the note)
      @return the new iterator value

      NOTE: Use the returned iterator, and but note that this function
          corrupts its arguments (perhaps, not the best design).
     *)
    val iter_next: search_iter_t -> search_iter_t

    (**
      Is an error found at the found?

      @param iter a search iterator
      @return true, if an error was found
     *)
    val iter_is_err_found: search_iter_t -> bool

    (**
      Get the name of a counterexample, if an error is found.
      If no error found, throw an exception.

      @param iter a search iterator
      @return the found counterexample.
      *)
    val iter_get_cex: search_iter_t -> string

    (**
      Get the statistics collected until the iterator.

      @param iter a search iterator
      @return statistics
      *)
    val iter_get_stat: search_iter_t -> stat_t
end


(**
  The search structure. It can be used to control the schema enumeration.
  E.g., one can enumerate schemas for different formulas by interleaving,
  or distribute schema checking over multiple network nodes.
  *)
module S: sig
    (**
     This record type is used to control the search
     *)
    type search_t = {
        iter: SchemaIter.search_iter_t;
            (** the search iterator *)
        check_fun: SchemaIter.search_iter_t -> SchemaIter.search_iter_t;
            (** check the current schema *)
        dispose_search_fun: unit -> unit;
            (** call this function in the end of the search,
                e.g., stop the SMT solver *)
    }
end

(* 
  An internal result structure. Used by check_one_order.

  TODO: get rid of it, exposed for tests only.
 *)
type internal_result_t = { m_is_err: bool; m_schema_len: int; }

(**
 The type of atomic formulas supported by the model checker
 *)
type atomic_spec_t =
    | And_Keq0 of int list          (** /\_{i \in X} k_i = 0 *)
    | AndOr_Kne0 of int list list   (** /\_{X_j \in Y} \/_{i \in X_j} k_i \ne 0 *)
    | Shared_Or_And_Keq0 of Spin.token SpinIr.expr * int list
                                    (** f(g) \/ /\_{i \in X} k_i = 0 *)


(**
 LTL(F, G) formulas as supported by the model checker
 *)
type utl_k_spec_t =
    | TL_p of atomic_spec_t     (** a conjunction of atomic formulas *)
    | TL_F of utl_k_spec_t        (** F \phi *)
    | TL_G of utl_k_spec_t        (** G \phi *)
    | TL_and of utl_k_spec_t list (* a conjunction *)


(**
 A classification of temporal formulas
 *)
type spec_t =
    | Propositional of Spin.token SpinIr.expr
        (* a propositional constraint on the initial state: init_form *)
    | Safety of Spin.token SpinIr.expr * Spin.token SpinIr.expr
        (* a safety violation: init_form -> F bad_form *)
    | UTL of Spin.token SpinIr.expr * utl_k_spec_t
        (* an unrestricted propositional formula for the initial states
           and a UTL formula *)

(**
 The elements of the constructed partial order
 *)
type po_elem_t =
    | PO_init of utl_k_spec_t (** the initial state and the associated formulas *)
    | PO_loop_start of utl_k_spec_t (** the loop start point (with the invariants) *)
    | PO_guard of PSet.elt  (** an unlocking/locking guard *)
    | PO_tl of int (* id *) * utl_k_spec_t
        (** an extremal appearance of a temporal-logic formula *)


(* extract struc_of_utl_k_spec from utl_k_spec_t *)
val struc_of_po_elem:
    po_elem_t -> SchemaSmt.C.po_elem_struc_t

(** Create the initial statistics *)
val mk_stat: unit -> stat_t

(** Get the statistics as a string*)
val stat_s: stat_t -> string


(** Convert an atomic formula to a string *)
val atomic_spec_s: atomic_spec_t -> string


(** Convert a UTL formula to a string *)
val utl_spec_s: utl_k_spec_t -> string

(**
   This function enumerates all lassos of a single formula
   that can potentially form a counterexample.
 
   NOTE: this function creates multiple copies of the SMT solver.
 *)
val find_error_in_single_form:
    Runtime.runtime_t
        -> SpinIr.data_type_tab
        -> SymbSkel.Sk.skel_t -> string
        -> Spin.token SpinIr.expr
        -> PorBounds.D.deps_t
        -> SchemaIter.search_iter_t

(**
   This function is similar to find_error_in_single_form but it enumerates
   lassos for multiple formulas. The lassos that correspond to different
   formulas are interleaved, i.e., the ith lasso of the first formula is
   checked, then the ith lasso of the second formula, etc. The function stops
   when either the first error is found, or all lassos are enumerated.

   If an error is found, then the iterator of the failed formula is returned.
   Otherwise None is returned.
 
   NOTE: this function creates multiple copies of the SMT solver.
 *)
val find_error_in_many_forms_interleaved:
    Runtime.runtime_t
        -> SpinIr.data_type_tab
        -> SymbSkel.Sk.skel_t
        -> (string * Spin.token SpinIr.expr) list
        -> PorBounds.D.deps_t
        -> SchemaIter.search_iter_t option

(* A parallel version of find_error_in_many_forms_interleaved *)
val find_error_in_many_forms_interleaved_MPI:
    Runtime.runtime_t
        -> SpinIr.data_type_tab
        -> SymbSkel.Sk.skel_t
        -> (string * Spin.token SpinIr.expr) list
        -> PorBounds.D.deps_t
        -> SchemaIter.search_iter_t option

(**
  Check one linear order.
 *)
val check_one_order:
    Smt.smt_solver -> SymbSkel.Sk.skel_t -> (string * spec_t)
    -> PorBounds.D.deps_t -> SchemaSmt.tac_t -> reach_opt:bool
    -> (int list * po_elem_t list)
    -> internal_result_t

(**
  Create a schema iterator. Used in testing.
 *)
val mk_schema_iterator:
    Smt.smt_solver
        -> SymbSkel.Sk.skel_t
        -> (string * spec_t)
        -> PorBounds.D.deps_t
        -> SchemaSmt.tac_t
        -> (unit -> unit)
        -> ((SchemaIter.search_iter_t -> SchemaIter.search_iter_t)
            * SchemaIter.search_iter_t)


(**
 Try to convert an LTL formula to UTL.

 Raises IllegalLtl_error, when the formula is not supported.

 @param form a spin expression that encodes an ltl formula.
 @return an LTL(F,G)-formula over counters.
 *)
val extract_utl: SymbSkel.Sk.skel_t -> Spin.token SpinIr.expr
    -> Spin.token SpinIr.expr * utl_k_spec_t


(**
  Create a cut graph from a UTL_TB formula and add a threshold graph.

  @param skel a threshold automaton.
  @param deps dependencies.
  @param spec a specification.

  @return (num_vertices, partial_order, reverse_map).
*)
val mk_cut_and_threshold_graph:
    SymbSkel.Sk.skel_t -> PorBounds.D.deps_t -> spec_t
    -> (int * ((int * int) list) * (po_elem_t Accums.IntMap.t))


(**
 Check, whether an LTL formula is supported by the checker.

 @param form a spin expression that encodes an LTL formula.
 @return true, if the formula belongs to the supported class.
 *)
val can_handle_spec:
    SpinIr.data_type_tab -> SymbSkel.Sk.skel_t -> Spin.token SpinIr.expr -> bool


(**
 Try to convert an LTL formula to UTL.

 @param form a spin expression that encodes an ltl formula.
 @return an LTL(F,G)-formula over counters.
 *)
val extract_safety_or_utl:
    SpinIr.data_type_tab -> SymbSkel.Sk.skel_t -> Spin.token SpinIr.expr
    -> spec_t

