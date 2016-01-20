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
 The record type of a result returned by check_schema_tree_on_the_fly.
 *)
type result_t = {
    m_is_err_found: bool;
    m_counterexample_filename: string;
}

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
    | Safety of Spin.token SpinIr.expr * Spin.token SpinIr.expr
        (* a safety violation: init_form -> F bad_form *)
    | UTL of Spin.token SpinIr.expr * utl_k_spec_t
        (* an unrestricted propositional formula for the initial states
           and a UTL formula *)


(** Convert an atomic formula to a string *)
val atomic_spec_s: atomic_spec_t -> string


(** Convert a UTL formula to a string *)
val utl_spec_s: utl_k_spec_t -> string


(**
 Try to find a bug using gen_and_check_schemas_on_the_fly.
 *)
val find_error:
    Runtime.runtime_t
        -> SpinIr.data_type_tab
        -> SymbSkel.Sk.skel_t -> string
        -> Spin.token SpinIr.expr
        -> PorBounds.D.deps_t
        -> result_t
   
(**
 Enumerate all schemas and try to find a bug.
 *)
val gen_and_check_schemas_on_the_fly:
    Smt.smt_solver
        -> SymbSkel.Sk.skel_t -> spec_t
        -> PorBounds.D.deps_t -> SchemaSmt.tac_t
        -> result_t


(**
 Try to convert an LTL formula to UTL.

 Raises IllegalLtl_error, when the formula is not supported.

 @param form a spin expression that encodes an ltl formula.
 @return an LTL(F,G)-formula over counters.
 *)
val extract_utl: SymbSkel.Sk.skel_t -> Spin.token SpinIr.expr
    -> Spin.token SpinIr.expr * utl_k_spec_t


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

