(**
 A new implementation of a schema-based model checker that supports LTL(F, G)
 over counters and shared variables.

 Igor Konnov, 2016
 *)

(**
 The record type of a result returned by check_schema_tree_on_the_fly.
 *)
type result_t = {
    m_is_err_found: bool;
    m_counterexample_filename: string;
}

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
        -> SymbSkel.Sk.skel_t -> Spin.token SpinIr.expr
        -> PorBounds.D.deps_t -> SchemaSmt.tac_t
        -> result_t

