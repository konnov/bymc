(**
 A reachability checker that uses path schemas (CAV'15).
 This implementation is essentially what is described in the CAV'15 paper:
 
 Igor Konnov, Helmut Veith, Josef Widder.
 SMT and POR beat Counter Abstraction: Parameterized Model Checking of
 Threshold-based Distributed Algorithms. CAV'15.
 

 @author Igor Konnov, 2014-2016
 *)

val is_error_tree:
    Runtime.runtime_t
        -> SpinIr.data_type_tab
        -> SymbSkel.Sk.skel_t
        -> (int -> unit)
        -> string
        -> Spin.token SpinIr.expr
        -> PorBounds.D.deps_t
        -> PorBounds.T.schema_tree_t
        -> bool
