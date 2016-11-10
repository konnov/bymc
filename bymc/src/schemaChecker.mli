(**
 A reachability checker that uses path schemas (CAV'15).
 This implementation is essentially what is described in the CAV'15 paper:
 
 Igor Konnov, Helmut Veith, Josef Widder.
 SMT and POR beat Counter Abstraction: Parameterized Model Checking of
 Threshold-based Distributed Algorithms. CAV'15.
 

 @author Igor Konnov, 2014-2016
 *)

open Batteries

open SchemaSmt


(**
 Find a reachable state that violates a specification
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


(* Retrieve a counterexample from the current SMT context and write it to the output *)
val write_counterex:
    ?start_no:int  -> Smt.smt_solver -> SymbSkel.Sk.skel_t -> unit BatIO.output
    -> F.frame_t list -> int

(* Transform a counterexample into cex_t *)
val counterex_of_frame_hist:
    ?start_no:int  -> Smt.smt_solver -> SymbSkel.Sk.skel_t
    -> string -> int list -> F.frame_t list -> SchemaSmt.C.cex_t

(**
 An SMT implementation of tac_t.

 By default, the tactic is working in the incremental mode, i.e., a new node
 and a context introduces a new SMT context.  The incremental mode can be used
 to check schemas that share a common prefix.

 In the non-incremental mode, no new SMT context is ever introduced.
 This mode can be used to check individual schemas one-by-one.
 Note that this mode is intended only for LTL checking (see SchemaCheckerLtl).
 *)
class tree_tac_t: Smt.smt_solver -> SpinIr.data_type_tab ->
    object
        inherit tac_t
        
        method top: F.frame_t

        method frame_hist: F.frame_t list
 
        method push_frame: F.frame_t -> unit

        method assert_top:
            Spin.token SpinIr.expr list -> unit

        method assert_top2:
            Spin.token SpinIr.expr list -> unit

        method assert_frame_eq:
            SymbSkel.Sk.skel_t -> F.frame_t -> unit

        method enter_node: node_kind_t -> unit

        method check_property:
            Spin.token SpinIr.expr -> (F.frame_t list -> unit) -> bool

        method leave_node: node_kind_t -> unit

        method enter_context: unit

        method leave_context: unit

        method push_rule: PorBounds.D.deps_t -> SymbSkel.Sk.skel_t -> int -> unit

        method set_incremental: bool -> unit

        method get_incremental: bool
    end

