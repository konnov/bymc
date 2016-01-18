(**
 A reachability checker that uses path schemas (CAV'15).
 This implementation is essentially what is described in the CAV'15 paper:
 
 Igor Konnov, Helmut Veith, Josef Widder.
 SMT and POR beat Counter Abstraction: Parameterized Model Checking of
 Threshold-based Distributed Algorithms. CAV'15.
 

 @author Igor Konnov, 2014-2016
 *)

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


(* Retrieve a counterexample from the current SMT context *)
val get_counterex:
    Smt.smt_solver -> SymbSkel.Sk.skel_t -> string -> F.frame_t list
    -> string

(**
 A simple implementation of tac_t with SMT.
 *)
class tree_tac_t: Runtime.runtime_t -> SpinIr.data_type_tab ->
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

    end

