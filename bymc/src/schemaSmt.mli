(**
 Elements of our schema encoding in SMT.

 @author Igor Konnov, 2015-2016
 *)


(** A single SMT frame that corresponds to a state in a path *)
module F: sig
    (**
     A data structure for an SMT frame.

     TODO: encapsulate?
     *)
    type frame_t = {
        (** sequential number of the frame *)
        no: int;
        (** acceleration factor of the transition leading to the frame *)
        accel_v: SpinIr.var; 
        (** one copy per location *)
        loc_vars: SpinIr.var list; 
        (** one copy per shared variable *)
        shared_vars: SpinIr.var list;
        (**  the variables (from loc_vars and shared_vars)
            introduced in this frame  *)
        new_vars: SpinIr.var list;
        (** mapping id of the original variable to its copy in the frame *) 
        var_map: SpinIr.var Accums.IntMap.t;
    }

    (**
     Create a frame for an initial state.
     *)
    val init_frame: SpinIr.data_type_tab -> SymbSkel.Sk.skel_t -> frame_t

    (**
     Introduce a new frame and connect it to the previous one.
     *)
    val advance_frame: SpinIr.data_type_tab -> SymbSkel.Sk.skel_t -> frame_t
        -> (SpinIr.var -> SpinIr.var -> bool) -> frame_t

    (**
     Push variable declarations into SMT.
     *)
    val declare_frame: Smt.smt_solver -> SpinIr.data_type_tab -> frame_t -> unit

    (**
     Push assertions into SMT.
     *)
    val assert_frame: Smt.smt_solver -> SpinIr.data_type_tab
        -> frame_t -> frame_t -> Spin.token SpinIr.expr list -> unit
end 


(**
 A node type: a leaf or an intermediate node.
 *)
type node_kind_t = Leaf | Intermediate


(**
 There are different ways to enumerate schemas, which are effectively
 branches of the schema tree.  Here we introduce a general interface for
 different tactics that apply to a depth-first search over the schema tree.
*)
class type tac_t =
    object
        (**
         Declare a new frame, which corresponds to a new state.
         This frame is pushed on the frame stack.
         *)
        method push_frame: F.frame_t -> unit

        (**
         Return the frame on the top
         *)
        method top: F.frame_t

        (**
         Return the sequence of frames generated so far
         (starting with the initial one)
         *)
        method frame_hist: F.frame_t list

        
        (**
         Add assertions to the frame on the top of the frame stack.
         
         @param expressions the expressions to assert
         *)
        method assert_top:
            Spin.token SpinIr.expr list -> unit

        
        (** 
         Add assertion to a pair of frames on the top.
         
         @param expressions to assert, where Next(Var _) refers to the
                topmost frame and (Var _) refers to the second topmost
                frame
         *)
        method assert_top2:
            Spin.token SpinIr.expr list -> unit

        (**
         This function is called when a new tree node is entered.
         The functions enter/leave are called in the depth-first order.

         @param node_kind indicates whether the node is
                leaf (Leaf), or not (Intermediate)
         *)
        method enter_node: node_kind_t -> unit

        (**
         Check, whether the property is violated in the current frame.
         The actual check can be postponed, depending on the actual tactic
         implementation. The only guarantee is that if the property is violated
         for some tree node, then it will be eventually reported for some call
         of check_property
         
         @form ltl propositional formula
         @error_fun function handler to be called on error,
            e.g., to print the trace
         *)
        method check_property:
            Spin.token SpinIr.expr -> (F.frame_t list -> unit) -> bool

        (**
         This function is called when a tree node is left.
         The functions enter/leave are called in the depth-first order.

         @param node_kind indicates whether the node is
                leaf (Leaf), or not (Intermediate)
         *)
        method leave_node: node_kind_t -> unit

        (**
         Enter the new context, also called a branch in the schema tree.
         The functions enter/leave are called in the depth-first order.
         *)
        method enter_context: unit

        (**
         Leave the context, also called a branch in the schema tree.
         The functions enter/leave are called in the depth-first order.
         *)
        method leave_context: unit

        (**
         Push a rule into the SMT solver.

         @param rule_no a rule number
         *)
        method push_rule: PorBounds.D.deps_t -> SymbSkel.Sk.skel_t -> int -> unit
    end

