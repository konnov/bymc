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
        no: int;
            (** sequential number of the frame *)
        rule_no: int;
            (** the number of the rule that leads to this frame *)
        accel_v: SpinIr.var;
            (** acceleration factor of the transition leading to the frame *)
        loc_vars: SpinIr.var list;
            (** one copy per location *)
        shared_vars: SpinIr.var list;
            (** one copy per shared variable *)
        new_vars: SpinIr.var list;
            (**  the variables (from loc_vars and shared_vars)
                introduced in this frame  *)
        var_map: SpinIr.var Accums.IntMap.t;
            (** mapping id of the original variable to its copy in the frame *) 
    }

    (**
     Create a frame for an initial state.
     *)
    val init_frame: SpinIr.data_type_tab -> SymbSkel.Sk.skel_t -> frame_t

    (**
     Introduce a new frame and connect it to the previous one.
     *)
    val advance_frame: SpinIr.data_type_tab -> SymbSkel.Sk.skel_t -> frame_t
        -> int -> (SpinIr.var -> SpinIr.var -> bool) -> frame_t

    (**
     Push variable declarations into SMT.
     *)
    val declare_frame: Smt.smt_solver -> SpinIr.data_type_tab -> frame_t -> unit

    (**
     Push assertions into SMT.
     *)
    val assert_frame: Smt.smt_solver -> SpinIr.data_type_tab
        -> frame_t -> frame_t -> Spin.token SpinIr.expr list -> unit

    (**
     Assert that all the variables in two frames are equal, e.g.,
     to check whether a loop has been formed.
     *)
    val assert_frame_eq: Smt.smt_solver -> SpinIr.data_type_tab
        -> SpinIr.var list -> frame_t -> frame_t -> unit

    (**
     Convert an expression to a frame-specific expression.
     *)
    val to_frame_expr: frame_t -> frame_t
        -> Spin.token SpinIr.expr -> Spin.token SpinIr.expr
end 


(**
  A counterexample
  *)
module C: sig
    (* the structure of a partial order *)
    type po_elem_struc_t =
        | PO_init_struc
        | PO_loop_start_struc
        | PO_guard_struc
        | PO_tl_struc

    type move_t = {
        f_rule_no: int;   (** the rule that performed the move *)
        f_accel: int;     (** the acceleration factor *)
    }

    type cex_t = {
        f_form_name: string;
            (** formula name *)
        f_loop_index: int;
            (** the index of the loop start in the list f_moves *) 
        f_init_state: int Accums.StrMap.t;
            (** a variable assignment in the initial state *)
        f_moves: move_t list;
            (** the moves made *)
        f_iorder: int list;
            (** the order that has generated the counterexample *)
        f_po_struc: po_elem_struc_t list;
            (** the structure of the linear order required by the counterex. *)
    }

    (* a string representation of a po_elem_struc_t *)
    val po_elem_struc_s: po_elem_struc_t -> string

    (** save a counterexample to a file *)
    val save_cex: string -> cex_t -> unit

    (** load a counterexample from a file *)
    val load_cex: string -> cex_t
end


(**
 A node type: an intermediate node, a loop start, or a leaf.
 *)
type node_kind_t = Leaf | Intermediate | LoopStart


(**
 There are different ways to enumerate schemas, which are effectively
 branches of the schema tree.  Here we introduce a general interface for
 different tactics that apply to a depth-first search over the schema tree.
*)
class virtual tac_t:
    object
        (**
         Declare a new frame, which corresponds to a new state.
         This frame is pushed on the frame stack.
         *)
        method virtual push_frame: F.frame_t -> unit

        (**
         Return the frame on the top
         *)
        method virtual top: F.frame_t

        (**
         Return the sequence of frames generated so far
         (starting with the initial one)
         *)
        method virtual frame_hist: F.frame_t list

        
        (**
         Add assertions to the frame on the top of the frame stack.
         
         @param expressions the expressions to assert
         *)
        method virtual assert_top:
            Spin.token SpinIr.expr list -> unit

        
        (** 
         Add assertion to a pair of frames on the top.
         
         @param expressions to assert, where Next(Var _) refers to the
                topmost frame and (Var _) refers to the second topmost
                frame
         *)
        method virtual assert_top2:
            Spin.token SpinIr.expr list -> unit

        (** 
         Add assertion that the variables in two frames are equal.
         
         @param skel a symbolic skeleton
         @param a frame to compare the top against
         *)
        method virtual assert_frame_eq:
            SymbSkel.Sk.skel_t -> F.frame_t -> unit

        (**
         This function is called when a new tree node is entered.
         The functions enter/leave are called in the depth-first order.

         @param node_kind indicates whether the node is
                leaf (Leaf), or not (Intermediate)
         *)
        method virtual enter_node: node_kind_t -> unit

        (**
         Check, whether the property is violated in the current frame.
         The actual check can be postponed, depending on the actual tactic
         implementation. The only guarantee is that if the property is violated
         for some tree node, then it will be eventually reported for some call
         of check_property
         
         @param form ltl propositional formula
         @param error_fun function handler to be called on error,
            e.g., to print the trace
         
         @return true, if there is an execution that satisfies the property
         *)
        method virtual check_property:
            Spin.token SpinIr.expr -> (F.frame_t list -> unit) -> bool

        (**
         This function is called when a tree node is left.
         The functions enter/leave are called in the depth-first order.

         @param node_kind indicates whether the node is
                leaf (Leaf), or not (Intermediate)
         *)
        method virtual leave_node: node_kind_t -> unit

        (**
         Enter the new context, also called a branch in the schema tree.
         The functions enter/leave are called in the depth-first order.
         *)
        method virtual enter_context: unit

        (**
         Leave the context, also called a branch in the schema tree.
         The functions enter/leave are called in the depth-first order.
         *)
        method virtual leave_context: unit

        (**
         A trigger to be called before a steady schedule is evaluated,
         e.g., to evaluate unlocking guards.
         *)
        method virtual pre_steady: unit

        (**
         A trigger to be called after a steady schedule is evaluated,
         e.g., to evaluate locking guards.
         *)
        method virtual post_steady: unit

        (**
         Push a rule into the SMT solver.

         @param rule_no a rule number
         *)
        method virtual push_rule: SymbSkel.Sk.skel_t -> int -> unit
    end

