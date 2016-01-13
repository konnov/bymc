(**
 An implementation of schemaSmt.
 *)

open BatPrintf

open Accums
open SpinIr
open SymbSkel


type node_kind_t = Leaf | Intermediate


(** A single SMT frame that corresponds to a state in a path *)
module F = struct
    (**
     A data structure for an SMT frame.
     *)
    type frame_t = {
        (** sequential number of the frame *)
        no: int;
        (** acceleration factor of the transition leading to the frame *)
        accel_v: var; 
        (** one copy per location *)
        loc_vars: var list; 
        (** one copy per shared variable *)
        shared_vars: var list;
        (**  the variables (from loc_vars and shared_vars)
            introduced in this frame  *)
        new_vars: var list;
        (** mapping id of the original variable to its copy in the frame *) 
        var_map: var IntMap.t;
    }

    (* auxillary functions *)
    let mk_loc_var (tt: data_type_tab) frame_no proto =
        let nv = proto#fresh_copy (sprintf "F%d_at_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv

    let mk_shared_var (tt: data_type_tab) frame_no proto =
        let nv = proto#fresh_copy (sprintf "F%d_g_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv

    let map_frame_vars frame nframe expr =
        let map_var fr v =
            if IntMap.mem v#id fr.var_map
            then Var (IntMap.find v#id fr.var_map)
            else Var v
        in
        let rec sub = function
            | Var v -> map_var frame v
            | UnEx (Spin.NEXT, Var v) -> map_var nframe v
            | UnEx (t, e) -> UnEx (t, sub e)
            | BinEx (t, l, r) -> BinEx (t, sub l, sub r)
            | _ as e -> e
        in
        sub expr

    (* signature implementation *)

    (**
     Introduce a new frame and connect it to the previous one.
     *)
    let advance_frame tt sk prev_frame is_var_updated_fun =
        let next_no = 1 + prev_frame.no in 
        let copy_var ctor_fun (map, vs, new_vs) basev v =
            if is_var_updated_fun basev v
            then let nv = ctor_fun tt next_no basev in
                (IntMap.add basev#id nv map, nv :: vs, nv :: new_vs)
            else (map, v :: vs, new_vs)
        in
        let loc_vars = List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs) in
        let map, locs, new_vars =
            List.fold_left2 (copy_var mk_loc_var) (prev_frame.var_map, [], [])
                (List.rev loc_vars) (List.rev prev_frame.loc_vars) in
        let map, shared, new_vars =
            List.fold_left2 (copy_var mk_shared_var)
                (map, [], new_vars) (List.rev sk.Sk.shared) (List.rev prev_frame.shared_vars) in
        let accel_v = new_var (sprintf "F%d_warp" next_no) in
        tt#set_type accel_v (new data_type SpinTypes.TUNSIGNED);
        { no = next_no; accel_v = accel_v;
            loc_vars = locs; shared_vars = shared;
            new_vars = new_vars; var_map = map }

    (**
     Create a frame for an initial state.
     *)
    let init_frame tt sk =
        let loc_vars = List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs) in
        let empty_frame = {
            no = -1; accel_v = new_var "";
            loc_vars = loc_vars; shared_vars = sk.Sk.shared;
            new_vars = []; var_map = IntMap.empty
        }
        in
        advance_frame tt sk empty_frame (fun _ _ -> true)

    (**
     Push variable declarations into SMT.
     *)
    let declare_frame solver tt frame =
        solver#comment (sprintf "frame %d" frame.no);
        let add_var v =
            solver#append_var_def v (tt#get_type v) in
        add_var frame.accel_v;
        List.iter add_var frame.new_vars

    (**
     Push assertions into SMT.
     *)
    let assert_frame solver tt frame next_frame assertions =
        let add_expr e =
            ignore (solver#append_expr (map_frame_vars frame next_frame e)) in
        List.iter add_expr assertions

end


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

