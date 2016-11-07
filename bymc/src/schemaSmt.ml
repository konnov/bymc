(**
 An implementation of schemaSmt.
 *)

open Batteries
open Printf
open Sexplib

open Accums
open SpinIr
open SymbSkel


(**
 A node type: an intermediate node, a loop start, or a leaf.
 *)
type node_kind_t = Leaf | Intermediate | LoopStart



(** A single SMT frame that corresponds to a state in a path *)
module F = struct
    (**
     A data structure for an SMT frame.
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

    (* auxillary functions *)
    let mk_loc_var (tt: data_type_tab) frame_no proto =
        let nv = proto#fresh_copy (sprintf "F%06d_at_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv

    let mk_shared_var (tt: data_type_tab) frame_no proto =
        let nv = proto#fresh_copy (sprintf "F%06d_g_%s" frame_no proto#get_name) in
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
    let advance_frame tt sk prev_frame rule_no is_var_updated_fun =
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
        let accel_v = new_var (sprintf "F%06d_warp" next_no) in
        tt#set_type accel_v (new data_type SpinTypes.TUNSIGNED);
        { no = next_no; rule_no = rule_no; accel_v = accel_v;
            loc_vars = locs; shared_vars = shared;
            new_vars = new_vars; var_map = map }

    (**
     Create a frame for an initial state.
     *)
    let init_frame tt sk =
        let loc_vars = List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs) in
        let empty_frame = {
            no = -1; (* advance_frame sets no to 0 *)
            rule_no = -1; (* no rule to lead to the initial frame *)
            accel_v = new_var "";
            loc_vars = loc_vars; shared_vars = sk.Sk.shared;
            new_vars = []; var_map = IntMap.empty
        }
        in
        advance_frame tt sk empty_frame (-1) (fun _ _ -> true)

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
     Convert an expression to a frame-specific expression.
     *)
    let to_frame_expr frame next_frame exp =
        map_frame_vars frame next_frame exp

    (**
     Push assertions into SMT.
     *)
    let assert_frame solver tt frame next_frame assertions =
        let add_expr e =
            ignore (solver#append_expr (map_frame_vars frame next_frame e))
        in
        List.iter add_expr assertions


    (**
     Assert that all the variables in two frames are equal, e.g.,
     to check whether a loop has been formed.
     *)
    let assert_frame_eq solver tt vars frame1 frame2 =
        let eq v = BinEx (Spin.EQ, UnEx (Spin.NEXT, Var v), Var v) in
        assert_frame solver tt frame2 frame1 (List.map eq vars)
end


(**
  A counterexample
  *)
module C = struct
    type move_t = {
        f_rule_no: int;   (** the rule that performed the move *)
        f_accel: int;     (** the acceleration factor *)
    }

    type cex_t = {
        f_loop_index: int;
            (** the index of the loop start in the list f_moves *) 
        f_init_state: int Accums.StrMap.t;
            (** a variable assignment in the initial state *)
        f_moves: move_t list;
            (** the moves made *)
    }

    module S = Sexp

    let save_cex filename cex =
        let of_keyval (name, value) =
            S.List [S.Atom name; S.Atom (string_of_int value)]
        in
        let of_move m =
            S.List [S.Atom (string_of_int m.f_rule_no);
                    S.Atom (string_of_int m.f_accel)]
        in
        let sexp = S.List [
            S.List [
                S.Atom "loop";
                S.Atom (string_of_int cex.f_loop_index)
            ];
            S.List [
                S.Atom "init";
                S.List (List.map of_keyval (StrMap.bindings cex.f_init_state));
            ];
            S.List [
                S.Atom "moves";
                S.List (List.map of_move cex.f_moves)
            ];
        ]
        in
        S.save_hum filename sexp

        
    let load_cex filename =
        let add_kv map = function
            | S.List [S.Atom n; S.Atom v] ->
                StrMap.add n (int_of_string v) map

            | _ -> raise (Failure "Expected a pair of (string, int)")
        in
        let to_move = function
            | S.List [S.Atom no; S.Atom acc] ->
                { f_rule_no = int_of_string no; f_accel = int_of_string acc }

            | _ -> raise (Failure "Expected a pair of (int, int)")
        in
        let parse = function
            | S.List [
                S.List [S.Atom "loop"; S.Atom ls];
                S.List [S.Atom "init"; S.List init_lst];
                S.List [S.Atom "moves"; S.List move_lst];
            ] ->
            {
                f_loop_index = int_of_string ls;
                f_init_state = List.fold_left add_kv StrMap.empty init_lst;
                f_moves = List.map to_move move_lst;
            }

            | _ -> raise (Failure "Expected ((loop int) (init _) (moves _))")
        in
        parse (S.load_sexp filename)
end


(**
 There are different ways to enumerate schemas, which are effectively
 branches of the schema tree.  Here we introduce a general interface for
 different tactics that apply to a depth-first search over the schema tree.
*)
class virtual tac_t =
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
         Push a rule into the SMT solver.

         @param rule_no a rule number
         *)
        method virtual push_rule: PorBounds.D.deps_t -> SymbSkel.Sk.skel_t -> int -> unit
    end

