(**
  Synthesizing threshold automata using CEGYS.

  @author Igor Konnov, 2016
 *)

open Batteries

open Printf

open Accums
open Debug
open PorBounds
open Spin
open SpinIr
open SymbSkel
open SchemaSmt


exception No_solution


module BI = BatBig_int
module SCL = SchemaCheckerLtl

(** an iterator over the vectors of unknowns a_1, ..., a_k *)
type vec_iter_t = {
    (** the names of the unknowns *)
    f_names: string list;
    (** the degree of the upper bound (2^f_degree) on the unknowns' values *)
    f_degree: int;
    (** an integer that encodes the signs (s_i) and the values (each value v_i
        is represented with a bit string v^1_i, ..., v^m_i) as follows:
        v^1_1, ..., v^1_k, ..., v^m_1, ..., v^m_k, s_1, ..., s_k for k = f_degree *)
    f_gray: BI.big_int;
}


let iter_to_ints iter =
    let (k: int) = List.length iter.f_names in
    let extract_val (neg_zeroes, ints) (i: int) =
        let rec collect_val (shift: int) (j: int) =
            if j >= iter.f_degree
            then BI.zero_big_int
            else begin
                let (pos: int) = k + i + j * k in
                let (bit: BI.big_int) = BI.extract_big_int iter.f_gray pos 1 in
                (*printf "  i = %d, j = %d, pos = %d, bit = %s\n"
                    i j pos (BI.to_string bit);*)
                BI.add_big_int
                    (BI.shift_left_big_int bit shift)
                    (collect_val (shift + 1) (j + 1))
            end
        in
        let value = BI.int_of_big_int (collect_val 0 0) in
        let sign_pos = i in
        let sign_bit = BI.extract_big_int iter.f_gray sign_pos 1 in
        if BI.equal sign_bit BI.zero_big_int
        then (neg_zeroes, value :: ints)                    (* positive *)
        else ((value = 0) || neg_zeroes, (-value) :: ints)  (* negative *)
    in
    let neg_zeroes, ints = 
        List.fold_left extract_val (false, []) (range 0 k)
    in
    (neg_zeroes, List.rev ints)


let iter_to_unknowns_vec iter =
    let _, ints = iter_to_ints iter in
    let exprs = List.map (fun i -> IntConst i) ints in
    List.combine iter.f_names exprs


let map_of_unknowns_vec (vec: (string * Spin.token SpinIr.expr) list) =
    let add map (name, exp) = StrMap.add name exp map in
    List.fold_left add StrMap.empty vec


(** compute the initial vector of unknowns *)
let vec_iter_init sk (degree: int) =
    (* fill the last k bits with ones *)
    let rec all_ones n =
        (* 2 * x + 1 *)
        if n > 0
        then BI.succ_big_int (BI.shift_left_big_int (all_ones (n - 1)) 1)
        else BI.zero_big_int
    in
    let k = List.length sk.Sk.unknowns in
    {
        f_names = List.map (fun v -> v#get_name) sk.Sk.unknowns;
        f_degree = degree;
        f_gray = all_ones k; (* 00000(1)^k, i.e., all signs are set to 1 *)
    }


(** compute the next vector of unknowns *)
let rec vec_iter_next iter =
    let next_gray = BI.succ_big_int iter.f_gray in
    (*printf "  next = %s\n" (BI.to_string next_gray);*)
    let next_iter = {iter with f_gray = next_gray} in
    let neg_zeroes, next_ints = iter_to_ints next_iter in
    (*printf "next_ints = [%s]\n"
        (str_join ", " (List.map string_of_int next_ints));*)
    if neg_zeroes
    then vec_iter_next next_iter (* ignore values with -0 *)
    else next_iter


let vec_iter_end iter =
    let k = List.length iter.f_names in
    let beyond =
        BI.shift_left_big_int BI.unit_big_int (k + k * iter.f_degree)
    in
    (*printf "  beyond = %s\n" (BI.to_string beyond);*)
    BI.ge_big_int iter.f_gray beyond


let unknowns_vec_s vec =
    let pair_s (n, e) =
        sprintf "%s = %s" n (SpinIrImp.expr_s e)
    in
    str_join ", " (List.map pair_s vec)


(** replace unknowns with the values given in the unknowns vector *)
let replace_unknowns_in_expr unknowns_vec exp =
    let vec_map = map_of_unknowns_vec unknowns_vec in
    let map_fun v =
        try StrMap.find v#get_name vec_map
        with Not_found -> Var v
    in
    Simplif.compute_consts (map_vars map_fun exp)


(** replace unknowns with the values given in the unknowns vector *)
let replace_unknowns_in_skel sk unknowns_vec =
    let vec_map = map_of_unknowns_vec unknowns_vec in
    let sub exp =
        let map_fun v =
            try StrMap.find v#get_name vec_map
            with Not_found -> Var v
        in
        Simplif.compute_consts (map_vars map_fun exp)
    in
    let map_rule r =
        { r with Sk.guard = sub r.Sk.guard;
                 Sk.act = List.map sub r.Sk.act }
    in
    { sk with Sk.unknowns = [];
              Sk.assumes = List.map sub sk.Sk.assumes;
              Sk.rules = List.map map_rule sk.Sk.rules;
              Sk.inits = List.map sub sk.Sk.inits;
              Sk.forms = StrMap.map sub sk.Sk.forms;
    }


(** replace unknowns with the values given in the unknowns vector *)
let replace_unknowns_in_deps deps unknowns_vec =
    let vec_map = map_of_unknowns_vec unknowns_vec in
    let sub exp =
        let map_fun v =
            try StrMap.find v#get_name vec_map
            with Not_found -> Var v
        in
        Simplif.compute_consts (map_vars map_fun exp)
    in
    let map_mstone (n, elt, exp, lock) =
        (n, elt, sub exp, lock)
    in
    { deps with D.cond_map = PSetEltMap.map sub deps.D.cond_map;
              D.act_map = PSetEltMap.map sub deps.D.act_map;
              D.uconds = List.map map_mstone deps.D.uconds;
              D.lconds = List.map map_mstone deps.D.lconds;
    }


(** check, whether a counterexample is applicable to the skeleton *)    
let is_cex_applicable sk cex =
    let get_int = function
        | IntConst i -> i
        | _ as e ->
            raise (Failure ("Expected IntConst _, found %s" ^ (SpinIrImp.expr_s e)))
    in
    let bind state var =
        try IntConst (StrMap.find var#get_name state)
        with Not_found -> Var var
    in
    let apply_action accel state = function
        | BinEx (EQ, UnEx (NEXT, Var lhs),
                BinEx (PLUS, Var rhs, IntConst i)) ->
                    (* multiply the added value by the acceleration factor *)
            let mul_rhs =
                BinEx (PLUS, Var rhs, IntConst (i * accel)) in
            let rhs_val =
                Simplif.compute_consts (SpinIr.map_vars (bind state) mul_rhs)
            in
            StrMap.add lhs#get_name (get_int rhs_val) state

        | BinEx (EQ, UnEx (NEXT, Var lhs), Var rhs) ->
            if lhs#get_name = rhs#get_name
            then state
            else StrMap.add lhs#get_name (StrMap.find rhs#get_name state) state
            
        | _ as e ->
            let m = "Unexpected action: " ^ (SpinIrImp.expr_s e) in
            raise (Failure m)
    in
    let rec is_app state = function
        | [] ->
            true    (* no moves left *)

        | m :: tl ->    (* check the guard of the rule associated with m *)
            let r = List.nth sk.Sk.rules m.C.f_rule_no in
            let guard_val = Simplif.compute_consts
                (SpinIr.map_vars (bind state) r.Sk.guard)
            in
            (*
            printf " rule %d: guard %s evaluates to %s\n"
                m.C.f_rule_no
                (SpinIrImp.expr_s r.Sk.guard) (SpinIrImp.expr_s guard_val);
             *)
            match guard_val with
            | IntConst 0 ->
                (* the guard evaluates to false *)
                false

            | IntConst 1 ->
                (* the guard evaluates to true, go on *)
                let next_state =
                    List.fold_left (apply_action m.C.f_accel) state r.Sk.act
                in
                is_app next_state tl

            | _ ->
                let m = sprintf "Unexpected outcome of the guard %s: %s"
                    (SpinIrImp.expr_s r.Sk.guard) (SpinIrImp.expr_s guard_val)
                in
                raise (Failure m)
    in
    is_app cex.C.f_init_state cex.C.f_moves


(*************************************************************************)
type frame_stack_elem_t =
    | Frame of F.frame_t    (* just a frame *)
    | Node of int           (* a node marker *)
    | Context of int        (* a context marker *)


let bind state var =
    try IntConst (StrMap.find var#get_name state)
    with Not_found -> Var var


(**
 A tactic that tries to replay a counterexample generated by SchemaCheckerLtl.

 This class is a modified copy of SchemaChecker.tree_tac_t.
 *)
class eval_tac_t (tt: SpinIr.data_type_tab)
        (deps: PorBounds.D.deps_t)
        (cex: C.cex_t) (unknowns: (string * Spin.token SpinIr.expr) list) =
    object(self)
        inherit tac_t

        val mutable m_frames = []
        val mutable m_depth  = 0
        val mutable m_valid = true (* is the current set of constraints valid? *)
        val mutable m_moves_left = cex.C.f_moves
        val mutable m_state: int StrMap.t =
            let add m (n, e) = match e with
            | IntConst i -> StrMap.add n i m
            | _ -> raise (Failure "Expected IntConst _")
            in
            List.fold_left add
                (StrMap.add "F000000_warp" 0 cex.C.f_init_state) unknowns
        
        method top =
            let rec find = function
                | (Frame f) :: _ -> f
                | _ :: tl -> find tl
                | [] -> raise (Failure "Frame stack is empty")
            in
            find m_frames

        method frame_hist =
            let m l = function
                | Frame f -> f :: l
                | _ -> l
            in
            (* do not reverse m_frames as the first frame is the latest one *)
            List.fold_left m [] m_frames
 
        method private top2 =
            let rec find = function
                | (Frame f) :: tl -> f, tl
                | _ :: tl -> find tl
                | [] -> raise (Failure "Frame stack is empty")
            in
            let top, tl = find m_frames in
            let prev, _ = find tl in
            top, prev

        method push_frame f =
            (* nothing to do here *)
            m_frames <- (Frame f) :: m_frames

        method private assert_expr e =
            if not m_valid || (is_c_false e)
            then m_valid <- false
            else if not (is_c_true e)
            then begin
                let e_val =
                    Simplif.compute_consts (SpinIr.map_vars (bind m_state) e) in
                (*printf "expr = %s\n" (SpinIrImp.expr_s e);
                printf "e_val = %s\n" (SpinIrImp.expr_s e_val);*)
                match e_val with
                | IntConst 0 ->
                    m_valid <- false

                | IntConst 1 ->
                    ()

                | _ ->
                    let m = sprintf "Unexpected outcome of the expression %s: %s"
                        (SpinIrImp.expr_s e) (SpinIrImp.expr_s e_val)
                    in
                    raise (Failure m)
            end

        method assert_top assertions =
            List.iter self#assert_expr assertions 


        method assert_top2 assertions =
            raise (Failure "not implemented")

        method assert_frame_eq sk loop_frame =
            (* not required here *)
            ()

        method enter_node kind =
            let frame_no = self#top.F.no in
            m_frames <- (Node frame_no) :: m_frames;
            m_depth <- m_depth + 1

        method check_property form error_fun =
            let prop_value =
                if SpinIr.is_c_false form
                then false
                else begin
                    if (is_c_true form)
                    then m_valid (* the previous evaluation propagates *)
                    else begin
                        let old_valid = m_valid in
                        self#assert_top [form];
                        let res = m_valid in
                        m_valid <- old_valid;
                        (* take the previous along the path into account *)
                        res && m_valid
                    end
                    (* ignore the error function here
                    if m_valid
                    then error_fun self#frame_hist;
                    *)
                end
            in
            prop_value

        method leave_node kind =
            let rec unroll = function
                | (Node n) :: l -> (n, l)
                | _ :: l -> unroll l
                | [] -> (0, [])
            in
            m_depth <- m_depth - 1;
            let frame_no, old_frames = unroll m_frames in
            m_frames <- old_frames;
            assert (frame_no = self#top.F.no)

        method enter_context =
            let frame_no = self#top.F.no in
            m_depth <- m_depth + 1;
            m_frames <- (Context frame_no) :: m_frames


        method leave_context =
            let rec unroll = function
                | (Context n) :: l -> (n, l)
                | _ :: l -> unroll l
                | [] -> (0, [])
            in
            let frame_no, old_frames = unroll m_frames in
            m_frames <- old_frames;
            let old_no = self#top.F.no in
            assert (frame_no = old_no);
            m_depth <- m_depth - 1


        method pre_steady = ()

        method post_steady = ()


        method push_rule sk rule_no =
            let get_int = function
                | IntConst i -> i
                | _ as e ->
                    raise (Failure ("Expected IntConst _, found %s" ^ (SpinIrImp.expr_s e)))
            in
            let not_redundant_action = function
                | BinEx (Spin.EQ, UnEx (Spin.NEXT, Var l), Var r) ->
                        l#get_name <> r#get_name
                | _ -> true
            in
            let rule = List.nth sk.Sk.rules rule_no in
            let move = List.hd m_moves_left in
            let do_update _ =
                let frame = self#top in
                let actions = List.filter not_redundant_action rule.Sk.act in
                let is_new_f _ _ = false in (* nothing new *)
                let new_frame = F.advance_frame tt sk frame rule_no is_new_f in
                self#push_frame new_frame;
                let move_loc state loc add_fun =
                    let loc_var = IntMap.find loc sk.Sk.loc_vars in
                    let old_val = StrMap.find loc_var#get_name state in
                    let new_val = add_fun old_val move.C.f_accel in
                    if new_val < 0
                    then m_valid <- false; (* WARNING: updating the attribute here *)
                    (*printf "updating loc%d from %d to %d\n" loc old_val new_val;*)
                    StrMap.add loc_var#get_name new_val state
                in
                let new_state =
                    if rule.Sk.src <> rule.Sk.dst (* don't do it for self-loops *)
                    then move_loc
                            (move_loc m_state rule.Sk.src (-))
                            rule.Sk.dst (+)
                    else m_state
                in
                let rule_guard =
                    (* Milestone conditions are either:
                        known a priori in a segment,
                        or checked once for a milestone.
                      Thus, check only non-milestone conditions
                     *)
                    PorBounds.D.non_milestones deps rule_no
                in
                let guard_val =
                    Simplif.compute_consts (SpinIr.map_vars (bind m_state) rule_guard)
                in
                if m_valid
                then m_valid <- ((move.C.f_accel = 0) || (get_int guard_val) = 1);
                let apply_action accel state = function
                    | BinEx (EQ, UnEx (NEXT, Var lhs),
                            BinEx (PLUS, Var rhs, IntConst i)) ->
                                (* multiply the added value by the acceleration factor *)
                        let mul_rhs =
                            BinEx (PLUS, Var rhs, IntConst (i * accel)) in
                        let rhs_val =
                            Simplif.compute_consts (SpinIr.map_vars (bind state) mul_rhs)
                        in
                        StrMap.add lhs#get_name (get_int rhs_val) state

                    | BinEx (EQ, UnEx (NEXT, Var lhs), Var rhs) ->
                        if lhs#get_name = rhs#get_name
                        then state
                        else StrMap.add lhs#get_name (StrMap.find rhs#get_name state) state
                        
                    | _ as e ->
                        let m = "Unexpected action: " ^ (SpinIrImp.expr_s e) in
                        raise (Failure m)
                in
                m_moves_left <- List.tl m_moves_left;
                let new_state =
                    if m_valid
                    then List.fold_left
                        (apply_action move.C.f_accel) new_state actions
                    else m_state
                in
                (* also add the acceleration factor into the state *)
                (*printf "\nadded %s = %d\n" frame.F.accel_v#get_name move.C.f_accel;*)
                m_state <- StrMap.add new_frame.F.accel_v#get_name move.C.f_accel new_state
            in
            (* it might happen that the rules diverge, e.g., when the counterexample
               is generated from another sequence of rules
             *)
            if rule_no = move.C.f_rule_no && m_valid
            then do_update ()


        method reset =
            m_frames <- [];
            m_depth <- 0


        method set_incremental (_: bool) =
            ()

        method get_incremental =
            false
    end


(**
 A tactic that transforms a counterexample into constraints over the unknowns.

 This class is a modified copy of SchemaChecker.eval_tac_t.
 XXX: Refactor.
 *)
class simp_tac_t (tt: SpinIr.data_type_tab)
        (deps: PorBounds.D.deps_t)
        (cex: C.cex_t) (template: SymbSkel.Sk.skel_t)
        (unknowns: (string * Spin.token SpinIr.expr) list) =
    object(self)
        inherit tac_t

        val mutable m_moves_left = cex.C.f_moves
        val mutable m_state: int StrMap.t =
            StrMap.add "F000000_warp" 0 cex.C.f_init_state
        val mutable m_eval_tac = new eval_tac_t tt deps cex unknowns
        (* we collect assertions here, since we need a negation *)
        val mutable m_assertions = []
        
        method top =
            m_eval_tac#top

        method frame_hist =
            m_eval_tac#frame_hist

        method push_frame f =
            m_eval_tac#push_frame f

        method private assert_expr e =
            if not (is_c_true e) && not (is_c_false e)
            then begin
                let e_val =
                    Simplif.compute_consts (SpinIr.map_vars (bind m_state) e) in
                (*printf "expr = %s\n" (SpinIrImp.expr_s e);
                printf "e_val = %s\n" (SpinIrImp.expr_s e_val);*)
                m_assertions <- e_val :: m_assertions
            end

        method assert_top assertions =
            m_eval_tac#assert_top assertions;
            List.iter self#assert_expr assertions 

        method assert_top2 assertions =
            raise (Failure "not implemented")

        method assert_frame_eq sk loop_frame =
            m_eval_tac#assert_frame_eq sk loop_frame

        method enter_node kind =
            m_eval_tac#enter_node kind

        method check_property form error_fun =
            let res = m_eval_tac#check_property form error_fun in
            (* check with the evaluation on the current parameters *)
            self#assert_top (if res then [form] else [(UnEx (NEG, form))]);
            res

        method leave_node kind =
            m_eval_tac#leave_node kind

        method enter_context =
            m_eval_tac#enter_context

        method leave_context =
            m_eval_tac#leave_context


        method pre_steady = ()

        method post_steady = ()

        method push_rule sk rule_no =
            let get_int = function
                | IntConst i -> i
                | _ as e ->
                    raise (Failure ("Expected IntConst _, found %s" ^ (SpinIrImp.expr_s e)))
            in
            let not_redundant_action = function
                | BinEx (Spin.EQ, UnEx (Spin.NEXT, Var l), Var r) ->
                        l#get_name <> r#get_name
                | _ -> true
            in
            (* NOTE: we extract the rule from the template *)
            let rule = List.nth template.Sk.rules rule_no in
            let move = List.hd m_moves_left in
            let do_update _ =
                let frame = self#top in
                let actions = List.filter not_redundant_action rule.Sk.act in
                (* push the rule to eval_tac_t *)
                m_eval_tac#push_rule sk rule_no;
                (* and now we have a new frame! *)
                let new_frame = self#top in
                self#push_frame new_frame;
                let move_loc state loc add_fun =
                    let loc_var = IntMap.find loc sk.Sk.loc_vars in
                    let old_val = StrMap.find loc_var#get_name state in
                    let new_val = add_fun old_val move.C.f_accel in
                    assert (new_val >= 0);
                    StrMap.add loc_var#get_name new_val state
                in
                let new_state =
                    if rule.Sk.src <> rule.Sk.dst (* don't do it for self-loops *)
                    then move_loc
                            (move_loc m_state rule.Sk.src (-))
                            rule.Sk.dst (+)
                    else m_state
                in
                let apply_action accel state = function
                    | BinEx (EQ, UnEx (NEXT, Var lhs),
                            BinEx (PLUS, Var rhs, IntConst i)) ->
                                (* multiply the added value by the acceleration factor *)
                        let mul_rhs =
                            BinEx (PLUS, Var rhs, IntConst (i * accel)) in
                        let rhs_val =
                            Simplif.compute_consts (SpinIr.map_vars (bind state) mul_rhs)
                        in
                        StrMap.add lhs#get_name (get_int rhs_val) state

                    | BinEx (EQ, UnEx (NEXT, Var lhs), Var rhs) ->
                        if lhs#get_name = rhs#get_name
                        then state
                        else StrMap.add lhs#get_name (StrMap.find rhs#get_name state) state
                        
                    | _ as e ->
                        let m = "Unexpected action: " ^ (SpinIrImp.expr_s e) in
                        raise (Failure m)
                in
                m_moves_left <- List.tl m_moves_left;
                let new_state =
                    List.fold_left
                        (apply_action move.C.f_accel) new_state actions
                in
                (* also add the acceleration factor into the state *)
                m_state <- StrMap.add new_frame.F.accel_v#get_name move.C.f_accel new_state
            in
            (* it might happen that the rules diverge, e.g., when the counterexample
               is generated from another sequence of rules
             *)
            assert (rule_no = move.C.f_rule_no);
            (* compute the current value of the rule guard *)
            let simp_guard =
                Simplif.compute_consts (SpinIr.map_vars (bind m_state) rule.Sk.guard)
            in
            (*printf "rule %d, factor %d, simp_guard = %s\n"
                rule_no move.C.f_accel (SpinIrImp.expr_s simp_guard);*)
            (* and then do an update as prescribed by the actions *)
            do_update ();
            if move.C.f_accel > 0
            then begin
                (* just for debugging *)
                let guard_eval = replace_unknowns_in_expr unknowns simp_guard in
                if (IntConst 0) = guard_eval
                then begin
                    printf "   > FAILED rule %d, factor %d, simp_guard = %s\n"
                        rule_no move.C.f_accel (SpinIrImp.expr_s simp_guard);
                    assert ((IntConst 1) = guard_eval)
                end;
                (* debugging ends *)
                m_assertions <- simp_guard :: m_assertions (* push the assertions *)
            end
            (* else the rule was not fired, ignore its guards *)


        method reset =
            m_eval_tac#reset

        method set_incremental (_: bool) =
            ()

        method get_incremental =
            false


        (**
         Finally, push the assertions to the solver.

         NOTE: this is the most interesting function here!
         *)
        method push_assertions (synt_solver: Smt.smt_solver) =
            let e = Simplif.propagate_not
                ~negate:true (list_to_binex AND m_assertions) in
            let se = Simplif.compute_consts e in
            match se with
            | IntConst 0 ->
                raise (Failure "The example is unconditionally true")

            | IntConst 1 ->
                (* The counterexample appears to be useless... What shall we do? *)
                let pa e = printf "  %s\n" (SpinIrImp.expr_s e) in
                printf "Collected assertions (there should be no zeros!):\n";
                List.iter pa m_assertions;
                raise (Failure "Useless counterexample. Giving up.")

            | _ ->
                ignore (synt_solver#append_expr se)
    end


(** check, whether a counterexample is applicable to the skeleton *)    
let is_cex_applicable_new solver type_tab sk deps cex =
    let spec =
        let form = StrMap.find cex.C.f_form_name sk.Sk.forms in
        let neg_form = Ltl.normalize_form (UnEx (NEG, form)) in
        (*printf "neg_form = %s\n" (SpinIrImp.expr_s neg_form);*)
        let ltl, utl = SCL.extract_utl sk neg_form in
        SCL.UTL (ltl, utl)
    in
    let size, par_order, rev_map =
        SCL.mk_cut_and_threshold_graph sk deps spec
    in
    let is_struct_ok =
        (* is there a way to decode the order? *)
        size > (List.fold_left max 0 cex.C.f_iorder)
    in
    (*
    let kvs =
        List.map
            (fun (k, v) ->
                sprintf "%d -> %s" k (C.po_elem_struc_s (SCL.struc_of_po_elem v)))
            (IntMap.bindings rev_map)
    in
    printf "rev_map(%d) = {%s}\n" size (str_join ", " kvs);
    *)
    let eorder =
        try List.map (fun n -> IntMap.find n rev_map) cex.C.f_iorder
        with Not_found -> []
    in
    let po_elem_struc_list = List.map SCL.struc_of_po_elem eorder in
    if not is_struct_ok (*po_elem_struc_list <> cex.C.f_po_struc*)
    then begin
        (*
        printf "The structures are not equal:\n  %s\n  %s\n"
            (str_join ", " (List.map C.po_elem_struc_s po_elem_struc_list))
            (str_join ", " (List.map C.po_elem_struc_s cex.C.f_po_struc));
            *)
        false
    end
    else begin
        log INFO (sprintf "Using the order: %s...\n"
            (str_join ", " (List.map C.po_elem_struc_s po_elem_struc_list)));
        let ntt = type_tab#copy in
        (* XXX: introduce variables for the location counters *)
        let loc_vars = IntMap.values sk.Sk.loc_vars in
        let set_type v = ntt#set_type v (new data_type SpinTypes.TUNSIGNED) in
        BatEnum.iter set_type loc_vars;
        (* END: XXX *)
        let tac = new eval_tac_t ntt deps cex [] in
        solver#push_ctx;
        let initf = F.init_frame ntt sk in
        tac#push_frame initf;
        tac#assert_top sk.Sk.inits;
        let res =
            SCL.check_one_order solver sk (cex.C.f_form_name, spec) deps
                    (tac :> SchemaSmt.tac_t) ~reach_opt:false (cex.C.f_iorder, eorder)
        in
        solver#pop_ctx;
        if not res.SCL.m_is_err
        then log ERROR ("Failed to replay the counterexample. The tool is buggy!");
        res.SCL.m_is_err
    end


(** Is the synthesized solution vacuously true, i.e.,
    the assumptions are contradictory.
 *)
let is_ta_vacuous solver sk =
    if List.mem (IntConst 0) sk.Sk.assumes
    then true (* assume(0) is met *)
    else begin
        solver#push_ctx;
        let append_expr e =
            if e <> (IntConst 1)
            then ignore (solver#append_expr e)
        in
        List.iter append_expr sk.Sk.assumes;
        let unsat = not solver#check in
        solver#pop_ctx;
        unsat
    end


(**
 Push a counterexample to the own solver of the synthesizer.
 *)
let push_counterexample solver synt_solver type_tab sk deps template unknowns cex =
    let spec =
        let form = StrMap.find cex.C.f_form_name template.Sk.forms in
        let neg_form = Ltl.normalize_form (UnEx (NEG, form)) in
        (*printf "neg_form = %s\n" (SpinIrImp.expr_s neg_form);*)
        if Ltl.is_propositional type_tab neg_form
        then SCL.Propositional neg_form (* propositional forms need special care *)
        else let ltl, utl = SCL.extract_utl template neg_form in
            SCL.UTL (ltl, utl)
    in
    let size, par_order, rev_map =
        (* XXX: using deps from sk, not template *)
        SCL.mk_cut_and_threshold_graph template deps spec
    in
    let eorder =
        try List.map (fun n -> IntMap.find n rev_map) cex.C.f_iorder
        with Not_found -> []
    in
    let tac = new simp_tac_t type_tab deps cex template unknowns in
    solver#push_ctx;
    let initf = F.init_frame type_tab sk in
    tac#push_frame initf;
    let not_const_true e = (e <> (IntConst 1)) in
    tac#assert_top (List.filter not_const_true template.Sk.assumes);
    tac#assert_top template.Sk.inits;
    let res =
        SCL.check_one_order solver template (cex.C.f_form_name, spec) deps
                (tac :> SchemaSmt.tac_t) ~reach_opt:false (cex.C.f_iorder, eorder)
    in
    solver#pop_ctx;
    if not res.SCL.m_is_err
    then log ERROR ("Failed to replay the counterexample. The tool is buggy!");
    (* push the assertions! *)
    tac#push_assertions synt_solver;
    ()


(** exclude a given tuple of unknowns from consideration *)
let exclude_unknowns synt_solver assumptions unknowns =
    let neq (name, value) = BinEx (NE, Var (SpinIr.new_var name), value) in
    let ineqs = List.map neq unknowns in
    if ineqs <> []
    then begin
        synt_solver#comment ("excluded " ^ (unknowns_vec_s unknowns));
        ignore (synt_solver#append_expr (list_to_binex OR ineqs))
    end


(*
  Merge equivalent conditions into one.
  E.g., x >= a, x >= 2 * a, x >= 3 * a will be merged into one when a = 0.

  FEATURE: implement this feature.
*)
let merge_in_deps deps =
    deps

