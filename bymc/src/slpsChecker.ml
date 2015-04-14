(*
 * Encode path schemas and check them with an SMT solver.
 *
 * Igor Konnov, 2014-2015
 *)

open Printf

open Accums
open Debug
open PorBounds
open SpinIr
open SymbSkel

(* A single frame that corresponds to a state in a path *)
module F = struct
    type frame_t = {
        no: int; (* sequential number of the frame *)
        accel_v: var; (* acceleration factor of the transition leading to the frame *)
        loc_vars: var list; (* one copy per location *)
        shared_vars: var list; (* one copy per shared variable *)
        new_vars: var list;
            (*  the variables (from loc_vars and shared_vars)
                introduced in this frame  *)
        var_map: var IntMap.t;
            (* mapping id of the original variable to its copy in the frame *)
    }

    let mk_loc_var (tt: data_type_tab) frame_no proto =
        let nv = proto#fresh_copy (sprintf "F%d_at_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv


    let mk_shared_var (tt: data_type_tab) frame_no proto =
        let nv = proto#fresh_copy (sprintf "F%d_g_%s" frame_no proto#get_name) in
        tt#set_type nv (tt#get_type proto);
        nv

        (* TODO: myself 2015, please write a comment! *)
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

    let init_frame tt sk =
        let loc_vars = List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs) in
        let empty_frame = {
            no = -1; accel_v = new_var "";
            loc_vars = loc_vars; shared_vars = sk.Sk.shared;
            new_vars = []; var_map = IntMap.empty
        }
        in
        advance_frame tt sk empty_frame (fun _ _ -> true)

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

    let declare_frame solver tt frame =
        solver#comment (sprintf "frame %d" frame.no);
        let add_var v =
            solver#append_var_def v (tt#get_type v) in
        add_var frame.accel_v;
        List.iter add_var frame.new_vars

    let assert_frame solver tt frame next_frame assertions =
        let add_expr e =
            ignore (solver#append_expr (map_frame_vars frame next_frame e)) in
        List.iter add_expr assertions

end


type node_kind_t = Leaf | Intermediate


let kind_s = function
    | Leaf -> "Leaf"
    | Intermediate -> "Intermediate"


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
        method top_frame: F.frame_t

        
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

        (** This function is called when a new tree node is entered.
            The functions enter/leave are called in the depth-first order.

            @param node_kind indicates whether the node is
                leaf (Leaf), or not (Intermediate)
         *)
        method enter_node: node_kind_t -> unit

        (**
         * Check, whether the property is violated in the current frame.
         * The actual check can be postponed, depending on the actual tactic
         * implementation. The only guarantee is that if the property is violated
         * for some tree node, then it will be eventually reported for some call
         * of check_property
         *
         * @form ltl propositional formula
         *)
        method check_property: Spin.token SpinIr.expr -> bool

        (** This function is called when a tree node is left.
            The functions enter/leave are called in the depth-first order.

            @param node_kind indicates whether the node is
                leaf (Leaf), or not (Intermediate)
         *)
        method leave_node: node_kind_t -> unit

        (* Enter the new context, also called a branch in the schema tree.
           The functions enter/leave are called in the depth-first order.
         *)
        method enter_context: unit

        (* Leave the context, also called a branch in the schema tree.
           The functions enter/leave are called in the depth-first order.
         *)
        method leave_context: unit
    end


type frame_stack_elem_t =
    | Frame of F.frame_t    (* just a frame *)
    | Node of int           (* a node marker *)


class tree_tac_t (rt: Runtime.runtime_t) (tt: SpinIr.data_type_tab): tac_t =
    object(self)
        val mutable m_frames = []
        val mutable m_depth  = 0
        
        method top_frame =
            let rec find = function
                | (Frame f) :: _ -> f
                | (Node _) :: tl -> find tl
                | _ -> raise (Failure "Frame stack is empty")
            in
            find m_frames
 
        method private top2 =
            let rec find = function
                | (Frame f) :: tl -> f, tl
                | (Node _) :: tl -> find tl
                | _ -> raise (Failure "Frame stack is empty")
            in
            let top, tl = find m_frames in
            let prev, _ = find tl in
            top, prev

        method push_frame f =
            F.declare_frame rt#solver tt f;
            m_frames <- (Frame f) :: m_frames

        method assert_top assertions =
            let frame = self#top_frame in
            F.assert_frame rt#solver tt frame frame assertions

        method assert_top2 assertions =
            let top, prev = self#top2 in
            F.assert_frame rt#solver tt prev top assertions

        method enter_node kind =
            let slv = rt#solver in
            let k_s = kind_s kind in
            slv#comment
                (sprintf "push@%d: check_node[%s] at frame %d"
                    m_depth k_s self#top_frame.F.no);
            slv#push_ctx;
            m_depth <- m_depth + 1

        method check_property form =
            false

        method leave_node kind =
            let slv = rt#solver in
            let k_s = kind_s kind in
            m_depth <- m_depth - 1;
            slv#comment
                (sprintf "pop@%d: check_node[%s] at frame %d"
                    m_depth k_s self#top_frame.F.no);
            slv#pop_ctx


        method enter_context =
            let slv = rt#solver in
            slv#push_ctx;
            slv#comment
                (sprintf "push@%d: enter_context: potential milestones at frame %d"
                        m_depth self#top_frame.F.no)

        method leave_context =
            let slv = rt#solver in
            slv#comment (sprintf "pop@%d: leave_context at frame %d"
                m_depth self#top_frame.F.no);
            slv#pop_ctx

    end


let not_redundant_action = function
        | BinEx (Spin.EQ, UnEx (Spin.NEXT, Var l), Var r) ->
                l#get_name <> r#get_name
        | _ -> true


let accelerate_expr accel_var e =
    let rec f = function
        | UnEx (t, e) ->
                UnEx (t, f e)

        | BinEx (t, l, r) ->
                BinEx (t, f l, f r)

        | IntConst i ->
                if i = 1
                then Var accel_var
                else BinEx (Spin.MULT, IntConst i, Var accel_var)

        | e -> e
    in
    f e


let collect_next_vars e =
    let rec f set = function
        | UnEx (Spin.NEXT, Var v) -> IntSet.add v#id set
        | UnEx (_, e) -> f set e
        | BinEx (_, l, r) -> f (f set l) r
        | _ -> set
    in
    f IntSet.empty e


type var_kind_t = KWarp | KGlob | KLoc | KUndef


let demangle v =    
    let name_re =
        Str.regexp "F\\([0-9]+\\)_\\(g_\\|at_\\|\\)\\([_A-Za-z][_A-Za-z0-9]*\\)"
    in
    let name = v#get_name in
    if Str.string_match name_re name 0
    then begin
        let tp = Str.matched_group 2 name in
        let short = Str.matched_group 3 name in
        match tp with
        | "" -> (KWarp, short)
        | "g_" -> (KGlob, short)
        | "at_" -> (KLoc, short)
        | _ -> (KUndef, name)
    end
    else (KUndef, name)


let get_counterex rt sk form_name frame_hist =
    let reverse no v m = StrMap.add v#get_name no m in
    let revmap = IntMap.fold reverse sk.Sk.loc_vars StrMap.empty in
    let get_vars vars =
        let query = rt#solver#get_model_query in
        List.iter (fun v -> ignore (Smt.Q.try_get query (Var v))) vars;
        let new_query = rt#solver#submit_query query in
        let map v =
            match Smt.Q.try_get new_query (Var v) with
                | Smt.Q.Result e ->
                    let k, n = demangle v in
                    (k, n, e)
                | Smt.Q.Cached ->
                    raise (Failure "Unexpected Cached")
        in
        List.map map vars
    in
    let p is_init_frame out (k, n, e) =
        match k with
        | KLoc ->
                let locno = StrMap.find n revmap in
                let loc = List.nth sk.Sk.locs locno in
                let pair locvar locval = sprintf "%s:%d" locvar#get_name locval
                in
                let idx = List.map2 pair sk.Sk.locals loc |> str_join "][" in
                if not is_init_frame || e <> IntConst 0
                then fprintf out " K[%s] := %s;" idx (SpinIrImp.expr_s e)

        | _ ->
                fprintf out " %s := %s;" n (SpinIrImp.expr_s e)
    in
    let rec each_frame out num = function
        | [] -> ()

        | f :: tl ->
            let vals = get_vars (f.F.accel_v :: f.F.new_vars) in
            let (_, _, accel), other = List.hd vals, List.tl vals in
            let new_num =
                if f.F.no = 0 || accel <> IntConst 0
                then begin
                    fprintf out "%4d (F%4d) x%2s: "
                        num f.F.no (SpinIrImp.expr_s accel);
                    List.iter (p (f.F.no = 0) out) other;
                    if f.F.no = 0
                    then fprintf out " K[*]: = 0;\n"
                    else fprintf out "\n";
                    1 + num
                end
                else num
            in
            each_frame out new_num tl
    in
    let fname = sprintf "cex-%s.trx" form_name in
    let out = open_out fname in
    fprintf out "----------------\n";
    fprintf out " Counterexample\n";
    fprintf out "----------------\n";
    rt#solver#set_need_model true;
    fprintf out "           ";
    List.iter (p false out) (get_vars sk.Sk.params);
    fprintf out "\n";
    each_frame out 0 frame_hist;
    fprintf out "----------------\n";
    fprintf out " Gute Nacht. Spokoinoy nochi.\n";
    rt#solver#set_need_model false;
    close_out out;
    printf "    > Saved counterexample to %s\n" fname


let display_depth depth is_last =
    if is_last
    then logtm INFO (sprintf "%s|" (String.make depth '/'))
    else logtm INFO (String.make (1 + depth) '/')


let check_tree rt tt sk bad_form on_leaf start_frame form_name deps tac tree =
    let each_rule is_milestone (frame, fs) rule_no =
        let rule = List.nth sk.Sk.rules rule_no in
        let src_loc_v = List.nth frame.F.loc_vars rule.Sk.src in
        let dst_loc_v = List.nth frame.F.loc_vars rule.Sk.dst in
        let actions = List.filter not_redundant_action rule.Sk.act in
        let next_shared =
            List.fold_left IntSet.union IntSet.empty
                (List.map collect_next_vars actions) in
        let is_new_f basev v =
            v#id = src_loc_v#id || v#id = dst_loc_v#id
                || IntSet.mem basev#id next_shared
        in
        let new_frame = F.advance_frame tt sk frame is_new_f in
        tac#push_frame new_frame;
        let move loc sign =
            let prev = List.nth frame.F.loc_vars loc in
            let next = List.nth new_frame.F.loc_vars loc in
            (* k'[loc] = k[loc] +/- accel *)
            BinEx (Spin.EQ, UnEx (Spin.NEXT, Var next),
                BinEx (sign, Var prev, Var new_frame.F.accel_v))
        in
        tac#assert_top2 [move rule.Sk.src Spin.MINUS];
        tac#assert_top2 [move rule.Sk.dst Spin.PLUS];

        let rule_guard =
            (* Milestone conditions are either:
                known a priori in a segment,
                or checked once for a milestone.
              Thus, check only non-milestone conditions
             *)
            PorBounds.D.non_milestones deps rule_no
        in
        let guard = (* if acceleration factor > 0 then guard *)
            BinEx (Spin.OR, BinEx (Spin.EQ, Var new_frame.F.accel_v, IntConst 0), rule_guard) in
        if rule_guard <> IntConst 1
        then tac#assert_top2 [guard];

        let accelerated =
            List.map (accelerate_expr new_frame.F.accel_v) actions in
        tac#assert_top2 accelerated;
        (new_frame, new_frame :: fs)
    in
    let rec sum_factors = function
        | [] -> IntConst 0
        | [frame] -> Var frame.F.accel_v
        | frame :: tl -> BinEx (Spin.PLUS, Var frame.F.accel_v, sum_factors tl)
    in
    let check_property frame_hist =
        rt#solver#comment "push: check_property";
        let stack_level = rt#solver#get_stack_level in
        
        rt#solver#push_ctx;
        rt#solver#comment "is segment bad?";
        if not (is_c_true bad_form)
        then tac#assert_top [bad_form];
        let err = rt#solver#check in
        if err (* print the counterexample *)
        then get_counterex rt sk form_name (List.rev frame_hist);

        rt#solver#comment "pop: check_property";
        rt#solver#pop_ctx;
        assert (stack_level = rt#solver#get_stack_level);
        err
    in
    let rec check_node depth frame_hist
            { T.pre_rule_set; T.pre_cond; T.segment; T.succ } =
        (* check the context *)
        let nil_context = is_rule_set_empty pre_rule_set in
        let start_frame = List.hd frame_hist in
        tac#enter_context;

        (* only one of the rules should actually fire *)
        let cond_frames =
            if not nil_context
            then begin
                let _, _, milestone_expr, _ = pre_cond in
                (* assert that the milestone is unlocked *)
                tac#assert_top [milestone_expr];
                (* and this effects into firing of the following rules *)
                let cond_rules =
                    PorBounds.unpack_rule_set pre_rule_set deps.D.full_segment in
                let _, new_frames =
                    List.fold_left (each_rule true) (start_frame, []) cond_rules in
                let constr = BinEx (Spin.EQ, IntConst 1, sum_factors new_frames) in
                tac#assert_top [constr];
                new_frames @ frame_hist
            end
            else frame_hist
        in

        (* push the segment rules *)
        let node = (if succ = [] then Leaf else Intermediate) in
        let stack_level = rt#solver#get_stack_level in
        let frame = List.hd cond_frames in
        tac#enter_node node;
        display_depth depth true;
        let seg = PorBounds.unpack_rule_set segment deps.D.full_segment in
        let endf, end_hist =
            List.fold_left (each_rule false) (frame, cond_frames) seg in
        let err = check_property end_hist in

        if node = Leaf
        then begin
            on_leaf (endf.F.no + 1)
        end;

        (* and check the subtree *)
        let each_succ err s =
            if err then err else check_node (1 + depth) end_hist s
        in
        let res = List.fold_left each_succ err succ in
        tac#leave_node node;
        assert (stack_level = rt#solver#get_stack_level);

        tac#leave_context;
        res
    in
    check_node 0 [start_frame] tree


let extract_spec type_tab s =
    match Ltl.classify_spec type_tab s with
    | Ltl.CondSafety (init, bad) -> (init, bad)
    | _ ->
        let m = sprintf "unsupported LTL formula: %s" (SpinIrImp.expr_s s) in
        raise (Ltl.Ltl_error m)


let is_error_tree rt tt sk on_leaf form_name ltl_form deps tree =
    let init_form, bad_form = extract_spec tt ltl_form in
    if is_c_false bad_form
    then raise (Failure "Bad condition is trivially false");

    rt#solver#push_ctx;
    rt#solver#set_need_model true;

    let ntt = tt#copy in
    let tac = new tree_tac_t rt ntt in
    let initf = F.init_frame ntt sk in
    tac#push_frame initf;
    tac#assert_top sk.Sk.inits;
    rt#solver#comment "initial constraints from the spec";
    if is_c_false init_form
    then raise (Failure "Initial condition is trivially false");
    if not (is_c_true init_form)
    then tac#assert_top [init_form];

    let err = check_tree rt ntt sk bad_form on_leaf initf form_name deps tac tree in
    rt#solver#set_need_model false;
    rt#solver#pop_ctx;
    err

