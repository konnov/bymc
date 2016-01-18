(**
 Encode path schemas and check them with an SMT solver.

 @author Igor Konnov, 2014-2016
 *)

open Batteries
open BatPrintf

open Accums
open Debug
open PorBounds
open SpinIr
open SymbSkel

open SchemaSmt


let kind_s = function
    | Leaf -> "Leaf"
    | Intermediate -> "Intermediate"
    | LoopStart -> "LoopStart" (* not required for safety *)

(**

 Auxillary functions for the SMT encoding.

 *)
module B = struct
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
end 


let write_counterex ?(start_no=0) solver sk out frame_hist =
    let reverse no v m = StrMap.add v#get_name no m in
    let revmap = IntMap.fold reverse sk.Sk.loc_vars StrMap.empty in
    let get_vars vars =
        let query = solver#get_model_query in
        List.iter (fun v -> ignore (Smt.Q.try_get query (Var v))) vars;
        let new_query = solver#submit_query query in
        let map v =
            match Smt.Q.try_get new_query (Var v) with
                | Smt.Q.Result e ->
                    let k, n = B.demangle v in
                    (k, n, e)
                | Smt.Q.Cached ->
                    raise (Failure "Unexpected Cached")
        in
        List.map map vars
    in
    let p is_init_frame out (k, n, e) =
        match k with
        | B.KLoc ->
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
    let each_frame out (val_map, num) f =
        let vals = get_vars (f.F.accel_v :: f.F.new_vars) in
        let add map (_, name, value) =
            StrMap.add name value map
        in
        let new_val_map = BatList.fold_left add val_map (List.tl vals) in
        let (_, _, accel), other = List.hd vals, List.tl vals in
        if f.F.no = 0 || accel <> IntConst 0
        then begin
            fprintf out "%4d (F%4d) x%2s: "
                (start_no + num) f.F.no (SpinIrImp.expr_s accel);
            List.iter (p (f.F.no = 0) out) other;
            if other = [] && f.F.no <> 0
            then fprintf out " <nop>";
            if f.F.no = 0
            then fprintf out " K[*] := 0;\n"
            else fprintf out "\n";
            (new_val_map, 1 + num)
        end
        else (new_val_map, num)
    in
    solver#set_need_model true;
    List.iter (p false out) (get_vars sk.Sk.params);
    fprintf out "\n";
    let val_map, nprinted =
        (* print the frames *)
        BatList.fold_left (each_frame out) (StrMap.empty, 0) frame_hist
    in
    (* print the final values *)
    let pr_loc no =
        let locvar = Sk.locvar sk no in
        if StrMap.mem locvar#get_name val_map
        then let value = StrMap.find locvar#get_name val_map in
            p false out (B.KLoc, locvar#get_name, value)
    in
    let pr_shared v =
        if StrMap.mem v#get_name val_map
        then p false out (B.KGlob, v#get_name, StrMap.find v#get_name val_map)
    in
    fprintf out "****************\n";
    List.iter pr_shared sk.Sk.shared;
    List.iter pr_loc (range 0 sk.Sk.nlocs);
    fprintf out "\n";
    nprinted


let dump_counterex_to_file solver sk form_name frame_hist =
    let fname = sprintf "cex-%s.trx" form_name in
    let out = open_out fname in
    fprintf out "----------------\n";
    fprintf out " Counterexample\n";
    fprintf out "----------------\n";
    fprintf out "           ";
    ignore (write_counterex solver sk out frame_hist);
    fprintf out "----------------\n";
    fprintf out " Gute Nacht. Spokoinoy nochi. Laku noch.\n";
    close_out out;
    printf "    > Saved counterexample to %s\n" fname;
    fname

(*******************************************************************)

type frame_stack_elem_t =
    | Frame of F.frame_t    (* just a frame *)
    | Node of int           (* a node marker *)
    | Context of int        (* a context marker *)


(**
 A simple implementation of tac_t with SMT.
 *)
class tree_tac_t (rt: Runtime.runtime_t) (tt: SpinIr.data_type_tab) =
    object(self)
        inherit tac_t

        val mutable m_frames = []
        val mutable m_depth  = 0
        
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
            F.declare_frame rt#solver tt f;
            m_frames <- (Frame f) :: m_frames

        method assert_top assertions =
            let frame = self#top in
            F.assert_frame rt#solver tt frame frame assertions

        method assert_top2 assertions =
            let top, prev = self#top2 in
            F.assert_frame rt#solver tt prev top assertions

        method assert_frame_eq sk loop_frame =
            rt#solver#comment (sprintf "assert_frame_eq this %d" loop_frame.F.no);
            let loc_vars = List.map (Sk.locvar sk) (range 0 sk.Sk.nlocs) in
            F.assert_frame_eq rt#solver tt loc_vars loop_frame self#top;
            F.assert_frame_eq rt#solver tt sk.Sk.shared loop_frame self#top

        method enter_node kind =
            let slv = rt#solver in
            let k_s = kind_s kind in
            let frame_no = self#top.F.no in
            slv#comment (sprintf "push@%d: enter_node[%s] at frame %d"
                m_depth k_s frame_no);
            slv#push_ctx;
            m_frames <- (Node frame_no) :: m_frames;
            m_depth <- m_depth + 1

        method check_property form error_fun =
            let slv = rt#solver in
            slv#comment "push: check_property";
            let stack_level = slv#get_stack_level in
            
            if SpinIr.is_c_false form
            then false  (* it never holds *)
            else begin
                slv#push_ctx;
                slv#comment "is segment bad?";
                if not (is_c_true form)
                then self#assert_top [form];
                let err = slv#check in
                if err
                then error_fun self#frame_hist;
                slv#comment "pop: check_property";
                slv#pop_ctx;
                assert (stack_level = slv#get_stack_level);
                err
            end

        method leave_node kind =
            let rec unroll = function
                | (Node n) :: l -> (n, l)
                | _ :: l -> unroll l
                | [] -> (0, [])
            in
            let slv = rt#solver in
            let k_s = kind_s kind in
            m_depth <- m_depth - 1;
            let frame_no, old_frames = unroll m_frames in
            m_frames <- old_frames;
            assert (frame_no = self#top.F.no);
            slv#comment
                (sprintf "pop@%d: leave_node[%s] at frame %d"
                    m_depth k_s self#top.F.no);
            slv#pop_ctx


        method enter_context =
            let slv = rt#solver in
            slv#push_ctx;
            let frame_no = self#top.F.no in
            slv#comment
                (sprintf "push@%d: enter_context: potential milestones at frame %d"
                        m_depth frame_no);
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
            let slv = rt#solver in
            slv#comment (sprintf "pop@%d: leave_context at frame %d"
                m_depth frame_no);
            slv#pop_ctx


        method push_rule deps sk rule_no =
            let frame = self#top in
            let rule = List.nth sk.Sk.rules rule_no in
            let src_loc_v = List.nth frame.F.loc_vars rule.Sk.src in
            let dst_loc_v = List.nth frame.F.loc_vars rule.Sk.dst in
            let actions = List.filter B.not_redundant_action rule.Sk.act in
            let next_shared =
                List.fold_left IntSet.union IntSet.empty
                    (List.map B.collect_next_vars actions) in
            let is_new_f basev v =
                ((v#id = src_loc_v#id || v#id = dst_loc_v#id)
                    && rule.Sk.src <> rule.Sk.dst)
                    || IntSet.mem basev#id next_shared
            in
            let new_frame = F.advance_frame tt sk frame is_new_f in
            self#push_frame new_frame;
            let move loc sign =
                let prev = List.nth frame.F.loc_vars loc in
                let next = List.nth new_frame.F.loc_vars loc in
                (* k'[loc] = k[loc] +/- accel *)
                BinEx (Spin.EQ, UnEx (Spin.NEXT, Var next),
                    BinEx (sign, Var prev, Var new_frame.F.accel_v))
            in
            if rule.Sk.src <> rule.Sk.dst (* don't do it for self-loops *)
            then begin
                self#assert_top2 [move rule.Sk.src Spin.MINUS];
                self#assert_top2 [move rule.Sk.dst Spin.PLUS];
            end;

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
            then self#assert_top2 [guard];

            let accelerated =
                List.map (B.accelerate_expr new_frame.F.accel_v) actions in
            self#assert_top2 accelerated

    end


let display_depth depth is_last =
    if is_last
    then logtm INFO (sprintf "%s|" (String.make depth '/'))
    else logtm INFO (String.make (1 + depth) '/')


let check_static_tree rt tt sk bad_form on_leaf form_name deps tac tree =
    let no_optimization =
        (Options.get_plugin_opt rt#caches#options "schema.tech") <> Some "cav15-opt"
    in
    let rec check_node depth
            { T.pre_rule_set; T.pre_cond; T.segment; T.succ } =
        (* check the context *)
        let nil_context = is_rule_set_empty pre_rule_set in
        tac#enter_context;

        (* it is sufficient, if only one of the rules fires,
           but for now we do not enforce this constraint. *)
        if not nil_context
        then begin
            let _, _, milestone_expr, _ = pre_cond in
            (* assert that the milestone is unlocked *)
            tac#assert_top [milestone_expr];
            (* and this effects into firing of the following rules *)
            let cond_rules =
                PorBounds.unpack_rule_set pre_rule_set deps.D.full_segment in
            List.iter (tac#push_rule deps sk) cond_rules;
            (* REMOVED: why having more constraints than necessary?
            (* only one rule fires *)
            let constr = BinEx (Spin.EQ, IntConst 1, sum_factors new_frames) in
            tac#assert_top [constr]
            *)
        end;

        (* push the segment rules *)
        let node = (if succ = [] then Leaf else Intermediate) in
        let stack_level = rt#solver#get_stack_level in
        tac#enter_node node;
        display_depth depth true;

        (* We overlooked the following natural optimization in the CAV'15
           submission: if the current segment is unreachable, then its branches
           are also unreachable -- prune the whole subtree.
         *)
        (* uncomment the following line, if you want to get
           the same behavior as in the CAV'15 paper *)
        let is_reachable = no_optimization || rt#solver#check in
        let is_error_found =
            if not is_reachable
            then false (* prune the subtree and do not report any error *)
            else begin (* check the property and the subtree *)
                let seg = PorBounds.unpack_rule_set segment deps.D.full_segment in
                List.iter (tac#push_rule deps sk) seg;
                let err =
                    tac#check_property bad_form
                        (fun hist -> ignore (dump_counterex_to_file rt#solver sk form_name hist))
                in
                if node = Leaf
                then begin
                    on_leaf (tac#top.F.no + 1)
                end;

                (* and check the subtree *)
                let each_succ err s =
                    if err then err else check_node (1 + depth) s
                in
                List.fold_left each_succ err succ
            end
        in
        tac#leave_node node;
        assert (stack_level = rt#solver#get_stack_level);

        tac#leave_context;
        is_error_found
    in
    check_node 0 tree


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

    let err = check_static_tree rt ntt sk bad_form on_leaf form_name deps tac tree in
    rt#solver#set_need_model false;
    rt#solver#pop_ctx;
    err

