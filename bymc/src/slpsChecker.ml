(* Encode regular expressions on paths and check them with an SMT solver.
 *
 * Igor Konnov, 2014
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
    let p out (k, n, e) =
        match k with
        | KLoc ->
                let locno = StrMap.find n revmap in
                let loc = List.nth sk.Sk.locs locno in
                let pair locvar locval = sprintf "%s:%d" locvar#get_name locval
                in
                let idx = List.map2 pair sk.Sk.locals loc |> str_join "][" in
                fprintf out " K[%s] := %s;" idx (SpinIrImp.expr_s e)

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
                    List.iter (p out) other;
                    fprintf out "\n";
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
    List.iter (p out) (get_vars sk.Sk.params);
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


let check_tree rt tt sk bad_form on_leaf start_frame form_name tree =
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
        F.declare_frame rt#solver tt new_frame;
        let move loc sign =
            let prev = List.nth frame.F.loc_vars loc in
            let next = List.nth new_frame.F.loc_vars loc in
            (* k'[loc] = k[loc] +/- accel *)
            BinEx (Spin.EQ, UnEx (Spin.NEXT, Var next),
                BinEx (sign, Var prev, Var new_frame.F.accel_v))
        in
        F.assert_frame rt#solver tt frame new_frame [move rule.Sk.src Spin.MINUS];
        F.assert_frame rt#solver tt frame new_frame [move rule.Sk.dst Spin.PLUS];

        let guard = (* if acceleration factor > 0 then guard *)
            BinEx (Spin.OR, BinEx (Spin.EQ, Var new_frame.F.accel_v, IntConst 0), rule.Sk.guard) in
        if is_milestone
        then
        begin
            match rule.Sk.guard with
            | IntConst 1 -> ()
            | _ -> F.assert_frame rt#solver tt frame new_frame [guard]
        end;

        let accelerated =
            List.map (accelerate_expr new_frame.F.accel_v) actions in
        F.assert_frame rt#solver tt frame new_frame accelerated;
        (new_frame, new_frame :: fs)
    in
    let rec sum = function
        | [] -> IntConst 0
        | [frame] -> Var frame.F.accel_v
        | frame :: tl -> BinEx (Spin.PLUS, Var frame.F.accel_v, sum tl)
    in
    let check_segment frame_hist frame seg =
        let endf, end_hist =
            List.fold_left (each_rule false) (frame, frame_hist) seg in
        rt#solver#comment "push: check_segment";
        let stack_level = rt#solver#get_stack_level in
        rt#solver#push_ctx;
        rt#solver#comment "is segment bad?";
        if not (is_c_false bad_form)
        then raise (Failure "Bad condition is trivially false");
        if not (is_c_true bad_form)
        then F.assert_frame rt#solver tt endf endf [bad_form];
        let err = rt#solver#check in
        if err (* print the counterexample *)
        then get_counterex rt sk form_name (List.rev end_hist);

        rt#solver#comment "pop: check_segment";
        rt#solver#pop_ctx;
        assert (stack_level = rt#solver#get_stack_level);
        endf, end_hist, err
    in
    let rec check_node depth frame_hist frame = function
        | T.Leaf seg ->
            rt#solver#comment (sprintf "push@%d: check_node[Leaf] at frame %d" depth frame.F.no);
            let stack_level = rt#solver#get_stack_level in
            rt#solver#push_ctx;
            rt#solver#comment "last segment";
            display_depth depth true;
            let endf, end_hist, err = check_segment frame_hist frame seg in
            rt#solver#comment (sprintf "pop@%d: check_node[Leaf] at frame %d" depth frame.F.no);
            rt#solver#pop_ctx;
            assert (stack_level = rt#solver#get_stack_level);

            on_leaf (endf.F.no + 1);
            err

        | T.Node (seg, branches) ->
            rt#solver#comment (sprintf "push@%d: check_node[Node] at frame %d" depth frame.F.no);
            let stack_level = rt#solver#get_stack_level in
            rt#solver#push_ctx;
            rt#solver#comment "next segment";
            display_depth depth false;
            let seg_endf, end_hist, err = check_segment frame_hist frame seg in

            let each_branch err b =
                check_branch (1 + depth) end_hist seg_endf err b in
            let res = List.fold_left each_branch err branches in
            rt#solver#comment (sprintf "pop@%d: check_node[Node] at frame %d" depth frame.F.no);
            rt#solver#pop_ctx;
            assert (stack_level = rt#solver#get_stack_level);
            res
    and check_branch depth frame_hist frame err br =
        if err
        then true
        else begin
            (* only one of the rules should actually fire *)
            let stack_level = rt#solver#get_stack_level in
            rt#solver#push_ctx;
            rt#solver#comment (sprintf "push@%d: check_branch: potential milestones at frame %d" depth frame.F.no);
            let endf, new_frames =
                List.fold_left (each_rule true) (frame, []) br.T.cond_rules in
            let constr = BinEx (Spin.EQ, IntConst 1, sum new_frames) in
            ignore (rt#solver#append_expr constr);
            let end_hist = new_frames @ frame_hist in
            let res = check_node (1 + depth) end_hist endf br.T.subtree in
            rt#solver#comment (sprintf "pop@%d: check_branch at frame %d" depth frame.F.no);
            rt#solver#pop_ctx;
            assert (stack_level = rt#solver#get_stack_level);
            res (* when SAT, an error is found *)
        end
    in
    check_node 0 [start_frame] start_frame tree


let extract_spec type_tab s =
    match Ltl.classify_spec type_tab s with
    | Ltl.CondSafety (init, bad) -> (init, bad)
    | _ ->
        let m = sprintf "unsupported LTL formula: %s" (SpinIrImp.expr_s s) in
        raise (Ltl.Ltl_error m)


let is_error_tree rt tt sk on_leaf form_name ltl_form tree =
    let init_form, bad_form = extract_spec tt ltl_form in
    rt#solver#push_ctx;
    rt#solver#set_need_model true;

    let ntt = tt#copy in
    let initf = F.init_frame ntt sk in
    F.declare_frame rt#solver ntt initf;
    F.assert_frame rt#solver ntt initf initf sk.Sk.inits;
    rt#solver#comment "initial constraints from the spec";
    if is_c_false init_form
    then raise (Failure "Initial condition is trivially false");
    if not (is_c_true init_form)
    then F.assert_frame rt#solver ntt initf initf [init_form];

    let err = check_tree rt tt sk bad_form on_leaf initf form_name tree in
    rt#solver#set_need_model false;
    rt#solver#pop_ctx;
    err

