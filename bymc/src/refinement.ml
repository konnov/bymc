(* The refinement for our counter abstraction *)

open Printf
open Str

open Accums
open Spin
open SpinIr
open SpinIrImp
open Smt
open Debug

exception Refinement_error of string

let pred_reach = "p"
let pred_recur = "r"

let parse_spin_trail filename dom data_ctx ctr_ctx_tbl prog =
    let last_id = ref 0 in
    let rev_map = Hashtbl.create 10 in (* from ids to abstract states *)
    let r = " *\\([A-Za-z0-9]+\\):GS{[0-9-]*->[0-9-]*:\\(\\([{}0-9,]\\)*\\)}.*" in
    let state_re = Str.regexp r in
    let loop_re = Str.regexp ".*<<<<<START OF CYCLE>>>>>.*" in
    let rev_rows = ref [] in
    let loop_pos = ref 0 in
    let fin = open_in filename in
    begin
        (* parse strings like this: P:GS{0->1:{1,1,0,1,0,0,0,0,0,0,0},0,0} *)
        try
            while true do
                let line = input_line fin in
                if Str.string_match state_re line 0
                then begin
                    let proc = Str.matched_group 1 line in
                    let no_clutter s = global_replace (regexp "[{}]") "" s in
                    let group = no_clutter (Str.matched_group 2 line) in
                    let strs = (Str.split (Str.regexp ",") group) in
                    let ints = List.map int_of_string strs in
                    rev_rows := (proc, ints) :: !rev_rows;
                    if may_log DEBUG
                    then begin
                        List.iter (fun i -> printf "%d " i) ints;
                        printf "\n"
                    end
                end else
                if Str.string_match loop_re line 0
                then loop_pos := (List.length !rev_rows)
                else (printf "WARNING: no match for %s\n" line)
            done
        with End_of_file ->
            close_in fin;
    end;
    printf "loop starts with %d\n" !loop_pos;
    let rows = List.rev !rev_rows in
    let num_rows = List.length rows in

    let int_to_expr c_ctx pos value =
        let id = !last_id in
        last_id := !last_id + 1;
        if pos < c_ctx#get_ctr_dim
        then
            let arr_ctr_elem = BinEx (ARR_ACCESS, Var c_ctx#get_ctr, Const pos) in
            let e = dom#expr_is_concretization arr_ctr_elem value in
            (* constraint no, concrete expression, abstract expression *)
            (id, e, BinEx (EQ, arr_ctr_elem, Const value))
        else let shared_no = pos - c_ctx#get_ctr_dim in
            let shared = (Program.get_shared prog) in
            let v = Var (List.nth shared shared_no) in
            let e =
                if data_ctx#must_keep_concrete v
                then dom#expr_is_concretization v value
                else BinEx (EQ, v, Const value) (* keep it abstract *)
            in
            (* constraint no, concrete expression, abstract expression *)
            (id, e, BinEx (EQ, v, Const value))
    in
    let row_to_exprs (state_no: int) ((proc, row): string * int list)
            : string * token stmt list =
        let c_ctx = ctr_ctx_tbl#get_ctx_by_abbrev proc in
        let map_one pos value =
            let id, conc_ex, abs_ex = int_to_expr c_ctx pos value in
            Hashtbl.add rev_map id (state_no, abs_ex);
            Expr (id, conc_ex) in
        (* a list of concrete constraints on each column of the row *)
        (proc, List.map2 map_one (range 0 (List.length row)) row)
    in
    let prefix_asserts = List.map2 row_to_exprs (range 0 num_rows) rows in
    let loop_asserts = list_sub prefix_asserts !loop_pos (num_rows - !loop_pos) in
    (prefix_asserts, loop_asserts, rev_map)


(* don't touch symbolic variables --- they are the parameters! *)
let map_to_in v = if v#is_symbolic then v else v#copy (v#get_name ^ "_IN") ;;
let map_to_out v = if v#is_symbolic then v else v#copy (v#get_name ^ "_OUT") ;;
let map_to_step step v =
    if v#is_symbolic
    then v
    else v#copy (sprintf "S%d_%s" step v#get_name)


let stick_var map_fun v = Var (map_fun v)

let connect_steps tracked_vars step =
    let connect v =
        let ov = map_to_step step (map_to_out v) in
        let iv = map_to_step (step + 1) (map_to_in v) in
        BinEx (EQ, Var ov, Var iv) in
    list_to_binex AND (List.map connect tracked_vars)


(* the process is skipping the step, not moving *)
let skip_step local_vars step =
    let eq v =
        let iv = map_to_step step (map_to_in v) in
        let ov = map_to_step step (map_to_out v) in
        BinEx (EQ, Var ov, Var iv) in
    list_to_binex AND (List.map eq local_vars)


let create_path proc xducer local_vars shared_vars when_moving n_steps =
    let tracked_vars = local_vars @ shared_vars in
    let map_xducer n =
        let es = List.map expr_of_m_stmt xducer in
        List.map (map_vars (stick_var (map_to_step n))) es
    in
    (* different proctypes will not clash on their local variables as only
       one of them is taking at each point of time *)
    let move_or_skip is_moving step =
        if is_moving
        then map_xducer step
        else [skip_step local_vars step]
    in
    let xducers = List.concat
        (* the first element of when_moving represents a dummy element,
           showing the initial state. Skip it. *)
        (List.map2 move_or_skip (List.tl when_moving) (range 0 n_steps)) in
    let connections =
        List.map
            (connect_steps tracked_vars)
            (range 0 (n_steps - 1)) in
    xducers @ connections


let smt_append_bind solver rev_map smt_rev_map expr_stmt =
    match expr_stmt with
    | Expr (id, e) ->
        let smt_id = solver#append_expr e in
        (* Bind ids assigned to expressions by the solver to the ids
           of constraints retrieved from the model checker.
           Not all expressions correspond to the counter-example,
           thus, we add only those which do.
           *)
        if id >= 0 && (Hashtbl.mem rev_map id) then begin
            let s, abs_expr = Hashtbl.find rev_map id in
            log DEBUG (sprintf "map: %d -> %d %s\n" smt_id s (expr_s abs_expr));
            if solver#get_collect_asserts
            then Hashtbl.add smt_rev_map smt_id (Hashtbl.find rev_map id);
        end

    | _ -> ()


(* TODO: optimize it for the case of checking one transition only! *)
(* TODO: mark the case of replaying a path (not a transition) as experimental
         and remove it out from here, it is heavy *)
let simulate_in_smt solver prog ctr_ctx_tbl trail_asserts rev_map n_steps =
    let shared_vars = (Program.get_shared prog) in
    let type_tab = (Program.get_type_tab prog) in
    let smt_rev_map = Hashtbl.create (Hashtbl.length rev_map) in
    assert (n_steps < (List.length trail_asserts));
    let trail_asserts = list_sub trail_asserts 0 (n_steps + 1) in
    let append_one_assert proc shared state_no asrt =
        match asrt with
        | Expr (id, e) ->
            let new_e =
                if state_no = 0
                then map_vars
                    (fun v -> Var (map_to_step 0 (map_to_in v))) e
                else map_vars
                    (fun v -> Var (map_to_step (state_no - 1) (map_to_out v))) e
            in
            smt_append_bind solver rev_map smt_rev_map (Expr (id, new_e))

        | _ -> ()
    in
    let append_trail_asserts state_no (proc, asserts) =
        List.iter (append_one_assert proc shared_vars state_no) asserts
    in
    solver#push_ctx;
    (* project the trace to the names of processes taking steps *)
    let moving_procs = List.map (fun (p, _) -> p) trail_asserts in
    (* put asserts from the control flow graph *)
    log INFO (sprintf 
        "    collecting declarations and xducer asserts (%d xducers)..."
        (List.length (Program.get_procs prog)));
    flush stdout;
    let proc_asserts proc =
        let c_ctx = ctr_ctx_tbl#get_ctx proc#get_name in
        let proc_xd = proc#get_stmts in
        let when_moving = List.map (fun p -> p = c_ctx#abbrev_name) moving_procs
        in
        let local_vars = [c_ctx#get_ctr] in
        create_path c_ctx#abbrev_name proc_xd local_vars shared_vars when_moving n_steps in
    let xducer_asserts =
        List.concat (List.map proc_asserts (Program.get_procs prog)) in
    let decls = expr_list_used_vars xducer_asserts in

    log INFO (sprintf "    appending %d declarations..."
        (List.length decls)); flush stdout;
    let append_def v =
        solver#append_var_def v (type_tab#get_type v)
    in
    List.iter append_def decls;
    log INFO (sprintf "    appending %d transducer asserts..."
        (List.length xducer_asserts)); flush stdout;
    List.iter (fun e -> let _ = solver#append_expr e in ()) xducer_asserts;
    log INFO (sprintf "    appending %d trail asserts..."
        (List.length trail_asserts)); flush stdout;
    (* put asserts from the counter example *)
    List.iter2 append_trail_asserts (range 0 (n_steps + 1)) trail_asserts;
    log INFO "    waiting for SMT..."; flush stdout;
    let result = solver#check in
    solver#pop_ctx;
    (result, smt_rev_map)


let parse_smt_evidence prog solver =
    let vals = Hashtbl.create 10 in
    let lines = solver#get_evidence in
    let aliases = Hashtbl.create 5 in
    let is_alias full_name = Hashtbl.mem aliases full_name in
    let add_alias full_name step name dir =
        Hashtbl.add aliases full_name (step, name, dir) in
    let get_alias full_name = Hashtbl.find aliases full_name in
    let param_re = Str.regexp "(= \\([a-zA-Z0-9]+\\) \\([-0-9]+\\))" in
    let var_re =
        Str.regexp "(= S\\([0-9]+\\)_\\([_a-zA-Z0-9]+\\)_\\(IN\\|OUT\\) \\([-0-9]+\\))"
    in
    let arr_re =
        Str.regexp "(= (S\\([0-9]+\\)_\\([_a-zA-Z0-9]+\\)_\\([A-Z0-9]+\\) \\([0-9]+\\)) \\([-0-9]+\\))"
    in
    let alias_re =
        Str.regexp ("(= S\\([0-9]+\\)_\\([_a-zA-Z0-9]+\\)_\\(IN\\|OUT\\) "
            ^ "S\\([0-9]+_[_a-zA-Z0-9]+_[A-Z0-9]+\\))") in
    let add_state_expr state expr =
        if not (Hashtbl.mem vals state)
        then Hashtbl.add vals state [expr]
        else Hashtbl.replace vals state (expr :: (Hashtbl.find vals state))
    in
    let parse_line line =
        if Str.string_match var_re line 0
        then begin
            (* (= S0_nsnt_OUT 1) *)
            let step = int_of_string (Str.matched_group 1 line) in
            let name = (Str.matched_group 2 line) in
            let dir = (Str.matched_group 3 line) in
            (* we support ints only, don't we? *)
            let value = int_of_string (Str.matched_group 4 line) in
            let state = if dir = "IN" then step else (step + 1) in
            let e = BinEx (ASGN, Var (new_var name), Const value) in
            if List.exists
                (fun v -> v#get_name = name) (Program.get_shared prog)
            then add_state_expr state e;
        end else if Str.string_match arr_re line 0
        then begin
            (* (= (S0_bymc_kP_IN 11) 0) *)
            let s = int_of_string (Str.matched_group 1 line) in
            let n = (Str.matched_group 2 line) in
            let d = (Str.matched_group 3 line) in
            let full = sprintf "%d_%s_%s" s n d in
            let step, name, dir =
                if is_alias full then get_alias full else s, n, d in
            let idx = int_of_string (Str.matched_group 4 line) in
            (* we support ints only, don't we? *)
            let value = int_of_string (Str.matched_group 5 line) in
            let state = if dir = "IN" then step else (step + 1) in
            let e = BinEx (ASGN,
                BinEx (ARR_ACCESS, Var (new_var name), Const idx),
                Const value) in
            if dir = "IN" || dir = "OUT"
            then add_state_expr state e; (* and ignore auxillary arrays *)
        end else if Str.string_match alias_re line 0
        then begin
            (* (= S0_bymc_kP_OUT S0_bymc_kP_Y2) *)
            let target = (Str.matched_group 4 line) in
            let step = int_of_string (Str.matched_group 1 line) in
            let name = (Str.matched_group 2 line) in
            let dir = (Str.matched_group 3 line) in
            add_alias target step name dir
        end else if Str.string_match param_re line 0
        then begin
            (* (= T 2) *)
            let name = (Str.matched_group 1 line) in
            let value = int_of_string (Str.matched_group 2 line) in
            add_state_expr 0 (BinEx (ASGN, Var (new_var name), Const value))
        end
    in
    List.iter parse_line lines;
    let cmp e1 e2 =
        let comp_res = match e1, e2 with
        | BinEx (ASGN, Var v1, Const k1),
          BinEx (ASGN, Var v2, Const k2) ->
              let r = String.compare v1#get_name v2#get_name in
              if r <> 0 then r else (k1 - k2)
        | BinEx (ASGN, BinEx (ARR_ACCESS, Var a1, Const i1), Const k1),
          BinEx (ASGN, BinEx (ARR_ACCESS, Var a2, Const i2), Const k2) ->
                let r = String.compare a1#get_name a2#get_name in
                if r <> 0
                then r
                else if i1 <> i2
                then i1 - i2
                else k1 - k2
        | BinEx (ASGN, BinEx (ARR_ACCESS, Var a1, Const i1), _),
          BinEx (ASGN, Var v2, _) ->
                -1 (* arrays go first *)
        | BinEx (ASGN, Var v1, _),
          BinEx (ASGN, BinEx (ARR_ACCESS, Var a2, Const i2), _) ->
                1 (* arrays go first *)
        | _ -> raise (Failure
            (sprintf "Incomparable: %s and %s" (expr_s e1) (expr_s e2)))
        in
        comp_res
    in
    let new_tbl = Hashtbl.create (Hashtbl.length vals) in
    Hashtbl.iter
        (fun k vs -> Hashtbl.add new_tbl k (list_sort_uniq cmp vs))
        vals;
    new_tbl


(* group an expression in a sorted valuation *)
let pretty_print_exprs exprs =
    let last_arr = ref "" in
    let last_idx = ref (-1) in
    let start_arr arr idx = 
        last_arr := arr#get_name;
        last_idx := idx - 1;
        printf "%s = { " !last_arr
    in
    let stop_arr () = 
        printf "} ";
        last_arr := ""
    in
    let pp = function
        | BinEx (ASGN, BinEx (ARR_ACCESS, Var arr, Const idx), Const value) ->
                if !last_arr <> "" && !last_arr <> arr#get_name
                then stop_arr ();
                if !last_arr <> arr#get_name
                then start_arr arr idx;
                if (!last_idx >= idx)
                then raise (Failure
                    (sprintf "Met %s[%d] = %d after %s[%d]"
                        arr#get_name idx value arr#get_name !last_idx));
                (* fill the gaps in indices *)
                List.iter (fun _ -> printf "_ ") (range !last_idx (idx - 1));
                (* print the value *)
                printf "%d " value;
                last_idx := idx

        | BinEx (ASGN, Var var, Const value) ->
                if !last_arr <> ""
                then stop_arr ();
                printf "%s = %d " var#get_name value

        | _ -> ()
    in
    List.iter pp exprs


let find_max_pred prefix = 
    let re = Str.regexp (".*bit bymc_" ^ prefix ^ "\\([0-9]+\\) = 0;.*") in
    let read_from_file () =
        let cin = open_in "cegar_decl.inc" in
        let stop = ref false in
        let max_no = ref (-1) in
        while not !stop do
            try
                let line = input_line cin in
                if Str.string_match re line 0
                then
                    let no = int_of_string (Str.matched_group 1 line) in
                    max_no := max !max_no no
            with End_of_file ->
                close_in cin;
                stop := true
        done;
        !max_no
    in
    try read_from_file ()
    with Sys_error _ -> (-1)


let intro_new_pred prefix (* pred_reach or pred_recur *) =
    let max_no = find_max_pred prefix in
    let pred_no = 1 + max_no in
    let cout = open_out_gen [Open_append] 0666 "cegar_decl.inc" in
    fprintf cout "bit bymc_%s%d = 0;\n" prefix pred_no;
    close_out cout;
    pred_no


(* retrieve unsat cores, map back corresponding constraints on abstract values,
   partition the constraints into two categories:
       before the transition, after the transition
 *)
let retrieve_unsat_cores solver smt_rev_map src_state_no =
    let core_ids = solver#get_unsat_cores in
    log INFO (sprintf "Detected %d unsat core ids\n" (List.length core_ids));
    let filtered = List.filter (fun id -> Hashtbl.mem smt_rev_map id) core_ids
    in
    let mapped = List.map (fun id -> Hashtbl.find smt_rev_map id) filtered in
    let pre, post = List.partition (fun (s, e) -> s = src_state_no) mapped in
    let b2 (s, e) = sprintf "(%s)" (expr_s e) in
    let pre, post = List.map b2 pre, List.map b2 post in
    (pre, post)


let refine_spurious_step solver smt_rev_map src_state_no =
    let pre, post = retrieve_unsat_cores solver smt_rev_map src_state_no in
    let pred_no = intro_new_pred pred_reach in

    if pre = [] && post = []
    then raise (Failure "Cannot refine: unsat core is empty");

    let cout = open_out_gen [Open_append] 0666 "cegar_pre.inc" in
    let preex = if pre = [] then "1" else (String.concat " && " pre) in
    fprintf cout "bymc_p%d = (%s);\n" pred_no preex;
    close_out cout;

    let cout = open_out_gen [Open_append] 0666 "cegar_post.inc" in
    fprintf cout "bymc_spur = (bymc_p%d && (%s)) || bymc_spur;\n"
        pred_no (String.concat " && " post);
    close_out cout


let print_vass_trace prog solver num_states = 
    printf "Here is a CONCRETE trace in VASS violating the property.\n";
    printf "State 0 gives concrete parameters.\n\n";
    let vals = parse_smt_evidence prog solver in
    let print_st i =
        printf "%d: " i;
        pretty_print_exprs (Hashtbl.find vals i);
        printf "\n";
    in
    List.iter (print_st) (range 0 num_states)


let is_loop_state_fair_by_step solver prog ctr_ctx_tbl rev_map fairness
        (proc_abbrev, state_asserts) state_num =
    solver#comment ("is_loop_state_fair_by_step: " ^ (expr_s fairness));
    let new_rev_map = Hashtbl.copy rev_map in
    let next_id = 1 + (List.fold_left max 0 (hashtbl_keys rev_map)) in
    (* add the assumption that state 0 is fair! *)
    Hashtbl.add new_rev_map next_id (0, fairness);
    solver#push_ctx;
    solver#set_collect_asserts true;
    solver#set_need_evidence true;

    (* State 0 is fair and it is a concretization of the abstract state
       kept in state_asserts. State 1 is anything we can go to via
       the transducer. *)
    let step_asserts =
        [(proc_abbrev, state_asserts @ [Expr(fresh_id (), fairness)]);
            (proc_abbrev, [])] in

    (* simulate one step *)
    let res, smt_rev_map =
        (simulate_in_smt solver prog ctr_ctx_tbl step_asserts rev_map 1) in

    (* collect unsat cores if there is no step *)
    let _, core_exprs =
        if not res
        then retrieve_unsat_cores solver smt_rev_map (-1)
        else [], []
    in
    let core_exprs_s = (String.concat " && " core_exprs) in

    if res then begin
        log INFO (sprintf
            "State %d in the loop is fair. See trace below." state_num);
        print_vass_trace prog solver 2;
    end else 
        printf "core_exprs_s: %s\n" core_exprs_s;

    solver#set_collect_asserts false;
    solver#set_need_evidence false;
    solver#pop_ctx;
    res, core_exprs_s


let check_loop_unfair solver prog ctr_abs_tbl
        rev_map fair_forms inv_forms loop_asserts =
    let check_one ff = 
        log INFO ("  Checking if the loop is fair..."); flush stdout;
        let check_and_collect_cores (all_sat, all_core_exprs_s, num) state_asserts =
            let sat, core_exprs_s =
                is_loop_state_fair_by_step solver prog ctr_abs_tbl
                    rev_map ff state_asserts num
            in
            (all_sat || sat, core_exprs_s :: all_core_exprs_s, (num + 1))
        in
        let sat, exprs, _ =
            List.fold_left check_and_collect_cores (false, [], 0) loop_asserts
        in
        if not sat
        then begin
            let pred_no = intro_new_pred pred_recur in
            let cout = open_out_gen [Open_append] 0666 "cegar_post.inc" in
            fprintf cout "bymc_r%d = (%s);\n" pred_no (String.concat " || " exprs);
            close_out cout;
        end;
        not sat
    in
    List.fold_left (||) false (List.map check_one fair_forms)
