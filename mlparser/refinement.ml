(* The refinement for our counter abstraction *)

open Printf;;

open Accums;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Smt;;
open Debug;;

let parse_spin_trail filename dom t_ctx ctr_ctx =
    let last_id = ref 0 in
    let rev_map = Hashtbl.create 10 in (* from ids to abstract states *)
    let state_re = Str.regexp ".*GS{[0-9-]*->[0-9-]*:\\(\\([0-9,]\\)*\\)}.*" in
    let int_lists = ref [] in
    let vec_len = ref 0 in
    let fin = open_in filename in
    begin
        try
            while true do
                let line = input_line fin in
                if Str.string_match state_re line 0
                then begin
                    let group = (Str.matched_group 1 line) in
                    let strs = (Str.split (Str.regexp ",") group) in
                    let ints = List.map int_of_string strs in
                    vec_len := List.length ints;
                    int_lists := ints :: !int_lists;
                    List.iter (fun i -> printf "%d " i) ints;
                    printf "\n";
                    if may_log DEBUG
                    then begin
                        List.iter (fun i -> printf "%d " i) ints;
                        printf "\n"
                    end
                end else (printf "WARNING: no match for %s\n" line)
            done
        with End_of_file ->
            close_in fin;
    end;

    let int_to_expr pos value =
        let id = !last_id in
        last_id := !last_id + 1;
        if pos < ctr_ctx#get_ctr_dim
        then let e = dom#concretize
                (BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, Const pos)) value in
            let acc = BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, Const pos) in
            (id, e, BinEx (EQ, acc, Const value))
        else let shared_no = pos - ctr_ctx#get_ctr_dim in
            let v = Var (List.nth t_ctx#get_shared shared_no) in
            let e =
                if t_ctx#must_hack_expr v
                then dom#concretize v value
                else BinEx (EQ, v, Const value) (* keep it abstract *)
            in
            (id, e, BinEx (EQ, v, Const value))
    in
    let row_to_exprs (state_no: int) (lst: int list) : token stmt list =
        let map_one pos value =
            let id, conc_ex, abs_ex = int_to_expr pos value in
            Hashtbl.add rev_map id (state_no, abs_ex);
            Expr (id, conc_ex) in
        List.map2 map_one (range 0 !vec_len) lst
    in
    let asserts =
        List.map2 row_to_exprs
            (range 0 (List.length !int_lists)) (List.rev !int_lists)
    in
    (asserts, rev_map)
;;

(* don't touch symbolic variables --- they are the parameters! *)
let map_to_in v = if v#is_symbolic then v else v#copy (v#get_name ^ "_IN") ;;
let map_to_out v = if v#is_symbolic then v else v#copy (v#get_name ^ "_OUT") ;;
let map_to_step step v =
    if v#is_symbolic then v else v#copy (sprintf "S%d_%s" step v#get_name) ;;

let stick_var map_fun v = Var (map_fun v);;


let connect_steps shared_vars step =
    let connect v =
        let ov = map_to_step step (map_to_out v) in
        let iv = map_to_step (step + 1) (map_to_in v) in
        BinEx (EQ, Var ov, Var iv) in
    list_to_binex AND (List.map connect shared_vars)
;;

let create_path shared_vars xducer n_steps =
    let map_xducer n = List.map (map_vars (stick_var (map_to_step n))) xducer in
    let xducers = List.concat (List.map map_xducer (range 0 n_steps)) in
    let connections =
        List.map (connect_steps shared_vars) (range 0 (n_steps - 1)) in
    xducers @ connections
;;

let simulate_in_smt solver t_ctx ctr_ctx xducers trail_asserts rev_map n_steps =
    let smt_rev_map = Hashtbl.create (Hashtbl.length rev_map) in
    assert (n_steps < (List.length trail_asserts));
    let trail_asserts = list_sub trail_asserts 0 (n_steps + 1) in
    let append_one_assert state_no asrt =
        match asrt with
        | Expr (id, e) ->
            let new_e =
                if state_no = 0
                then map_vars (fun v -> Var (map_to_step 0 (map_to_in v))) e
                else map_vars
                    (fun v -> Var (map_to_step (state_no - 1) (map_to_out v))) e
            in
            let smt_id = solver#append_expr new_e in
            (* bind ids from the solver with reverse mapping on
               concrete expressions *)
            let s, e = (Hashtbl.find rev_map id) in
            log DEBUG (sprintf "map: %d -> %d %s\n" smt_id s (expr_s e));
            Hashtbl.add smt_rev_map smt_id (Hashtbl.find rev_map id)

        | _ -> ()
    in
    let append_trail_asserts state_no asserts =
        List.iter (append_one_assert state_no) asserts
    in
    solver#push_ctx;
    (* put asserts from the control flow graph *)
    assert (1 = (Hashtbl.length xducers));
    let proc_xducer = List.hd (hashtbl_vals xducers) in
    let xducer_asserts =
        create_path (ctr_ctx#get_ctr :: t_ctx#get_shared) proc_xducer n_steps in
    let decls = expr_list_used_vars xducer_asserts in

    List.iter (fun v -> solver#append (var_to_smt v)) decls;
    List.iter (fun e -> let _ = solver#append_expr e in ()) xducer_asserts;
    (* put asserts from the counter example *)
    List.iter2 append_trail_asserts (range 0 (n_steps + 1)) trail_asserts;
    let result = solver#check in
    solver#pop_ctx;
    (result, smt_rev_map)
;;

let parse_smt_evidence solver =
    let vals = Hashtbl.create 10 in
    let lines = solver#get_evidence in
    let var_re =
        Str.regexp "(= S\\([0-9]+\\)_\\([a-zA-Z0-9]+\\)_\\(IN\\|OUT\\) \\([-0-9]+\\))"
    in
    let arr_re =
        Str.regexp "(= (S\\([0-9]+\\)_\\([a-zA-Z0-9]+\\)_\\(IN\\|OUT\\) \\([0-9]+\\)) \\([-0-9]+\\))"
    in
    let add_state_expr state expr =
        if not (Hashtbl.mem vals state)
        then Hashtbl.add vals state [expr]
        else Hashtbl.replace vals state (expr :: (Hashtbl.find vals state))
    in
    let parse_line line =
        if Str.string_match var_re line 0
        then
            let step = int_of_string (Str.matched_group 1 line) in
            let name = (Str.matched_group 2 line) in
            let dir = (Str.matched_group 3 line) in
            (* we support ints only, don't we? *)
            let value = int_of_string (Str.matched_group 4 line) in
            let state = if dir = "IN" then step else (step + 1) in
            let e = BinEx (ASGN, Var (new var name), Const value) in
            add_state_expr state e;
        else if Str.string_match arr_re line 0
        then
            let step = int_of_string (Str.matched_group 1 line) in
            let name = (Str.matched_group 2 line) in
            let dir = (Str.matched_group 3 line) in
            let idx = int_of_string (Str.matched_group 4 line) in
            (* we support ints only, don't we? *)
            let value = int_of_string (Str.matched_group 5 line) in
            let state = if dir = "IN" then step else (step + 1) in
            let e = BinEx (ASGN,
                BinEx (ARR_ACCESS, Var (new var name), Const idx),
                Const value) in
            add_state_expr state e;
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
;;

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
;;

let intro_new_pred () =
    let re = Str.regexp ".*bit bymc_p\\([0-9]+\\) = 0;.*" in
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
    let pred_no = 1 + !max_no in
    let cout = open_out_gen [Open_append] 0666 "cegar_decl.inc" in
    fprintf cout "bit bymc_p%d = 0;\n" pred_no;
    close_out cout;
    pred_no
;;

let refine_spurious_step solver smt_rev_map src_state_no =
    let core_ids = solver#get_unsat_cores in
    log INFO (sprintf "Detected %d unsat core ids\n" (List.length core_ids));
    let filtered = List.filter (fun id -> Hashtbl.mem smt_rev_map id) core_ids 
    in
    let mapped = List.map (fun id -> Hashtbl.find smt_rev_map id) filtered in
    let pre, post = List.partition (fun (s, e) -> s = src_state_no) mapped in
    let b2 (s, e) = sprintf "(%s)" (expr_s e) in
    let pre, post = List.map b2 pre, List.map b2 post in
    let pred_no = intro_new_pred () in

    let cout = open_out_gen [Open_append] 0666 "cegar_pre.inc" in
    fprintf cout "bymc_p%d = (%s);\n" pred_no (String.concat " && " pre);
    close_out cout;

    let cout = open_out_gen [Open_append] 0666 "cegar_post.inc" in
    fprintf cout "bymc_spur = (bymc_p%d && (%s)) || bymc_spur;\n"
        pred_no (String.concat " && " post);
    close_out cout
;;
