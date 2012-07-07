(* The refinement for our counter abstraction *)

open Printf;;

open Accums;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
open Smt;;
open Debug;;

let parse_spin_trail filename dom t_ctx ctr_ctx =
    let state_re = Str.regexp ".*GS{[0-9]*->[0-9]*:\\(\\([0-9,]\\)*\\)}.*" in
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
                    if may_log DEBUG
                    then begin
                        List.iter (fun i -> printf "%d " i) ints; printf "\n"
                    end
                end
            done
        with End_of_file ->
            close_in fin;
    end;

    let int_to_expr pos value =
        if pos < ctr_ctx#get_ctr_dim
        then dom#concretize
            (BinEx (ARR_ACCESS, Var ctr_ctx#get_ctr, Const pos)) value
        else let shared_no = pos - ctr_ctx#get_ctr_dim in
            dom#concretize (Var (List.nth t_ctx#get_shared shared_no)) value
    in
    let row_to_exprs (lst: int list) : token expr list =
        List.map2 int_to_expr (range 0 !vec_len) lst
    in
    List.map row_to_exprs (List.rev !int_lists)
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

let create_path shared_vars xducer num =
    let map_xducer n = List.map (map_vars (stick_var (map_to_step n))) xducer in
    let xducers = List.concat (List.map map_xducer (range 0 num)) in
    let connections =
        List.map (connect_steps shared_vars) (range 0 (num - 1)) in
    xducers @ connections
;;

let simulate_in_smt solver t_ctx ctr_ctx xducers trail_asserts n_steps =
    assert (n_steps < (List.length trail_asserts));
    let trail_asserts = list_sub trail_asserts 0 (n_steps + 1) in
    let print_row i exprs =
        Printf.printf "  %d. " i;
        List.iter (fun e -> Printf.printf "%s " (expr_s e)) exprs;
        Printf.printf "\n"
    in
    if may_log DEBUG then List.iter2 print_row (range 0 n_steps) trail_asserts;
    let map_it i asserts =
        if i = 0
        then List.map
            (map_vars (fun v -> Var (map_to_step 0 (map_to_in v)))) asserts
        else List.map
            (map_vars (fun v -> Var (map_to_step (i - 1) (map_to_out v))))
            asserts
    in
    let trail_asserts_glued =
        List.map2 map_it (range 0 (n_steps + 1)) trail_asserts in
    assert (1 = (Hashtbl.length xducers));
    let proc_xducer = List.hd (hashtbl_vals xducers) in
    let xducer_asserts =
        create_path (ctr_ctx#get_pc :: t_ctx#get_shared) proc_xducer n_steps in
    let asserts = xducer_asserts @ (List.concat trail_asserts_glued) in
    let decls = expr_list_used_vars asserts in
    let fo = open_out (sprintf "cex%d.yices" n_steps) in
    let push_var v = fprintf fo "%s\n" (var_to_smt v) in
    let push_expr e =
        fprintf fo ";; %s\n" (expr_s e);
        fprintf fo "(assert %s)\n" (expr_to_smt e)
    in
    fprintf fo "(set-evidence! true)\n";
    (* global definitions and assumptions go to the file only *)
    List.iter push_var t_ctx#get_symbolic;
    List.iter push_expr t_ctx#get_assumps;
    (* the main part of assertions *)
    List.iter push_var decls;
    List.iter push_expr asserts;
    fprintf fo "(check)\n";
    close_out fo;

    solver#push_ctx;
    List.iter (fun v -> solver#append (var_to_smt v)) decls;
    List.iter (fun e -> solver#append_expr e) asserts;
    let result = solver#check in
    solver#pop_ctx;
    result
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
            if (dir = "IN" && state = 0) || (dir = "OUT")
            then add_state_expr state e;
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
            if (dir = "IN" && state = 0) || (dir = "OUT")
            then add_state_expr state e;
    in
    List.iter parse_line lines;
    let cmp e1 e2 =
        match e1, e2 with
        | BinEx (ASGN, Var v1, _),
          BinEx (ASGN, Var v2, _) ->
                String.compare v1#get_name v2#get_name
        | BinEx (ASGN, BinEx (ARR_ACCESS, Var a1, Const i1), _),
          BinEx (ASGN, BinEx (ARR_ACCESS, Var a2, Const i2), _) ->
                let r = String.compare a1#get_name a2#get_name in
                if r <> 0 then r else (i1 - i2)
        | BinEx (ASGN, BinEx (ARR_ACCESS, Var a1, Const i1), _),
          BinEx (ASGN, Var v2, _) ->
                -1 (* arrays go first *)
        | BinEx (ASGN, Var v1, _),
          BinEx (ASGN, BinEx (ARR_ACCESS, Var a2, Const i2), _) ->
                1 (* arrays go first *)
        | _ -> -1 (* preserve the order otherwise *)
    in
    let new_tbl = Hashtbl.create (Hashtbl.length vals) in
    Hashtbl.iter
        (fun k vs -> Hashtbl.add new_tbl k (List.sort cmp vs))
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
                assert (!last_idx < idx);
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

