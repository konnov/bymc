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
let map_to_layer layer v =
    if v#is_symbolic then v else v#copy (sprintf "L%d_%s" layer v#get_name) ;;

let stick_var map_fun v = Var (map_fun v);;


let connect_layers shared_vars layer =
    let connect v =
        let ov = map_to_layer (layer + 1) (map_to_out v) in
        let iv = map_to_layer layer (map_to_in v) in
        BinEx (EQ, Var ov, Var iv) in
    list_to_binex AND (List.map connect shared_vars)
;;

let create_path shared_vars xducer num =
    let map_xducer n = List.map (map_vars (stick_var (map_to_layer n))) xducer in
    let xducers = List.concat (List.map map_xducer (range 0 num)) in
    let connections =
        List.map (connect_layers shared_vars) (range 0 (num - 1)) in
    xducers @ connections
;;

let simulate_in_smt solver t_ctx xducers trail_asserts n_steps =
    assert (n_steps < (List.length trail_asserts));
    let trail_asserts = list_sub trail_asserts 0 n_steps in
    let print_row i exprs =
        Printf.printf "  %d. " i;
        List.iter (fun e -> Printf.printf "%s " (expr_s e)) exprs;
        Printf.printf "\n"
    in
    if may_log DEBUG then List.iter2 print_row (range 0 n_steps) trail_asserts;
    let map_it i asserts =
        if i = 0
        then List.map
            (map_vars (fun v -> Var (map_to_layer i (map_to_in v)))) asserts
        else List.map
            (map_vars (fun v -> Var (map_to_layer (i - 1) (map_to_out v))))
            asserts
    in
    let trail_asserts_glued =
        List.map2 map_it (range 0 n_steps) trail_asserts in
    assert (1 = (Hashtbl.length xducers));
    let proc_xducer = List.hd (hashtbl_vals xducers) in
    let xducer_asserts = create_path t_ctx#get_shared proc_xducer n_steps in
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
    List.iter (fun e -> solver#append_assert (expr_to_smt e)) asserts;
    let result = solver#check in
    solver#pop_ctx;
    result

