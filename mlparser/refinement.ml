(* The refinement for our counter abstraction *)

open Printf;;

open Accums;;
open Spin;;
open Spin_ir;;
open Spin_ir_imp;;
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

let map_to_layer layer expr =
    let map_fun v = Var (v#copy (sprintf "L%d_%s" layer v#get_name)) in
    map_vars map_fun expr
;;

let connect_layers shared_vars layer =
    let connect v =
        let ov = map_to_layer layer (Var (v#copy (v#get_name ^ "_OUT"))) in
        let iv = map_to_layer (layer + 1) (Var (v#copy (v#get_name ^ "_IN"))) in
        BinEx (EQ, ov, iv) in
    list_to_binex AND (List.map connect shared_vars)
;;

let create_path shared_vars xducer num =
    let map_xducer n = List.map (map_to_layer n) xducer in
    let xducers = List.concat (List.map map_xducer (range 0 num)) in
    let connections =
        List.map (connect_layers shared_vars) (range 0 (num - 1)) in
    xducers @ connections
;;
