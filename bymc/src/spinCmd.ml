(*
 * All the things related to the command line interface and output
 * produced by Spin.
 *
 * Igor Konnov, 2013
 *)

open Printf
open Str

open Accums
open Debug
open Spin
open SpinIr
open SpinIrImp
open Smt

(* to be removed, use SpinPlugin instead *)
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
            (* constraint no, concrete expression,
               abstract expression d_l <= v < d_u *)
            (id, e, BinEx (EQ, arr_ctr_elem, Const value))
        else let shared_no = pos - c_ctx#get_ctr_dim in
            let shared = (Program.get_shared prog) in
            let v = Var (List.nth shared shared_no) in
            let e =
                if data_ctx#must_keep_concrete v
                then dom#expr_is_concretization v value (* d_l <= v < d_u *)
                else BinEx (EQ, v, Const value) (* keep abstract, v = d *)
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

