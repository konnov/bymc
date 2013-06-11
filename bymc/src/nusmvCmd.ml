(*
 * All the things related to the command line interface and output
 * produced by NuSMV.
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

let parse_nusmv_trace filename dom data_ctx ctr_ctx_tbl prog =
    let last_id = ref 0 in
    let rev_map = Hashtbl.create 10 in (* from ids to abstract states *)
    let assignment = Hashtbl.create 10 in (* current state mapping *)
    let assign_re = Str.regexp " *([a-zA-Z0-9_]+) = ([0-9]+) <-.*" in
    let state_re = Str.regexp " *-> State: [0-9]+\\.([0-9]+) <-.*" in
    let loop_re = Str.regexp ".*-- Loop starts here.*" in
    let rev_rows = ref [] in
    let loop_pos = ref 0 in
    let fin = open_in filename in
    begin (* Parse strings like
            -> State: 2.4 <-
              bymc_kP_0I = 1 *)
        try
            while true do
                let line = input_line fin in
                if Str.string_match assign_re line 0
                then
                    let name = Str.matched_group 1 line in
                    let value = int_of_string (Str.matched_group 2 line) in
                    if may_log DEBUG then printf "%s = %d\n";
                    Hashtbl.replace assignment name value
                else if Str.string_match state_re line 0
                then rev_rows := (Hashtbl.copy assignment) :: !rev_rows
                else if Str.string_match loop_re line 0
                then loop_pos := (List.length !rev_rows)
            done
        with End_of_file ->
            close_in fin;
    end;
    printf "loop starts with %d\n" !loop_pos;
    let rows = List.tl (List.rev !rev_rows) in (* remove the first row *)
    let num_rows = List.length rows in
    loop_pos := !loop_pos - 1;

    (* TODO: finish it! *)

    let int_to_expr c_ctx name value =
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
    let row_to_exprs (state_no: int) (row: (string * int) Hashtbl.t list)
            : string * token stmt list =
        let proc_num = Hashtbl.find row "bymc_proc" in
        let proc = List.get (Program.get_procs prog) proc_num in
        let c_ctx = ctr_ctx_tbl#get_ctx proc in
        let map_one name value =
            let id, conc_ex, abs_ex = int_to_expr c_ctx name value in
            Hashtbl.add rev_map id (state_no, abs_ex);
            Expr (id, conc_ex) in
        (* a list of concrete constraints on each column of the row *)
        (proc, List.map2 map_one (range 0 (List.length row)) row)
    in
    let prefix_asserts = List.map2 row_to_exprs (range 0 num_rows) rows in
    let loop_asserts = list_sub prefix_asserts !loop_pos (num_rows - !loop_pos) in
    (prefix_asserts, loop_asserts, rev_map)

