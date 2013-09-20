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
open PiaDom
open PiaDataCtx
open PiaCtrCtx
open Program
open RevTrans
open Spin
open SpinIr
open SpinIrImp
open Smt

let parse_nusmv_trace (filename: string) (dom: pia_domain) (data_ctx: pia_data_ctx)
        (ctr_ctx_tbl: ctr_abs_ctx_tbl) (rev_tab: retrans_tab)
        (prog: Program.program_t) =
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
                    if may_log DEBUG then printf "%s = %d\n" name value;
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

    let sym_tab = Program.get_sym_tab prog in
    let conc_expr c_ctx name value =
        let id = !last_id in
        last_id := !last_id + 1;
        let v = (sym_tab#lookup name)#as_var in
        match rev_tab#get v with
        | Var w ->
            let e =
                if data_ctx#must_keep_concrete (Var w)
                then dom#expr_is_concretization (Var w) value (* d_l <= v < d_u *)
                else BinEx (EQ, Var w, Const value) (* keep abstract, v = d *)
            in
            (* constraint no, concrete expression, abstract expression *)
            (id, e, BinEx (EQ, Var v, Const value))

        | _ as lhs ->
            let e = dom#expr_is_concretization lhs value in
            (* constraint no, concrete expression,
               abstract expression d_l <= v < d_u *)
            (id, e, BinEx (EQ, lhs, Const value))
    in
    let row_to_exprs (state_no: int) (row: (string, int) Hashtbl.t)
            : string * token stmt list =
        let proc_num = Hashtbl.find row "bymc_proc" in
        let proc = List.nth (Program.get_procs prog) proc_num in
        let c_ctx = ctr_ctx_tbl#get_ctx proc#get_name in
        let map_one name value lst =
            let id, conc_ex, abs_ex = conc_expr c_ctx name value in
            Hashtbl.add rev_map id (state_no, abs_ex);
            (Expr (id, conc_ex)) :: lst in
        (* a list of concrete constraints on each column of the row *)
        (proc#get_name, Hashtbl.fold map_one row [])
    in
    let prefix_asserts = List.map2 row_to_exprs (range 0 num_rows) rows in
    let loop_asserts = list_sub prefix_asserts !loop_pos (num_rows - !loop_pos) in
    (prefix_asserts, loop_asserts, rev_map)

