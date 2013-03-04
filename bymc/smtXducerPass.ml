(* Translate a program to an SSA representation and then construct
   SMT assumptions.

   Igor Konnov, 2012
 *)

open Printf

open Accums
open Cfg
open CfgSmt
open Debug
open SpinIr
open SpinIrImp
open Ssa

let write_exprs name stmts =
    let mul = 1 + (List.length stmts) in
    (* assign new ids to expression in a way that keeps the order between
       old ids and blocks of statements between them *)
    let num_stmt (num, lst) = function
        | MExpr (id, e) ->
                ((id + 1) * mul + 1, (MExpr ((id + 1) * mul, e)) :: lst)
        | _ ->
                raise (Failure "Expected Expr (_, _)")
    in
    let _, numbered = (List.fold_left num_stmt (0, []) stmts) in
    let sorted_stmts = List.sort cmp_m_stmt numbered in
    let out = open_out (sprintf "%s.xd" name) in
    let write_e s = fprintf out "%s\n" (expr_s (expr_of_m_stmt s)) in
    List.iter write_e sorted_stmts;
    close_out out


let to_xducer caches prog new_type_tab p =
    let reg_tbl = caches#get_struc#get_regions p#get_name in
    let loop_prefix = reg_tbl#get "loop_prefix" in
    let loop_body = reg_tbl#get "loop_body" in
    let lirs = (mir_to_lir (loop_body @ loop_prefix)) in
    let globals =
        (Program.get_shared prog) @ (Program.get_instrumental prog) in
    let locals = (Program.get_all_locals prog) in
    let cfg = mk_ssa true globals locals (mk_cfg lirs) in
    if may_log DEBUG
    then print_detailed_cfg ("Loop of " ^ p#get_name ^ " in SSA: " ) cfg;
    Cfg.write_dot (sprintf "ssa_%s.dot" p#get_name) cfg;
    let transd = cfg_to_constraints p#get_name new_type_tab cfg in
    write_exprs p#get_name transd;
    proc_replace_body p transd


let do_xducers caches prog =
    let new_type_tab = (Program.get_type_tab prog)#copy in
    let new_procs = List.map
        (to_xducer caches prog new_type_tab) (Program.get_procs prog) in
    (Program.set_type_tab new_type_tab
        (Program.set_procs new_procs prog))

