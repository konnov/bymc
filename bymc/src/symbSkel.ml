(* Extract a symbolic skeleton.
 *
 * Igor Konnov, 2014
 *)

open Printf

open Spin
open SpinIr
open SpinIrImp

open Cfg
open Ssa

let collect_constraints rt prog proc =
    (* do symbolic exploration/simplification *)
    (* collect a formula along the path *)
    let ntt = (Program.get_type_tab prog)#copy in
    let nst = new symb_tab proc#get_name in
    let get_comp p =
        let reg_tab = (rt#caches#find_struc prog)#get_regions p#get_name
        in
        reg_tab#get "comp" p#get_stmts 
    in
    let all_stmts = mir_to_lir (get_comp proc) in
    let cfg = Cfg.remove_ineffective_blocks (mk_cfg all_stmts) in
    let shared = Program.get_shared prog in
    let locals = proc#get_locals in
    let cfg_ssa = mk_ssa rt#solver false shared locals nst ntt cfg
    in
    Cfg.write_dot (sprintf "ssa-symb-%s.dot" proc#get_name) cfg_ssa;
    ()

