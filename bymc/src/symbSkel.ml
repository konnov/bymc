(* Extract a symbolic skeleton.
 *
 * Igor Konnov, 2014
 *)

open Printf

open Spin
open SpinIr
open SpinIrImp
open SymbExec

open Cfg
open Ssa

let collect_constraints rt prog proc trs =
    (* do symbolic exploration/simplification *)
    (* collect a formula along the path *)
    let get_comp p =
        let reg_tab = (rt#caches#find_struc prog)#get_regions p#get_name
        in
        reg_tab#get "comp" p#get_stmts 
    in
    let all_stmts = mir_to_lir (get_comp proc) in
    let cfg = Cfg.remove_ineffective_blocks (mk_cfg all_stmts) in
    let shared = Program.get_shared prog in
    let locals = proc#get_locals in
    let vars = locals @ shared in
    let ntt = (Program.get_type_tab prog)#copy in
    let nst = new symb_tab proc#get_name in
    nst#add_all_symb proc#get_symbs;
    (* XXX: do smth with it *)
    let add_input s =
        if s#get_sym_type = SymVar
        then let v = s#as_var in
            let iname = v#get_name ^ "_in" in
            nst#add_symb iname ((v#copy iname) :> symb)
    in
    List.iter add_input proc#get_symbs;

    let path_efun = enum_paths cfg in
    let num_paths = path_efun (exec_path rt#solver stdout ntt nst vars)
    in
    Printf.printf "    enumerated %d paths\n" num_paths;
    ()

