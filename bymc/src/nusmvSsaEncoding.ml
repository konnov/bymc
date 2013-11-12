(*
 Translating processes in SSA and encoding them in NuSMV format.
 This is the third try to create an efficient encoding in NuSMV.
 *)

open Printf

open Cfg
open CfgSmt
open Nusmv
open SpinIr
open SpinIrImp
open Ssa

let module_of_proc rt prog proc =
    let vars_of_syms syms =
        let is_var s = s#get_sym_type = SymVar in
        List.map (fun s -> s#as_var) (List.filter is_var syms)
    in
    let to_ssa =
        let reg_tbl =
            (rt#caches#find_struc prog)#get_regions proc#get_name in
        let comp = reg_tbl#get "comp" proc#get_stmts in
        (* both locals and shared are the parameters of our module *)
        let locals = vars_of_syms proc#get_symbs in
        let shared = Program.get_shared prog in
        (* construct SSA as in SmtXducerPass *)
        let new_sym_tab = new symb_tab "tmp" in
        let new_type_tab = (Program.get_type_tab prog)#copy in
        let cfg =
            mk_ssa false (shared @ locals) []
                new_sym_tab new_type_tab (mk_cfg (mir_to_lir comp)) in
        let exprs =
            cfg_to_constraints proc#get_name new_sym_tab new_type_tab cfg in
        (* find the new variables *)
        let temps = vars_of_syms new_sym_tab#get_symbs in
        (new_type_tab, shared, locals, temps, List.map expr_of_m_stmt exprs)
    in
    let is_arg v =
        (Str.last_chars v#get_name 3) = "_IN"
        || (Str.last_chars v#get_name 4) = "_OUT"
    in
    let ntt, shared, locals, temps, exprs = to_ssa in
    let locals = List.filter (fun v -> not (is_arg v)) temps in
    let args = List.filter is_arg temps in
    let temp_decls = List.map (fun v -> (v, ntt#get_type v)) locals in
    Module (proc#get_name, args, [SVar temp_decls; STrans exprs])

let transform rt out_name intabs_prog =
    let procs = Program.get_procs intabs_prog in
    let tops = List.map (module_of_proc rt intabs_prog) procs in
    let out = open_out (out_name ^ ".smv") in
    List.iter (fun t -> fprintf out "%s\n" (top_s t)) tops;
    close_out out

