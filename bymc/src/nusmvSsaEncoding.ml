(*
 Translating processes in SSA and encoding them in NuSMV format.
 This is the third try to create an efficient encoding in NuSMV.
 *)

open Printf

open Cfg
open CfgSmt
open Nusmv
open Spin
open SpinIr
open SpinIrImp
open Ssa

type proc_var_t =
    | SharedIn of var
    | SharedOut of var
    | LocalIn of var
    | LocalOut of var
    | Temp of var

let is_var_temp = function
    | Temp _ -> true
    | _ -> false

let is_var_local = function
    | LocalIn _ -> true
    | LocalOut _ -> true
    | _ -> false

let is_var_shared_in = function
    | SharedIn _ -> true
    | _ -> false

let ptov = function
    | SharedIn v
    | SharedOut v
    | LocalIn v
    | LocalOut v
    | Temp v -> v


let partition_var v =
    let is_in = (Str.last_chars v#get_name 3) = "_IN" in
    let is_out = (Str.last_chars v#get_name 4) = "_OUT" in
    match (is_in, is_out) with
    | (true, _) -> if v#proc_name = "" then SharedIn v else LocalIn v
    | (_, true) -> if v#proc_name = "" then SharedOut v else SharedIn v
    | _ -> Temp v


let replace_with_next syms v =
    match partition_var v with
    | SharedOut _ ->
        let nm = v#get_name in
        let inm = (String.sub nm 0 ((String.length nm) - 4)) ^ "_IN" in
        UnEx (NEXT, Var ((syms#lookup inm)#as_var))

    | _ -> Var v 


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

        (new_type_tab, new_sym_tab, List.map expr_of_m_stmt exprs)
    in
    let ntt, syms, exprs = to_ssa in
    let new_vars = vars_of_syms syms#get_symbs in
    let exprs = List.map (map_vars (replace_with_next syms)) exprs in
    let pvars = List.map partition_var new_vars in
    let temps = List.map ptov (List.filter is_var_temp pvars) in
    let args = List.map ptov (List.filter
        (fun pv -> is_var_local pv || is_var_shared_in pv) pvars) in
    let temp_decls = List.map (fun v -> (v, ntt#get_type v)) temps in
    Module (proc#get_name, args, [SVar temp_decls; STrans exprs])


let transform rt out_name intabs_prog =
    let procs = Program.get_procs intabs_prog in
    let tops = List.map (module_of_proc rt intabs_prog) procs in
    let out = open_out (out_name ^ ".smv") in
    List.iter (fun t -> fprintf out "%s\n" (top_s t)) tops;
    close_out out

