(* Use a symbolic skeleton in the NusmvSsaEncoding.
  We expect that it boosts the performance of both BDD and BMC model checking
  in NuSMV.

  NuSMV modules produced by this module MUST be compatible by signature
  with the process modules produced by NusmvSsaEncoding, as we later embed
  the modules into NusmvSsaEncoding.

  Igor Konnov, 2014
 *)

open Printf

open Accums
open Debug
open Spin
open SpinIr
open SymbSkel

(* constrain the local variables only to the combinations
    (src, dst) as prescribed by a skeleton.
 *)
let make_invar rt prog proc sk =
    let reg_tbl =
        (rt#caches#find_struc prog)#get_regions proc#get_name in
    let loop_sig = SkelStruc.extract_loop_sig prog reg_tbl proc in
    let prev_next = SkelStruc.get_prev_next loop_sig in
    let locals = sk.Sk.locals in
    let next_locals =
        List.map (fun v -> List.assoc v prev_next) locals in
    let map_loc vars l =
        let eq var value = BinEx (EQ, Var var, IntConst value) in
        list_to_binex AND (List.map2 eq vars l)
    in
    let rule_locs_cond r =
        let sloc = List.nth sk.Sk.locs r.Sk.src in
        let dloc = List.nth sk.Sk.locs r.Sk.dst in
        BinEx (AND,
            BinEx (AND, map_loc locals sloc, map_loc next_locals dloc),
            r.Sk.guard)
    in
    let inv = [list_to_binex OR (List.map rule_locs_cond sk.Sk.rules)] in
    let neg = Simplif.propagate_not ~negate:true in
    let rule_expr r =
        (* (src = a and dst = b and guard) -> action *)
        BinEx (OR, neg (rule_locs_cond r), list_to_binex AND r.Sk.act)
    in
    let trans = List.map rule_expr sk.Sk.rules in
    inv, trans

(*
  This is a modification of NusmvSsaEncoding.module_of_proc;
  many complex features are stripped off.
  TODO: multiple process types are not supported yet!
 *)
let module_of_proc rt prog skels =
    let procs = Program.get_procs prog in
    let nprocs = List.length procs in
    assert (nprocs = 1);
    let shared = Program.get_shared prog in
    let mono_proc_name = "P" in (* a shorter name improves readability *)

    (* process id is chosen non-deterministically for each step *)
    let pid = new_var "pid" in
    pid#set_proc_name "p"; (* to make life easier *)
    let pidt = new data_type SpinTypes.TINT in
    pidt#set_range 0 nprocs;

    let new_type_tab = (Program.get_type_tab prog)#copy in
    new_type_tab#set_type pid pidt;
    let new_sym_tab = new symb_tab mono_proc_name in
    new_sym_tab#add_symb pid#mangled_name (pid :> symb);

    let vart v =
        let vt = Program.get_type prog v in
        v, vt
    in
    let globalize v =
        let nv = v#copy v#mangled_name in
        nv#set_proc_name ""; (* make them global *)
        let _, vt = vart v in
        nv, vt
    in
    let new_locals = List.map globalize (Program.get_all_locals prog) in
    (* we have to constrain the variables with the invariant to cut out
       the deadlock behaviour when the input variables do not match
       the process code *)
    let invar_list, trans_list =
        List.split (List.map2 (make_invar rt prog) procs skels) in
    (* for the transition relation we either replace x_OUT with
       next(x), or keep it as it is (for the reachability) *)
    let args = (pid, pidt) :: (List.map vart shared) @ new_locals in
    let mod_type =
        Nusmv.SModule (mono_proc_name,
            (List.map (fun (v, _) -> v) args),
            [ (* the invariant explodes NuSMV-BDD,
                avoid it for reachability *)
             Nusmv.SInvar (List.concat invar_list);
             Nusmv.STrans (List.concat trans_list)])
    in
    (mono_proc_name, mod_type, args, new_sym_tab, new_type_tab)


let create_proc_mods rt intabs_prog skels =
    let proc_name, mod_type, args, nst, ntt =
        module_of_proc rt intabs_prog skels in

    let inst = Nusmv.SModInst("p_" ^ proc_name, proc_name,
        (List.map (fun (v, _) -> Var v) args))
    in
    let pid = (nst#lookup "p__pid")#as_var in
    ([Nusmv.SVar args; inst], [mod_type], nst, ntt, pid)


let transform rt out_name intabs_prog ctrabs_prog skels =
    (* TODO: this is a clone of NusmvSsaEncoding.transform.
       Consider refactoring *)
    let module SMV = NusmvSsaEncoding in
    let out = open_out (out_name ^ ".smv") in
    let main_sects, proc_mod_defs, proc_st, proc_tt, pid =
        create_proc_mods rt intabs_prog skels in
    let init_main = SMV.init_of_ctrabs rt intabs_prog ctrabs_prog in
    let ctr_main, ctr_mods =
        SMV.create_counter_mods rt proc_st proc_tt ctrabs_prog pid in
    let forms = SMV.create_counter_specs rt ctrabs_prog in
    let globals = SMV.collect_globals (main_sects @ ctr_main) in
    let non_spurious =
        SMV.create_counter_non_spurious rt ctrabs_prog globals in
    let all_main_sects =
        main_sects @ ctr_main @ init_main @ non_spurious in
    let tops = Nusmv.SModule ("main", [], all_main_sects)
            :: forms @ proc_mod_defs @ ctr_mods in
    let globals =
        List.map (fun v -> v#mangled_name)
            (SMV.collect_globals all_main_sects)
    in
    let hidden =
        SMV.create_or_read_names rt#caches#options globals "main-ssa-hidden.txt"
    in
    let hidden_set =
        List.fold_left (fun s n -> StrSet.add n s) StrSet.empty hidden
    in
    let visible_sections = SMV.hide_vars hidden_set tops in
    List.iter (fun t -> fprintf out "%s\n" (Nusmv.top_s t)) visible_sections;
    close_out out

