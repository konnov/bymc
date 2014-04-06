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
open SpinIr


(*
  This is a modification of NusmvSsaEncoding.
  TODO: multiple process types are not supported yet!
 *)
let module_of_proc rt prog skels =
    let procs = Program.get_procs prog in
    let nprocs = List.length procs in
    assert (nprocs = 1);
    let shared = Program.get_shared prog in
    let shared_set =
        List.fold_left (fun s v -> StrSet.add v#get_name s)
            StrSet.empty shared in
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
    let invar = [Var Nusmv.nusmv_true] (* TODO: fix it later *)
    in
    (* for the transition relation we either replace x_OUT with
       next(x), or keep it as it is (for the reachability) *)
    let exprs = [Var Nusmv.nusmv_true] (* TODO: use the skeleton here *)
    in
    let args = (List.map vart shared) @ new_locals in
    let mod_type =
        Nusmv.SModule (mono_proc_name,
            (List.map (fun (v, _) -> v) args),
            [ (* the invariant explodes NuSMV-BDD,
                avoid it for reachability *)
             Nusmv.SInvar invar;
             Nusmv.STrans exprs])
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

