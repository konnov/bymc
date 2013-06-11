(*
  An optimized encoding of counter representation that represent each
  counter as a module. This allows nusmv to use clusters, which are much
  more efficient for large models.

  Igor Konnov, 2013
 *)

open Printf

open AbsBasics
open Accums
open Debug
open Nusmv
open NusmvPass
open RevTrans
open SkelStruc
open Spin
open SpinIr
open SpinIrImp
open SymbExec
open VarRole

let collect_local_ids in_locals out_locals =
    let gather s v =
        IntSet.add v#id s in
    let fold a l = List.fold_left gather a l in
    fold (fold IntSet.empty in_locals) out_locals
    

let collect_rhs solver type_tab dom ctr_ctx op =
    solver#push_ctx;
    let x = ctr_ctx#get_ctr#fresh_copy "x" in
    let y = ctr_ctx#get_ctr#fresh_copy "y" in
    let ctr_tp = type_tab#get_type ctr_ctx#get_ctr in
    let tp = new data_type SpinTypes.TINT in
    tp#set_range_tuple ctr_tp#range;
    solver#append_var_def x tp; 
    solver#append_var_def y tp; 
    let tbl = Hashtbl.create 10 in
    let chg = BinEx (EQ, Var x, BinEx (op, Var y, Const 1)) in
    let on_point p =
        let add xv yv =
            if Hashtbl.mem tbl xv
            then Hashtbl.replace tbl xv (yv :: (Hashtbl.find tbl xv))
            else Hashtbl.add tbl xv [yv]
        in
        match p with
        | ((x1, v1) :: (_, v2) :: []) ->
            if x1#id = x#id then add v1 v2 else add v2 v1
        | _ -> raise (Failure "oops?")
    in
    let points_lst = dom#find_abs_vals ExistAbs solver chg in
    solver#pop_ctx;
    List.iter on_point points_lst;
    tbl


let mk_mod_sig proc idx myval params =
    let vname v = v#mangled_name in
    let ps = str_join ", " (List.map vname params) in
    sprintf "kntr_%s_%d(%s, %s, bymc_loc, bymc_proc)" proc#get_name idx ps myval


let write_counter_mods solver caches sym_tab type_tab hidden_idx_fun
        out proc_num proc (in_locals: var list) (out_locals: var list) =
    let ctr_ctx = caches#analysis#get_pia_ctr_ctx_tbl#get_ctx proc#get_name in
    let dom = caches#analysis#get_pia_dom in
    let dec_tbl = collect_rhs solver type_tab dom ctr_ctx PLUS in
    let inc_tbl = collect_rhs solver type_tab dom ctr_ctx MINUS in
    let create_module idx =
        let valtab = ctr_ctx#unpack_from_const idx in
        let mk_prev con op =
            let f (k, v) =
                let inp = get_input sym_tab k in
                sprintf "%s %s %d" inp#mangled_name op v in
            str_join con (List.map f (hashtbl_as_list valtab)) in
        let prev_eq = mk_prev " & " "=" in
        let prev_neq = mk_prev " | " "!=" in
        let mk_next con op =
            let f (k, v) =
                let out = get_output sym_tab k in
                sprintf "%s %s %d" out#mangled_name op v in
            str_join con (List.map f (hashtbl_as_list valtab)) in
        let next_eq = mk_next " & " "=" in
        let next_neq = mk_next " | " "!=" in
        fprintf out "MODULE %s\n" (mk_mod_sig proc idx "myval" (in_locals @ out_locals));
        fprintf out " ASSIGN\n";
        fprintf out " next(myval) :=\n";
        fprintf out "  case\n";
        let print_next k vs =
            fprintf out "   bymc_proc = %d & bymc_loc = 1 & (%s) & (%s) & myval = %d : { %s };\n"
                proc_num prev_neq next_eq k (str_join ", " (List.map string_of_int vs));
        in
        let print_prev k vs =
            fprintf out "   bymc_proc = %d & bymc_loc = 1 & (%s) & (%s) & myval = %d : { %s };\n"
                proc_num prev_eq next_neq k (str_join ", " (List.map string_of_int vs))
        in
        Hashtbl.iter print_prev dec_tbl;
        Hashtbl.iter print_next inc_tbl;
        fprintf out "   bymc_loc = 0 : {%s};\n"
            (str_join ", " (List.map string_of_int (range 0 dom#length)));
        fprintf out "   TRUE : myval;\n";
        fprintf out "  esac;\n";
    in
    let all_indices = ctr_ctx#all_indices_for (fun _ -> true) in
    let is_visible i =
        let myval = sprintf "%s_%dI" ctr_ctx#get_ctr#get_name i in
        let myval_var = (sym_tab#lookup myval)#as_var in
        0 = (hidden_idx_fun myval_var)
    in
    let visible = List.filter is_visible all_indices in
    List.iter create_module visible


let write_counter_use solver caches sym_tab type_tab hidden hidden_idx_fun
        out proc_num proc (in_locals: var list) (out_locals: var list) =
    let ctr_ctx = caches#analysis#get_pia_ctr_ctx_tbl#get_ctx proc#get_name in
    let vname v = v#mangled_name in
    let ps = str_join ", " (List.map vname (in_locals @ out_locals)) in
    let create_module idx =
        let valtab = ctr_ctx#unpack_from_const idx in
        let mk_prev con op =
            let f (k, v) =
                let inp = get_input sym_tab k in
                sprintf "%s %s %d" inp#mangled_name op v in
            str_join con (List.map f (hashtbl_as_list valtab))
        in
        let mk_next con op =
            let f (k, v) =
                let out = get_output sym_tab k in
                sprintf "%s %s %d" out#mangled_name op v in
            str_join con (List.map f (hashtbl_as_list valtab))
        in
        let prev_ne = mk_prev " | " "!=" in
        let next_eq = mk_next " & " "=" in
        let myval = sprintf "%s_%dI" ctr_ctx#get_ctr#get_name idx in
        let myval_var = (sym_tab#lookup myval)#as_var in
        let var_idx = hidden_idx_fun myval_var in
        if var_idx <> 0 then begin
            fprintf out "   bymc_proc = %d & bymc_loc = 1 & (%s) & (%s): { %d };\n"
                proc_num prev_ne next_eq var_idx
        end
    in
    let hid = List.map hidden_idx_fun hidden in
    let all_indices = ctr_ctx#all_indices_for (fun _ -> true) in
    List.iter create_module all_indices


let write_constraints solver caches sym_tab type_tab hidden_idx_fun
        out proc_num proc (in_locals: var list) (out_locals: var list) =
    let ctr_ctx =
        caches#analysis#get_pia_ctr_ctx_tbl#get_ctx proc#get_name in
    let is_visible i =
        let myval = sprintf "%s_%dI" ctr_ctx#get_ctr#get_name i in
        let myval_var = (sym_tab#lookup myval)#as_var in
        0 = (hidden_idx_fun myval_var)
    in
    let create_cons idx =
        let valtab = ctr_ctx#unpack_from_const idx in
        let prev_eq =
            let f (k, v) =
                let inp = get_input sym_tab k in
                sprintf "%s != %d" inp#mangled_name v in
            str_join " | " (List.map f (hashtbl_as_list valtab)) in
        let next_eq =
            let f (k, v) =
                let out = get_output sym_tab k in
                sprintf "%s = %d" out#mangled_name v in
            str_join " & " (List.map f (hashtbl_as_list valtab)) in
        if not (is_visible idx) then begin
            fprintf out " & (%s | (%s) | bymc_loc != 1)\n" prev_eq next_eq;
            fprintf out "-- "
        end;
        fprintf out " & (bymc_proc != %d | %s | %s_%dI != 0 | bymc_loc = 0)\n"
            proc_num prev_eq ctr_ctx#get_ctr#get_name idx;
    in
    fprintf out "INVAR\n";
    fprintf out " TRUE\n";
    let all_indices = ctr_ctx#all_indices_for (fun _ -> true) in
    List.iter create_cons all_indices


let keep_local local_ids v =
    if IntSet.mem v#id local_ids
    then if is_input v
        then v#mangled_name
        else sprintf "next(%s)" v#mangled_name
    else
    if is_input v
        then mk_output_name v
        else sprintf "next(%s)" (mk_output_name v)


let local_one_step local_ids v =
    if IntSet.mem v#id local_ids
    then if is_input v
        then v#mangled_name
        else mk_output_name v
    else
    if is_input v
        then mk_output_name v
        else sprintf "next(%s)" (mk_output_name v)


let find_proc_non_scratch caches proc =
    let roles = caches#analysis#get_var_roles in
    List.filter (fun v -> not (is_scratch (roles#get_role v))) proc#get_locals


let get_in_out sym_tab vars =
    let ins = List.map (get_input sym_tab) vars in
    let outs = List.map (get_output sym_tab) vars in
    (ins, outs)


let intro_in_out_vars sym_tab type_tab rev_tab prog proc vars =
    let proc_sym_tab = new symb_tab proc#get_name in
    proc_sym_tab#set_parent sym_tab;
    let proc_type_tab = type_tab#copy in
    let _ = transform_vars type_tab proc_type_tab proc_sym_tab rev_tab vars in
    proc_sym_tab, proc_type_tab


let declare_locals_and_counters caches sym_tab type_tab rev_tab
        prog shared all_locals hidden_idx_fun out proc =
    let locals = find_proc_non_scratch caches proc in
    let proc_sym_tab, proc_type_tab =
        intro_in_out_vars sym_tab type_tab rev_tab prog proc locals in
    let decl_var v = 
        let tp = proc_type_tab#get_type v in
        fprintf out "  %s: %s;\n" v#mangled_name (Nusmv.var_type_smv tp)
    in
    let in_locals, out_locals = get_in_out proc_sym_tab locals in
    fprintf out "  -- local variables of %s\n" proc#get_name;
    List.iter decl_var in_locals;
    List.iter decl_var out_locals;

    let vname v = v#mangled_name in
    fprintf out "  -- modules of %s\n" proc#get_name;
    fprintf out "  mod%s: %s(%s, %s, %s);\n" proc#get_name proc#get_name
        (str_join ", " (List.map vname in_locals))
        (str_join ", " (List.map vname out_locals))
        (str_join ", " (List.map vname shared));

    let ctr_ctx = caches#analysis#get_pia_ctr_ctx_tbl#get_ctx proc#get_name in
    let is_visible i =
        let myval = sprintf "%s_%dI" ctr_ctx#get_ctr#get_name i in
        let myval_var = (sym_tab#lookup myval)#as_var in
        0 = (hidden_idx_fun myval_var)
    in
    let declare_mod idx =
        (* XXX: magic encoding *)
        let myval = sprintf "%s_%dI" ctr_ctx#get_ctr#get_name idx in
        let signature = mk_mod_sig proc idx myval (in_locals @ out_locals) in
        if not (is_visible idx) then fprintf out "-- ";
        fprintf out "  mod%s_k%d: %s;\n" proc#get_name idx signature
    in
    let all_indices = ctr_ctx#all_indices_for (fun _ -> true) in
    List.iter declare_mod all_indices


let assign_default type_tab vars =
    let eq_var v =
        let tp = type_tab#get_type v in
        sprintf "(%s = %s)" v#mangled_name (Nusmv.type_default_smv tp) in
    str_join " & " (List.map eq_var vars)


(* create a cluster encoding in nusmv *)
(* XXX: TODO: XXX: this requires serious refactoring! *)
let transform solver caches out_name intabs_prog prog =
    let type_tab = Program.get_type_tab prog in
    let new_type_tab = type_tab#copy in
    let main_sym_tab = new symb_tab "main" in
    let rev_tab = new retrans_tab in
    let instr = transform_vars type_tab new_type_tab main_sym_tab rev_tab
        (Program.get_instrumental prog) in
    let shared = instr @ (transform_vars type_tab new_type_tab
        main_sym_tab rev_tab (Program.get_shared prog)) in
    let scope = SharedOnly in
    let hidden, hidden_idx_fun =
        create_read_hidden main_sym_tab
        (if scope = SharedOnly then instr else []) (* no refinement *)
        (sprintf "%s-hidden.txt" out_name) in
    let procs = Program.get_procs prog in
    let bymc_use, bymc_loc, bymc_proc =
        create_aux_vars new_type_tab main_sym_tab (List.length procs) hidden in
    let orig_shared = Program.get_shared intabs_prog in
    let shared_and_aux = bymc_loc :: bymc_use :: bymc_proc :: shared in
    let vars = shared_and_aux @ (Program.get_all_locals prog) in
    let _ = List.fold_left (intro_old_copies new_type_tab main_sym_tab rev_tab)
        shared [bymc_use; bymc_loc; bymc_proc] in
    let out = open_out (out_name ^ ".smv") in
    write_smv_header new_type_tab main_sym_tab shared_and_aux hidden_idx_fun out; 

    let make_init procs =
        let add_init_section accum proc =
            log INFO (sprintf "  add init %s" proc#get_name);
            let reg_tbl = caches#struc#get_regions proc#get_name in
            (reg_tbl#get "decl" proc#get_stmts)
                @ (reg_tbl#get "init" proc#get_stmts) @ accum
        in
        (* XXX: fix the initial states formula for several processes! *)
        let proc_sym_tab = new symb_tab "all" in
        proc_sym_tab#set_parent main_sym_tab;
        let proc_type_tab = new_type_tab#copy in
        (* cat all init sections in one *)
        (* XXX: it will break for tricky
           interdependencies between init sections *)
        let all_locals =
            List.fold_left (fun a p -> p#get_locals @ a) [] procs in
        let all_stmts = List.fold_left add_init_section [] procs in
        let _ =
            transform_vars type_tab proc_type_tab proc_sym_tab rev_tab all_locals
        in
        let tracked_vars = bymc_use :: shared in
        fprintf out "-- Processes: %s\n"
            (str_join ", " (List.map (fun p -> p#get_name) procs));
            let _ = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab tracked_vars hidden_idx_fun
                (smv_name proc_sym_tab) all_stmts out "init" "INIT" in
        ()
    in
    let make_constraints proc_num proc =
        let locals = find_proc_non_scratch caches proc in
        let local_shared = bymc_loc :: locals @ orig_shared in
        let proc_sym_tab, proc_type_tab =
            intro_in_out_vars main_sym_tab new_type_tab rev_tab prog proc local_shared
        in
        let in_locals, out_locals = get_in_out proc_sym_tab locals in
        write_constraints solver caches proc_sym_tab proc_type_tab
            hidden_idx_fun out proc_num proc in_locals out_locals
    in
    let make_proc_trans proc_num proc =
        log INFO (sprintf "  add trans %s" proc#get_name);
        let locals = find_proc_non_scratch caches proc in
        let local_shared = locals @ orig_shared in
        let proc_sym_tab, proc_type_tab =
            intro_in_out_vars main_sym_tab new_type_tab rev_tab prog proc local_shared
        in
        let in_locals, out_locals = get_in_out proc_sym_tab locals in
        let local_ids = collect_local_ids in_locals out_locals in

        let vname v = v#mangled_name in
        fprintf out "MODULE %s(%s, %s, %s)\n" proc#get_name
            (str_join ", " (List.map vname in_locals))
            (str_join ", " (List.map vname out_locals))
            (str_join ", " (List.map vname (bymc_loc :: bymc_proc :: orig_shared)));
        (* TODO: allow other processes to make a step too!  *)
        fprintf out "INIT\n";
        fprintf out "  (%s)\n"
            (assign_default proc_type_tab (in_locals @ out_locals));

        (* generate the invariant without globals *)
        let reg_tab = extract_skel proc#get_stmts in
        let loop_prefix = reg_tab#get "loop_prefix" proc#get_stmts in
        let loop_body = reg_tab#get "loop_body" proc#get_stmts in
        let body = loop_body @ loop_prefix in
        fprintf out "INVAR\n";
        fprintf out "  (bymc_loc != 0 | (bymc_loc = 0) & (%s))\n"
            (assign_default proc_type_tab (in_locals @ out_locals));
        fprintf out "-- Process %d: %s\n" proc_num proc#get_name;
        fprintf out " & ((bymc_loc != 1) | (bymc_proc != %d) | ((bymc_loc = 1) & (bymc_proc = %d) & (FALSE\n"
            proc_num proc_num;
        let _ = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab locals hidden_idx_fun (local_one_step local_ids)
            body out proc#get_name "TRANS" in
        fprintf out ")))\n";

        (* and the transition relation with globals *)
        fprintf out "TRANS\n";
        fprintf out "  (bymc_loc != 0 | (next(bymc_loc) = 1) & (%s))\n"
            (assign_default proc_type_tab (in_locals @ out_locals));
        fprintf out "-- Process %d: %s\n" proc_num proc#get_name;
        fprintf out " & ((bymc_loc != 1) | (bymc_proc != %d) | ((bymc_loc = 1) & (bymc_proc = %d) & (FALSE\n"
            proc_num proc_num;
        let num = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab local_shared hidden_idx_fun (local_one_step local_ids)
            body out proc#get_name "TRANS" in
        fprintf out ")))\n";

        (* now write modules specific to each counter *)
        write_counter_mods solver caches proc_sym_tab proc_type_tab
                hidden_idx_fun out proc_num proc in_locals out_locals;
        num
    in
    let make_trackers proc_num proc =
        let locals = find_proc_non_scratch caches proc in
        let local_shared = bymc_loc :: locals @ orig_shared in
        let proc_sym_tab, proc_type_tab =
            intro_in_out_vars main_sym_tab new_type_tab rev_tab prog proc local_shared
        in
        let in_locals, out_locals = get_in_out proc_sym_tab locals in
        (* and the module to track the used variables *)
        write_counter_use solver caches proc_sym_tab proc_type_tab
                hidden hidden_idx_fun out proc_num proc in_locals out_locals;
    in
    let write_trackers all_locals =
        let vname v = v#mangled_name in
        let hid = List.map hidden_idx_fun hidden in
        let ps = str_join ", " (List.map vname all_locals) in
        fprintf out "MODULE trackers(use, bymc_proc, bymc_loc, %s)\n" ps;
        fprintf out " ASSIGN\n";
        fprintf out " next(use) :=\n";
        fprintf out "  case\n";
        List.iter2 make_trackers (range 0 (List.length procs)) procs;
        fprintf out "   bymc_loc = 0 : { %s };\n"
            (str_join ", " (List.map string_of_int (0 :: hid)));
        fprintf out "   TRUE : use;\n";
        fprintf out "  esac;\n"

    in
    let collect_locals lst proc_num proc =
        let locals = find_proc_non_scratch caches proc in
        let local_shared = bymc_loc :: locals @ orig_shared in
        let proc_sym_tab, proc_type_tab =
            intro_in_out_vars main_sym_tab new_type_tab rev_tab prog proc local_shared
        in
        let in_locals, out_locals = get_in_out proc_sym_tab locals in
        in_locals @ out_locals @ lst
    in
    let all_locals =
        List.fold_left2 collect_locals [] (range 0 (List.length procs)) procs
    in
    List.iter
        (declare_locals_and_counters caches main_sym_tab new_type_tab rev_tab
            prog (bymc_loc :: bymc_proc :: orig_shared) all_locals
            hidden_idx_fun out)
        (Program.get_procs prog);
    let ps = str_join ", " (List.map (fun v -> v#mangled_name) all_locals) in
    fprintf out "  mod_ctrs_use: trackers(bymc_use, bymc_proc, bymc_loc, %s);\n" ps;
    fprintf out "INIT\n";
    write_default_init new_type_tab main_sym_tab
        (bymc_proc :: shared) hidden_idx_fun out;
    List.iter2 make_constraints
        (range 0 (List.length procs)) (Program.get_procs intabs_prog);

    fprintf out "TRANS\n\n";
    (* initialization is now made as a first step! *)
    fprintf out " ((bymc_loc = 0 & next(bymc_loc) = 1 & (FALSE\n";
    make_init (Program.get_procs prog);
    fprintf out " ))";
    fprintf out " | (bymc_loc = 1 & next(bymc_loc) = 1));\n";
    (* XXX: doubtful...
    fprintf out "\n-- prevent stuttering (safety only)\n";
    fprintf out " & (bymc_loc != 1 | %s);\n" (nostuttering shared);
    *)
    fprintf out "\n\n-- specifications\n";
    let atomics = Program.get_atomics prog in
    let _ = Program.StringMap.mapi
        (write_ltl_spec out atomics new_type_tab main_sym_tab hidden_idx_fun)
        (Program.get_ltl_forms prog) in

    write_hidden_spec hidden out;

    fprintf out "\n\n-- auxillary modules\n";

    let procs = Program.get_procs intabs_prog in
    let no_paths = List.map2 make_proc_trans (range 0 (List.length procs)) procs
    in
    let _ = List.fold_left (+) 0 no_paths in
    write_trackers all_locals;

    (* the receive-compute-update block *)
    (*write_trans_loop vars hidden_idx_fun out;*)
    close_out out

