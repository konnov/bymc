(*
  An optimized encoding of counter representation that represent each
  counter as a module. This allows nusmv to use clusters, which are much
  more efficient for large models.

  Igor Konnov, 2013
 *)

open Printf

open AbsBasics
open Accums
open Nusmv
open NusmvPass
open SkelStruc
open Spin
open SpinIr
open SpinIrImp
open SymbExec
open VarRole

let collect_rhs solver dom op =
    solver#push_ctx;
    let x = new var "x" (fresh_id ()) in
    let y = new var "y" (fresh_id ()) in
    let tp = new data_type SpinTypes.TINT in
    tp#set_range 0 dom#length; (* counters are bounded *)
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


let create_proc_counters solver caches out proc =
    let ctr_ctx =
        caches#analysis#get_pia_ctr_ctx_tbl#get_ctx proc#get_name in
    let dom = caches#analysis#get_pia_dom in
    let dec_tbl = collect_rhs solver dom PLUS in
    let inc_tbl = collect_rhs solver dom MINUS in
    let create_module idx =
        let valtab = ctr_ctx#unpack_from_const idx in
        (* XXX: fix params, they should include next *)
        let params = str_join ", "
            (List.map (fun v -> v#mangled_name) (hashtbl_keys valtab)) in
        let next_name v =
            let next = ctr_ctx#get_next v in
            next#mangled_name in
        let next_params = str_join ", "
            (List.map next_name (hashtbl_keys valtab)) in
        let mk_prev con op =
            let f (k, v) = sprintf "%s %s %d" k#mangled_name op v in
            str_join con (List.map f (hashtbl_as_list valtab)) in
        let prev_eq = mk_prev " & " "=" in
        let prev_neq = mk_prev " | " "!=" in
        let mk_next con op =
            let f (k, v) =
                sprintf "%s %s %d" (ctr_ctx#get_next k)#mangled_name op v in
            str_join con (List.map f (hashtbl_as_list valtab)) in
        let next_eq = mk_next " & " "=" in
        let next_neq = mk_next " | " "!=" in
        fprintf out "MODULE kntr_%s_%d(%s, %s, myval)\n"
            proc#get_name idx params next_params;
        fprintf out " ASSIGN\n";
        fprintf out " next(myval) :=\n";
        fprintf out "  case\n";
        let print_next k vs =
            fprintf out "   (%s) & (%s) & myval = %d : { %s };\n"
                prev_neq next_eq k (str_join ", " (List.map string_of_int vs));
        in
        let print_prev k vs =
            fprintf out "   (%s) & (%s) & myval = %d : { %s };\n"
                prev_eq next_neq k (str_join ", " (List.map string_of_int vs))
        in
        Hashtbl.iter print_prev dec_tbl;
        Hashtbl.iter print_next inc_tbl;
        fprintf out "   TRUE : myval;\n";
        fprintf out "  esac;\n";
    in
    let all_indices = ctr_ctx#all_indices_for (fun _ -> true) in
    List.iter create_module all_indices


(* create a cluster encoding in nusmv (requires a lot of memory) *)
let transform solver caches out_name intabs_prog prog =
    let type_tab = Program.get_type_tab prog in
    let new_type_tab = type_tab#copy in
    let new_sym_tab = new symb_tab "main" in
    let shared = transform_vars prog type_tab new_type_tab new_sym_tab
        ((Program.get_shared prog) @ (Program.get_instrumental prog)) in
    let hidden, hidden_idx_fun =
        create_read_hidden new_sym_tab
        (*if scope = SharedOnly then shared else [] (* no refinement *)*)
        []
        (sprintf "%s-hidden.txt" out_name) in
    let bymc_use, bymc_loc =
        create_aux_vars new_type_tab new_sym_tab hidden in
    let vars = bymc_loc :: bymc_use :: shared in
    let vars = vars @ (Program.get_all_locals prog) in
    let _ = List.fold_left (intro_old_copies new_type_tab new_sym_tab)
        shared [bymc_use; bymc_loc] in
    let out = open_out (out_name ^ ".smv") in
    write_smv_header new_type_tab new_sym_tab vars hidden_idx_fun out; 
    let make_init procs =
        let add_init_section accum proc =
            let reg_tbl = caches#struc#get_regions proc#get_name in
            (reg_tbl#get "decl" proc#get_stmts)
                @ (reg_tbl#get "init" proc#get_stmts) @ accum
        in
        (* XXX: fix the initial states formula for several processes! *)
        let proc_sym_tab = new symb_tab "all" in
        proc_sym_tab#set_parent new_sym_tab;
        let proc_type_tab = new_type_tab#copy in
        (* cat all init sections in one *)
        (* XXX: it will break for tricky
           interdependencies between init sections *)
        let all_locals =
            List.fold_left (fun a p -> p#get_locals @ a) [] procs in
        let all_stmts = List.fold_left add_init_section [] procs in
        let _ = transform_vars prog type_tab proc_type_tab proc_sym_tab all_locals
        in
        fprintf out "-- Processes: %s\n"
            (str_join ", " (List.map (fun p -> p#get_name) procs));
            let _ = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab vars hidden_idx_fun (smv_name proc_sym_tab) all_stmts out "init" "INIT" in
        ()
    in
    let make_proc_trans proc =
        let roles = caches#analysis#get_var_roles in
        let locals =
            List.filter (fun v -> not (is_scratch (roles#get_role v)))
            proc#get_locals
        in
        let local_shared = locals @ (Program.get_shared intabs_prog) in
        fprintf out "MODULE %s(...)\n" proc#get_name;
        fprintf out "TRANS\n  FALSE\n";
        let proc_sym_tab = new symb_tab proc#get_name in
        proc_sym_tab#set_parent new_sym_tab;
        let proc_type_tab = new_type_tab#copy in
        let _ = transform_vars prog type_tab proc_type_tab proc_sym_tab
            local_shared in
        fprintf out "-- Process: %s\n" proc#get_name;
        fprintf out " | (FALSE\n";
        let reg_tab = extract_skel proc#get_stmts in
        let loop_prefix = reg_tab#get "loop_prefix" proc#get_stmts in
        let loop_body = reg_tab#get "loop_body" proc#get_stmts in
        let body = loop_body @ loop_prefix in
        let num = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab local_shared hidden_idx_fun keep_name body out proc#get_name "TRANS" in
        fprintf out ")\n";
        num
    in
    fprintf out "INIT\n";
    write_default_init new_type_tab new_sym_tab shared hidden_idx_fun out;
    fprintf out "TRANS\n  FALSE\n";
    (* initialization is now made as a first step! *)
    make_init (Program.get_procs prog);

    let no_paths = List.map make_proc_trans (Program.get_procs intabs_prog) in
    let _ = List.fold_left (+) 0 no_paths in
    (* the receive-compute-update block *)
    write_trans_loop vars hidden_idx_fun out;

    List.iter (create_proc_counters solver caches out) (Program.get_procs prog);

    write_hidden_spec hidden out;
    fprintf out "\n-- specifications\n";
    let atomics = Program.get_atomics prog in
    let _ = Program.StringMap.mapi
        (write_ltl_spec out atomics new_type_tab new_sym_tab hidden_idx_fun)
        (Program.get_ltl_forms prog) in
    close_out out

