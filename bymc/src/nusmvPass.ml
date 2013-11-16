(*
  This pass transforms Promela code into Nusmv representation using
  symbolic execution.

  Igor Konnov, 2012
 *)

open Printf

open Accums
open Cfg
open CfgSmt
open Debug
open RevTrans
open Simplif
open Spin
open SpinIr
open SpinIrImp
open Ssa
open SymbExec
open VarRole

exception Bdd_error of string

module StringMap = Map.Make(String)

module IntMap = Map.Make (struct
 type t = int
 let compare a b = a - b
end)


let intmap_vals m =
    (* backport to 3.10.2 *)
    IntMap.fold (fun _ v a -> v :: a) m []
    (* the new code, which is no better:
    List.map (fun (k, v) -> v) (IntMap.bindings m) *)


type scope_vars_t = LocalShared | SharedOnly


(* ======= The new symbolic implementation. ===========================
           It is much more efficient than that one above.                 *)

let intro_old_copies new_type_tab new_sym_tab rev_tab collected var =
    let nv = new var (SymbExec.mk_input_name var) (fresh_id ()) in
    (* this will not work as we need a flat name, i.e., one without
       process name: *)
    let _ = new_type_tab#set_type nv (new_type_tab#get_type var) in
    new_sym_tab#add_symb nv#mangled_name (nv :> symb);
    rev_tab#bind nv (Var var);
    nv :: collected


let transform_vars old_type_tab new_type_tab new_sym_tab rev_tab vars =
(* XXX: similar to Simplif.flatten_array_decl *)
    let flatten_array_var collected var =
        let tp = old_type_tab#get_type var in
        let decl_elem_var lst i =
            let nv = var#fresh_copy (SymbExec.indexed_var var i) in
            let nt = tp#copy in
            nt#set_range_tuple tp#range;
            nt#set_nelems 1;
            new_type_tab#set_type nv nt;
            new_sym_tab#add_symb nv#mangled_name (nv :> symb);
            rev_tab#bind nv (BinEx (ARR_ACCESS, Var var, Const i));
            nv :: lst
        in
        if tp#is_array
        then List.fold_left decl_elem_var collected (range 0 tp#nelems)
        else begin
            new_type_tab#set_type var (old_type_tab#get_type var);
            new_sym_tab#add_symb var#mangled_name (var :> symb);
            rev_tab#bind var (Var var);
            var :: collected
        end
    in
    let unfolded = List.fold_left flatten_array_var [] vars in
    let _ = List.fold_left
            (intro_old_copies new_type_tab new_sym_tab rev_tab) [] unfolded in
    List.rev unfolded


let create_aux_vars new_type_tab new_sym_tab num_procs hidden =
    let var_use = new var "bymc_use" (fresh_id ()) in
    new_sym_tab#add_symb var_use#mangled_name (var_use :> symb);
    let use_tp = new data_type SpinTypes.TINT in
    use_tp#set_range 0 (1 + (List.length hidden));
    new_type_tab#set_type var_use use_tp;

    let var_loc = new var "bymc_loc" (fresh_id ()) in
    new_sym_tab#add_symb var_loc#mangled_name (var_loc :> symb);
    let init_tp = new data_type SpinTypes.TINT in
    init_tp#set_range 0 3;
    new_type_tab#set_type var_loc init_tp;

    let var_typ = new var "bymc_proc" (fresh_id ()) in
    new_sym_tab#add_symb var_typ#mangled_name (var_typ :> symb);
    let typ_tp = new data_type SpinTypes.TINT in
    typ_tp#set_range 0 num_procs;
    new_type_tab#set_type var_typ typ_tp;
    (var_use, var_loc, var_typ)


let write_smv_header new_type_tab new_sym_tab shared hidden_idx_fun out =
    let decl_var v = 
        let tp = new_type_tab#get_type v in
        if (hidden_idx_fun v) <> 0
        then fprintf out "  -- %s: %s;\n" v#mangled_name (Nusmv.var_type_smv tp)
        else fprintf out "  %s: %s;\n" v#mangled_name (Nusmv.var_type_smv tp)
    in
    fprintf out "MODULE main\nVAR\n";
    List.iter decl_var shared


let proc_to_symb solver caches prog 
        new_type_tab new_sym_tab vars hidden name_f body out name section =
    log INFO (sprintf "  mk_cfg...");
    let lirs = mir_to_lir body in
    let cfg = mk_cfg lirs in
    Cfg.write_dot (sprintf "%s-%s.dot" name section) cfg;
    let path_efun = enum_paths cfg in

    solver#set_need_evidence false;
    log INFO (sprintf "  constructing symbolic paths...");
    let num_paths =
        path_efun (exec_path solver out new_type_tab new_sym_tab vars hidden name_f)
    in
    Printf.printf "    enumerated %d paths\n" num_paths;
    num_paths


let write_trans_loop vars hidden_idx_fun out =
    Printf.printf "WARNING: added a loop to TRANS\n";
    let keep sym =
        let v = sym#as_var in
        if (hidden_idx_fun v) <> 0
        then ""
        else Printf.sprintf "next(%s)=%s" v#mangled_name v#mangled_name
    in
    let keep_s = str_join " & "
        (List.filter (fun s -> s <> "") (List.map keep vars)) in
    Printf.fprintf out " -- a self loop to ensure totality\n";
    Printf.fprintf out " | bymc_loc = 1 & (%s)\n" keep_s


let create_or_read_names (default: string list) (filename: string) =
    (* XXX: we should definitely use batteries here *)
    let file_exists =
        try Unix.access filename [Unix.F_OK]; true
        with (Unix.Unix_error (_, _, _)) -> false
    in
    let hidden =
        if not file_exists
        then begin
            let fout = open_out filename in
            List.iter (fun s -> fprintf fout "%s\n" s) default;
            close_out fout;
            default
        end else 
            let names = ref [] in
            let fin = open_in filename in
            try
                while true; do
                    let line = input_line fin in
                    names := (line :: !names)
                done;
                List.rev !names
            with End_of_file ->
                close_in fin;
                List.rev !names
    in
    hidden


let create_read_hidden (sym_tab: symb_tab) (shared: var list) (filename: string) =
    let default = List.map (fun v -> v#mangled_name) shared in
    let names = create_or_read_names default filename in
    let vars = List.map (fun s -> (sym_tab#lookup s)#as_var) names in
    let hidden_tab = Hashtbl.create (List.length vars) in
    List.iter2 (fun n v -> Hashtbl.add hidden_tab v#id n)
        (range 1 (1 + (List.length vars))) vars;
    (* If the variable is hidden, return its positive index in the table.
       Otherwise, return 0. *)
    let hidden_fun v =
        try Hashtbl.find hidden_tab v#id
        with Not_found -> 0
    in
    (vars, hidden_fun)


let write_default_init new_type_tab new_sym_tab shared hidden_idx_fun out =
    let init_var v = 
        let tp = new_type_tab#get_type v in
        if (hidden_idx_fun v) <> 0
        then ""
        else sprintf "%s = %s" v#mangled_name (Nusmv.type_default_smv tp)
    in
    let conds = List.filter str_nempty (List.map init_var shared) in
    let eq_s = str_join " & " ("bymc_use = 0" :: "bymc_loc = 0" :: conds) in
    fprintf out "  %s\n" eq_s


let write_hidden_spec hidden out =
    let write n =
        fprintf out "INVARSPEC (bymc_use != %d);\n" (1 + n)
    in
    List.iter write (range 0 (List.length hidden))


let write_ltl_spec out atomics type_tab sym_tab hidden_idx_fun name ltl_form =
    let rec rewrite = function
    | Var v as e ->
        if (hidden_idx_fun v) = 0
        then e
        else Const 0 (* unreachable *)

    | BinEx (EQ, Var v, Const i) as e ->
        if (hidden_idx_fun v) = 0
        then e
        (* then we know it is unreachable *)
        else if i > 0 then Const 0 else Const 1

    | BinEx (NE, Var v, Const i) as e ->
        if (hidden_idx_fun v) = 0
        then e
        (* then we know it is unreachable *)
        else if i > 0 then Const 1 else Const 0

    | BinEx (t, l, r) -> BinEx (t, rewrite l, rewrite r)

    | UnEx (t, r) -> UnEx (t, rewrite r)

    | _ as e -> e
    in
    let embedded = Ltl.embed_atomics type_tab atomics ltl_form in
    let flat = elim_array_access sym_tab embedded in
    let hidden_masked = compute_consts (rewrite flat) in
    if not (Ltl.is_fairness_form name)
    then begin
        match hidden_masked with
        | UnEx (ALWAYS, f) as tf ->
            if Ltl.is_propositional type_tab f
            then (* use a faster algorithm *)
                fprintf out " INVARSPEC NAME %s := (%s);\n\n"
                    name (Nusmv.form_s f)
            else fprintf out " LTLSPEC NAME %s := (%s);\n\n"
                name (Nusmv.form_s tf)

        | _ as tf ->
            fprintf out " LTLSPEC NAME %s := (%s);\n\n"
                name (Nusmv.form_s tf)

    end else begin
        let write = function
        | UnEx (ALWAYS, UnEx (EVENTUALLY, f)) as ff ->
            if Ltl.is_propositional type_tab f
            then fprintf out " JUSTICE (%s);\n\n"
                    (Nusmv.form_s f)
            else raise (Bdd_error ("Unsupported fairness: " ^ (expr_s ff)))

        | _ as ff ->
            printf "WARN: unsupported fairness type (ignored): %s\n"
                (expr_s ff)
        in
        let tab = Hashtbl.create 1 in
        Hashtbl.add tab name hidden_masked;
        List.iter write (Ltl.collect_fairness_forms tab)
    end


(* create a monolithic encoding in nusmv (requires a lot of memory) *)
let transform solver caches scope out_name prog =
    let type_tab = Program.get_type_tab prog in
    let new_type_tab = type_tab#copy in
    let new_sym_tab = new symb_tab "main" in
    let rev_tab = new retrans_tab in
    let shared = transform_vars type_tab new_type_tab new_sym_tab rev_tab
        ((Program.get_shared prog) @ (Program.get_instrumental prog)) in
    let hidden, hidden_idx_fun =
        create_read_hidden new_sym_tab
        (if scope = SharedOnly then shared else [] (* no refinement *))
        (sprintf "%s-hidden.txt" out_name) in
    let procs = Program.get_procs prog in
    let bymc_use, bymc_loc, bymc_proc =
        create_aux_vars new_type_tab new_sym_tab (List.length procs) hidden in
    let vars = bymc_loc :: bymc_use :: bymc_proc :: shared in
    let vars = if (scope = LocalShared)
        then vars @ (Program.get_all_locals prog) else vars in
    let _ = List.fold_left (intro_old_copies new_type_tab new_sym_tab rev_tab)
        shared [bymc_use; bymc_loc; bymc_proc] in
    let out = open_out (out_name ^ ".smv") in
    write_smv_header new_type_tab new_sym_tab vars hidden_idx_fun out; 

    let add_locals proc =
        let _ = transform_vars type_tab new_type_tab new_sym_tab
            rev_tab proc#get_locals in
        ()
    in
    List.iter add_locals (Program.get_procs prog);

    let make_init prog procs =
        let add_init_section accum proc =
            log INFO (sprintf "  add mono init for %s" proc#get_name);
            let reg_tbl =
                (caches#find_struc prog) #get_regions proc#get_name in
            (reg_tbl#get "decl" proc#get_stmts)
                @ (reg_tbl#get "init" proc#get_stmts) @ accum
        in
        (* XXX: fix the initial states formula for several processes! *)
        (*
        let proc_sym_tab = new symb_tab "all" in
        proc_sym_tab#set_parent new_sym_tab;
        let proc_type_tab = new_type_tab#copy in
        *)
        let proc_type_tab = new_type_tab in
        let proc_sym_tab = new_sym_tab in
        (* cat all init sections in one *)
        (* XXX: it will break for tricky
           interdependencies between init sections *)
        let all_locals =
            List.fold_left (fun a p -> p#get_locals @ a) [] procs in
        let all_stmts = List.fold_left add_init_section [] procs in
        let _ = transform_vars type_tab proc_type_tab proc_sym_tab rev_tab all_locals
        in
        fprintf out "-- Processes: %s\n"
            (str_join ", " (List.map (fun p -> p#get_name) procs));
        let _ = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab vars hidden_idx_fun (smv_name proc_sym_tab) all_stmts out "init" "INIT" in
        ()
    in
    let make_mono_trans proc =
        log INFO (sprintf "  add mono trans for %s" proc#get_name);
        let proc_type_tab = new_type_tab in
        let proc_sym_tab = new_sym_tab in
        fprintf out "-- Process: %s\n" proc#get_name;
        fprintf out " | (FALSE\n";
        let reg_tbl = (caches#find_struc prog)#get_regions proc#get_name in
        let loop_prefix = reg_tbl#get "loop_prefix" proc#get_stmts in
        let loop_body = reg_tbl#get "loop_body" proc#get_stmts in
        let body = loop_body @ loop_prefix in
        let num = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab vars hidden_idx_fun (smv_name proc_sym_tab) body out proc#get_name "TRANS" in
        fprintf out ")\n";
        num
    in
    fprintf out "INIT\n";
    write_default_init new_type_tab new_sym_tab shared hidden_idx_fun out;
    fprintf out "TRANS\n  (bymc_loc = 0 & next(bymc_loc) = 1) & (FALSE\n";
    (* initialization is now made as a first step! *)
    make_init prog (Program.get_procs prog);
    fprintf out ") | \n";
    fprintf out "(bymc_loc = 1 & next(bymc_loc) = 1) & (FALSE\n";
    let no_paths = List.map make_mono_trans (Program.get_procs prog) in
    let _ = List.fold_left (+) 0 no_paths in
    (* the receive-compute-update block *)
    write_trans_loop vars hidden_idx_fun out;
    fprintf out ")\n";

    write_hidden_spec hidden out;
    fprintf out "\n-- specifications\n";
    let atomics = Program.get_atomics_map prog in
    let _ = Accums.StringMap.mapi
        (write_ltl_spec out atomics new_type_tab new_sym_tab hidden_idx_fun)
        (Program.get_ltl_forms prog) in
    close_out out

