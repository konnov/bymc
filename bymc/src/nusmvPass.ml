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
    List.map (fun (k, v) -> v) (IntMap.bindings m)


type scope_vars_t = LocalShared | SharedOnly


(* ======= The new symbolic implementation. ===========================
           It is much more efficient than that one above.                 *)

let intro_old_copies new_type_tab new_sym_tab collected var =
    let nv = new var ("O" ^ var#mangled_name) (fresh_id ()) in
    let _ = new_type_tab#set_type nv (new_type_tab#get_type var) in
    new_sym_tab#add_symb nv#mangled_name (nv :> symb);
    nv :: collected


let transform_vars prog old_type_tab new_type_tab new_sym_tab vars =
(* XXX: similar to Simplif.flatten_array_decl *)
    let flatten_array_var collected var =
        let tp = old_type_tab#get_type var in
        let decl_elem_var lst i =
            let nv = var#fresh_copy (SymbExec.indexed_var var i) in
            let nt = tp#copy in
            nt#set_nelems 1;
            new_type_tab#set_type nv nt;
            new_sym_tab#add_symb nv#mangled_name (nv :> symb);
            nv :: lst
        in
        if tp#is_array
        then List.fold_left decl_elem_var collected (range 0 tp#nelems)
        else begin
            new_type_tab#set_type var (old_type_tab#get_type var);
            new_sym_tab#add_symb var#mangled_name (var :> symb);
            var :: collected
        end
    in
    let unfolded = List.fold_left flatten_array_var [] vars in
    let _ =
        List.fold_left (intro_old_copies new_type_tab new_sym_tab) [] unfolded
    in
    List.rev unfolded


let create_aux_vars new_type_tab new_sym_tab hidden =
    let var_use = new var "bymc_use" (fresh_id ()) in
    new_sym_tab#add_symb var_use#mangled_name (var_use :> symb);
    let use_tp = new data_type SpinTypes.TINT in
    use_tp#set_range 0 (1 + (List.length hidden));
    new_type_tab#set_type var_use use_tp;
    let var_loc = new var "bymc_loc" (fresh_id ()) in
    new_sym_tab#add_symb var_loc#mangled_name (var_loc :> symb);
    let init_tp = new data_type SpinTypes.TINT in
    init_tp#set_range 0 2;
    new_type_tab#set_type var_loc init_tp;
    (var_use, var_loc)


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
        new_type_tab new_sym_tab vars hidden body out name section =
    log INFO (sprintf "  mk_cfg...");
    let lirs = mir_to_lir body in
    let cfg = mk_cfg lirs in
    Cfg.write_dot (sprintf "%s-%s.dot" name section) cfg;
    let path_efun = enum_paths cfg in

    solver#set_need_evidence false;
    log INFO (sprintf "  constructing symbolic paths...");
    let num_paths =
        path_efun (exec_path solver out
            new_type_tab new_sym_tab vars hidden (section = "INIT"))
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


let create_read_hidden (sym_tab: symb_tab) (shared: var list) (filename: string) =
    (* XXX: we should definitely use batteries here *)
    let file_exists =
        try Unix.access filename [Unix.F_OK]; true
        with (Unix.Unix_error (_, _, _)) -> false
    in
    let hidden =
        if not file_exists
        then begin
            let fout = open_out filename in
            List.iter (fun v -> fprintf fout "%s\n" v#mangled_name) shared;
            close_out fout;
            shared
        end else 
            let vars = ref [] in
            let fin = open_in filename in
            try
                while true; do
                    let line = input_line fin in
                    let sym = sym_tab#lookup line in
                    vars := (sym#as_var :: !vars)
                done;
                List.rev !vars
            with End_of_file ->
                close_in fin;
                printf "    %d variables are hidden\n" (List.length !vars);
                List.rev !vars
    in
    let hidden_tab = Hashtbl.create (List.length hidden) in
    List.iter2 (fun n v -> Hashtbl.add hidden_tab v#id n)
        (range 1 (1 + (List.length hidden))) hidden;
    (* If the variable is hidden, return its positive index in the table.
       Otherwise, return 0.
    *)
    let hidden_fun v =
        try Hashtbl.find hidden_tab v#id
        with Not_found -> 0
    in
    (hidden, hidden_fun)


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
        fprintf out "SPEC AG (bymc_use != %d);\n" (1 + n)
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
            then (* try a chance to use a faster algorithm *)
                fprintf out " -- INVARSPEC NAME %s := (%s);\n\n"
                    name (Nusmv.expr_s (fun v -> v#get_name) f)
            else fprintf out " -- LTLSPEC NAME %s := (%s);\n\n"
                name (Nusmv.expr_s (fun v -> v#get_name) tf)

        | _ as tf ->
            fprintf out " -- LTLSPEC NAME %s := (%s);\n\n"
                name (Nusmv.expr_s (fun v -> v#get_name) tf)

    end else begin
        let write = function
        | UnEx (ALWAYS, UnEx (EVENTUALLY, f)) as ff ->
            if Ltl.is_propositional type_tab f
            then fprintf out " -- JUSTICE (%s);\n\n"
                    (Nusmv.expr_s (fun v -> v#get_name) f)
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
    let shared = transform_vars prog type_tab new_type_tab new_sym_tab
        ((Program.get_shared prog) @ (Program.get_instrumental prog)) in
    let hidden, hidden_idx_fun =
        create_read_hidden new_sym_tab
        (if scope = SharedOnly then shared else [] (* no refinement *))
        (sprintf "%s-hidden.txt" out_name) in
    let bymc_use, bymc_loc =
        create_aux_vars new_type_tab new_sym_tab hidden in
    let vars = bymc_loc :: bymc_use :: shared in
    let vars = if (scope = LocalShared)
        then vars @ (Program.get_all_locals prog) else vars in
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
        let _ = transform_vars prog type_tab proc_type_tab proc_sym_tab
            all_locals in
        fprintf out "-- Processes: %s\n"
            (str_join ", " (List.map (fun p -> p#get_name) procs));
        let _ = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab vars hidden_idx_fun all_stmts out "init" "INIT" in
        ()
    in
    let make_trans proc =
        let proc_sym_tab = new symb_tab proc#get_name in
        proc_sym_tab#set_parent new_sym_tab;
        let proc_type_tab = new_type_tab#copy in
        let _ = transform_vars prog type_tab proc_type_tab proc_sym_tab
            proc#get_locals in
        fprintf out "-- Process: %s\n" proc#get_name;
        fprintf out " | (FALSE\n";
        let reg_tbl = caches#struc#get_regions proc#get_name in
        let loop_prefix = reg_tbl#get "loop_prefix" proc#get_stmts in
        let loop_body = reg_tbl#get "loop_body" proc#get_stmts in
        let body = loop_body @ loop_prefix in
        let num = proc_to_symb solver caches prog proc_type_tab
            proc_sym_tab vars hidden_idx_fun body out proc#get_name "TRANS" in
        fprintf out ")\n";
        num
    in
    fprintf out "INIT\n";
    write_default_init new_type_tab new_sym_tab shared hidden_idx_fun out;
    fprintf out "TRANS\n  FALSE\n";
    (* initialization is now made as a first step! *)
    make_init (Program.get_procs prog);
    let no_paths = List.map make_trans (Program.get_procs prog) in
    let _ = List.fold_left (+) 0 no_paths in
    (* the receive-compute-update block *)
    write_trans_loop vars hidden_idx_fun out;

    write_hidden_spec hidden out;
    fprintf out "\n-- specifications\n";
    let atomics = Program.get_atomics prog in
    let _ = Program.StringMap.mapi
        (write_ltl_spec out atomics new_type_tab new_sym_tab hidden_idx_fun)
        (Program.get_ltl_forms prog) in
    close_out out

