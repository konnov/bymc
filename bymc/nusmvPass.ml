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


(* this code deviates a lot (!) from smtXducerPass *)
let blocks_to_smt caches prog type_tab new_type_tab get_mirs_fun filename p =
    log INFO (sprintf "  blocks_to_smt %s..." filename);
    let roles = caches#analysis#get_var_roles in
    let is_visible v =
        try begin
            match roles#get_role v with
            | VarRole.Scratch _ -> false
            | _ -> true
        end with VarRole.Var_not_found _ ->
            true
    in
    let lirs = (mir_to_lir (get_mirs_fun caches p)) in
    let all_vars = (Program.get_shared prog)
        @ (Program.get_instrumental prog) @ (Program.get_all_locals prog) in
    let vis_vs, hid_vs = List.partition is_visible all_vars in
    log INFO (sprintf "  mk_ssa...");
    let cfg = mk_cfg lirs in
    let ssa_cfg = mk_ssa true vis_vs hid_vs cfg in
    Cfg.write_dot (sprintf "%s.dot" filename) ssa_cfg;
    log INFO (sprintf "  move_phis_to_blocks...");
    let ssa_cfg = move_phis_to_blocks ssa_cfg in
    let mk_block_cons block_map block =
        let cons = block_intra_cons p#get_name type_tab new_type_tab block in
        IntMap.add block#label cons block_map
    in
    let block_cons =
        List.fold_left mk_block_cons IntMap.empty ssa_cfg#block_list in
    log INFO "DONE";
    (ssa_cfg#block_list, block_cons, (enum_paths ssa_cfg), (enum_paths cfg))


(* XXX: REWRITE EVERYTHING WHEN IT WORKS!
   XXX: symbolic execution works much better! Remove this version afterwards.
 *)
let proc_to_bdd prog smt_fun proc filename =
    let var_len v =
        let tp = Program.get_type prog v in
        match tp#basetype with
        | SpinTypes.TBIT -> { Bits.len = 1; Bits.hidden = false }

        | SpinTypes.TINT ->
            if tp#has_range
            then { Bits.len = bits_to_fit (tp#range_len - 1);
                   Bits.hidden = false }
            else raise (Bdd_error (sprintf "%s is unbounded" v#get_name))

        | _ -> raise (Bdd_error
            (sprintf "Don't know how to translate %s to bdd" v#get_name))
    in
    let rec collect_expr_vars var_map = function
        | Var v ->
            StringMap.add v#get_name (var_len v) var_map
        | BinEx (_, l, r) ->
            collect_expr_vars (collect_expr_vars var_map l) r
        | UnEx (_, e) ->
            collect_expr_vars var_map e
        | Phi (l, rs) ->
            let addv var_map v =
                StringMap.add v#get_name (var_len v) var_map in
            List.fold_left addv (addv var_map l) rs
        | _ ->
            var_map
    in
    let to_bit_vars var_map v =
        try
            let len = (StringMap.find v#get_name var_map).Bits.len in
            let bit_name i = sprintf "%s_%d" v#get_name (i + 1) in
            List.map bit_name (range 0 (bits_to_fit len))
        with Not_found -> raise (Failure ("Not_found " ^ v#get_name))
    in
    let is_hidden v =
        let isin =
            Str.string_match (Str.regexp ".*_IN_[0-9]+$") v 0 in
        let isout =
            Str.string_match (Str.regexp ".*_OUT_[0-9]+$") v 0 in
        (not isin) && (not isout)
    in
    let collect_stmt_vars var_map = function
        | MExpr (_, e) -> collect_expr_vars var_map e
        | _ -> var_map
    in
    let rec bits_of_expr pos = function
        | Var v ->
            let basetype = (Program.get_type prog v)#basetype in
            if basetype != SpinTypes.TBIT
            then raise (Bdd_error
                (sprintf "Variables %s must be boolean" v#get_name))
            else
            if pos then Bits.V v#get_name else Bits.NV v#get_name
        | BinEx (ASGN, Var v, Const i) ->
            if pos
            then Bits.VeqI (v#get_name, i)
            else Bits.VneI (v#get_name, i)
        | BinEx (EQ, Var v, Const i) ->
            if pos
            then Bits.VeqI (v#get_name, i)
            else Bits.VneI (v#get_name, i)
        | BinEx (NE, Var v, Const i) ->
            if pos
            then Bits.VneI (v#get_name, i)
            else Bits.VeqI (v#get_name, i)
        | BinEx (EQ, Var x, Var y) ->
            if pos
            then Bits.EQ (x#get_name, y#get_name)
            else Bits.NE (x#get_name, y#get_name)
        | BinEx (NE, Var x, Var y) ->
            if pos
            then Bits.NE (x#get_name, y#get_name)
            else Bits.EQ (x#get_name, y#get_name)
        | BinEx (GT, Var x, Var y) ->
            if pos
            then Bits.GT (x#get_name, y#get_name)
            else Bits.LE (x#get_name, y#get_name)
        | BinEx (GE, Var x, Var y) ->
            if pos
            then Bits.GE (x#get_name, y#get_name)
            else Bits.LT (x#get_name, y#get_name)
        | BinEx (LT, Var x, Var y) ->
            if pos
            then Bits.LT (x#get_name, y#get_name)
            else Bits.GE (x#get_name, y#get_name)
        | BinEx (LE, Var x, Var y) ->
            if pos
            then Bits.LE (x#get_name, y#get_name)
            else Bits.GT (x#get_name, y#get_name)
        | BinEx (AND, l, r) ->
            Bits.AND [bits_of_expr pos l; bits_of_expr pos r]
        | BinEx (OR, l, r) ->
            Bits.OR [bits_of_expr pos l; bits_of_expr pos r]
        | UnEx (NEG, l) ->
            bits_of_expr (not pos) l
        | Nop text ->
            Bits.ANNOTATION ("{" ^ text ^ "}", Bits.B1)
        | _ as e ->
            Bits.ANNOTATION ("skip: " ^ (expr_tree_s e), Bits.B1)
    in
    let to_bits = function
        | MExpr (_, e) ->
            bits_of_expr true e
        | _ as s -> 
            raise (Bdd_error ("Cannot convert to BDD: " ^ (mir_stmt_s s)))
    in
    let blocks, block_map, path_enum_fun, path_efun = smt_fun proc in 
    let all_stmts = List.concat (intmap_vals block_map) in
    let var_map =
        List.fold_left collect_stmt_vars StringMap.empty all_stmts in
    let all_phis = 
        List.concat (List.map (fun bb -> bb#get_phis) blocks) in
    let var_map = List.fold_left collect_expr_vars var_map all_phis in
    let var_pool = new Sat.fresh_pool 1 in
    let block_bits_map =
        IntMap.map (fun b -> Bits.AND (List.map to_bits b)) block_map in
    let block_forms_map =
        IntMap.map (Bits.to_sat var_map var_pool) block_bits_map in
    let hidden_vars =
        List.filter is_hidden (Sat.collect_vars (intmap_vals block_forms_map))
    in
    let out = open_out (sprintf "%s.bits" filename) in
    let ff = Format.formatter_of_out_channel out in
    List.iter (fun bbits -> Bits.format_bv_form ff bbits)
        (intmap_vals block_bits_map);
    close_out out;

    let out = open_out (sprintf "%s.bdd" filename) in
    let ff = Format.formatter_of_out_channel out in
    Format.fprintf ff "%s" "# sat\n";
    let out_f id form =
        Format.fprintf ff "(let B%d @," id;
        Sat.format_sat_form_polish ff form;
        Format.fprintf ff ")"; Format.pp_print_newline ff ()
    in
    IntMap.iter out_f block_forms_map;
    let path_no = ref 0 in
    let out_path path = 
        Format.fprintf ff "(let P%d @,(exists [" !path_no;
        path_no := !path_no + 1;
        List.iter (fun v -> Format.fprintf ff "%s @," v) hidden_vars;
        Format.fprintf ff "]@, (and ";
        let n_closing = ref 0 in (* collecting closing parenthesis *)
        let out_block prev_bb bb =
            (* merge basic blocks using phi functions *)
            let phis = bb#get_phis in
            if phis <> []
            then begin
                Format.fprintf ff "(sub@, [";
                (* find the position of the predecessor in the list *)
                let idx = bb#find_pred_idx prev_bb#label in
                let phi_pair = function
                | Phi (lhs, rhs) -> (lhs, (List.nth rhs idx))
                | _ -> raise (Failure ("Non-phi in basic_block#get_phis"))
                in
                let unfold_bits v =
                    List.iter
                        (Format.fprintf ff "%s ")
                        (to_bit_vars var_map v)
                in
                let pairs = List.map phi_pair phis in
                List.iter (fun (l, _) -> unfold_bits l) pairs;
                Format.fprintf ff "]@, [";
                List.iter (fun (_, r) -> unfold_bits r) pairs;
                Format.fprintf ff "]@, (and ";
                n_closing := !n_closing + 2
            end;
            Format.fprintf ff "B%d " bb#label
        in
        let preds = (List.hd path) :: (List.rev (List.tl (List.rev path)))
        in
        List.iter2 out_block preds path;
        List.iter (fun _ -> Format.fprintf ff ")") (range 0 !n_closing);
        Format.fprintf ff ")))"; Format.pp_print_newline ff ();
    in
    log INFO (sprintf "  constructing symbolic paths...");
    let num_paths = path_enum_fun (fun _ -> ()) in
    Printf.printf "    %d paths to construct...\n" num_paths;
    let num_paths = path_enum_fun out_path in
    Printf.printf "    constructed %d paths\n" num_paths;
    (* finally, add the relation *)
    Format.fprintf ff "(let R @,(or ";
    List.iter (fun i -> Format.fprintf ff "P%d " i) (range 0 num_paths);
    Format.fprintf ff "))";
    Format.pp_print_flush ff ();
    close_out out


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


let read_hidden (sym_tab: symb_tab) (shared: var list) (filename: string) =
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
            printf "ERROR: unsupported fairness type (ignored): %s\n"
                (expr_s ff)
        in
        let tab = Hashtbl.create 1 in
        Hashtbl.add tab name hidden_masked;
        List.iter write (Ltl.collect_fairness_forms tab)
    end


let transform solver caches prog =
    let type_tab = Program.get_type_tab prog in
    let new_type_tab = type_tab#copy in
    let new_sym_tab = new symb_tab "main" in
    let shared = (Program.get_shared prog) @ (Program.get_instrumental prog) in
    let shared = transform_vars prog type_tab new_type_tab new_sym_tab shared in
    let hidden, hidden_idx_fun = read_hidden new_sym_tab shared "hidden.txt"
    in
    let bymc_use, bymc_loc =
        create_aux_vars new_type_tab new_sym_tab hidden in
    let vars = bymc_loc :: bymc_use :: shared in
    let _ = List.fold_left (intro_old_copies new_type_tab new_sym_tab)
        shared [bymc_use; bymc_loc] in
    let out = open_out "main.smv" in
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

