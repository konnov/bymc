(*
  This pass transforms a transducer into a boolean representation,
  to be used in a BDD model checker.

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


let get_main_body caches proc =
    let reg_tbl = caches#get_struc#get_regions proc#get_name in
    let loop_prefix = reg_tbl#get "loop_prefix" proc#get_stmts in
    let loop_body = reg_tbl#get "loop_body" proc#get_stmts in
    loop_body @ loop_prefix


let get_init_body caches proc =
    let reg_tbl = caches#get_struc#get_regions proc#get_name in
    (reg_tbl#get "decl" proc#get_stmts)
        @ (reg_tbl#get "init" proc#get_stmts)


(* this code deviates a lot (!) from smtXducerPass *)
let blocks_to_smt caches prog type_tab new_type_tab get_mirs_fun filename p =
    log INFO (sprintf "  blocks_to_smt %s..." filename);
    let roles = caches#get_analysis#get_var_roles in
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
   XXX: symbolic execution works much better!
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


let transform_vars prog proc type_tab =
(* XXX: similar to Simplif.flatten_array_decl *)
    let new_type_tab = type_tab#copy in
    let new_sym_tab = new symb_tab proc#get_name in
    let flatten_array_var collected var =
        let tp = type_tab#get_type var in
        let decl_elem_var lst i =
            let nv = var#fresh_copy (SymbExec.indexed_var var i) in
            let nt = tp#copy in
            nt#set_nelems 1;
            new_type_tab#set_type nv nt;
            new_sym_tab#add_symb nv#get_name (nv :> symb);
            nv :: lst
        in
        if tp#is_array
        then List.fold_left decl_elem_var collected (range 0 tp#nelems)
        else begin
            new_type_tab#set_type var (type_tab#get_type var);
            new_sym_tab#add_symb var#get_name (var :> symb);
            var :: collected
        end
    in
    let intro_old_copies collected var =
        let nv = new var ("O" ^ var#get_name) (fresh_id ()) in
        let _ = new_type_tab#set_type nv (new_type_tab#get_type var) in
        new_sym_tab#add_symb nv#get_name (nv :> symb);
        nv :: collected
    in
    let vars = (Program.get_shared prog) @ (Program.get_instrumental prog)
        @ proc#get_locals in
    let unfolded_vars = List.fold_left flatten_array_var [] vars in
    let _ = List.fold_left intro_old_copies unfolded_vars unfolded_vars in
    (new_type_tab, new_sym_tab)


let proc_to_symb solver caches prog proc block_fun filename =
    let type_tab = Program.get_type_tab prog in
    let new_type_tab, new_sym_tab = transform_vars prog proc type_tab in

    let lirs = mir_to_lir (block_fun caches proc) in
    log INFO (sprintf "  mk_cfg...");
    let cfg = mk_cfg lirs in
    Cfg.write_dot (sprintf "%s.dot" filename) cfg;
    let path_efun = enum_paths cfg in

    solver#set_need_evidence false;
    let path_no = ref 0 in
    log INFO (sprintf "  constructing symbolic paths...");
    let num_paths = path_efun (fun _ -> ()) in
    let out = open_out (filename ^ ".smv") in
    Printf.printf "    %d paths to construct...\n" num_paths;
    let num_paths = path_efun (exec_path solver out new_type_tab new_sym_tab) in
    Printf.printf "    constructed %d paths\n" num_paths;
    close_out out


let transform_to_bdd solver caches prog =
    let convert_proc proc =
        let fname = proc#get_name ^ "-I" in
        (proc_to_symb solver caches prog proc get_init_body fname);
        let fname = proc#get_name ^ "-R" in
        (proc_to_symb solver caches prog proc get_main_body fname);
        (*
        let fname = proc#get_name ^ "-I" in
        (proc_to_bdd xprog
            (blocks_to_smt caches xprog type_tab new_type_tab get_init_body fname)
            proc fname);
        let fname = proc#get_name ^ "-R" in
        (proc_to_bdd xprog
            (blocks_to_smt caches xprog type_tab new_type_tab get_main_body fname)
            proc fname)
        *)
    in
    List.iter convert_proc (Program.get_procs prog)

