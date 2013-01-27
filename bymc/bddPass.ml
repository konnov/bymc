(*
  This pass transforms a transducer into a boolean representation,
  to be used in a BDD model checker.

  Igor Konnov, 2012
 *)

open Printf

open Accums
open Cfg
open CfgSmt
open Spin
open SpinIr
open SpinIrImp
open Ssa

exception Bdd_error of string

module StringMap = Map.Make(String)

let proc_to_bdd prog proc =
    let var_len v =
        let tp = Program.get_type prog v in
        match tp#basetype with
        | SpinTypes.TBIT -> { Bits.len = 1; Bits.hidden = false }

        | SpinTypes.TINT ->
            if tp#has_range
            then { Bits.len = tp#range_len; Bits.hidden = false }
            else raise (Bdd_error (sprintf "%s is unbounded" v#get_name))

        | _ -> raise (Bdd_error
            (sprintf "Don't know how to translate %s to bdd" v#get_name))
    in
    let rec collect_expr_vars var_map = function
        | Var v ->
            (*
            Printf.printf "len(%s) == %d\n" v#qual_name (var_len v).Bits.len;
            *)
            StringMap.add v#get_name (var_len v) var_map
        | BinEx (_, l, r) ->
            collect_expr_vars (collect_expr_vars var_map l) r
        | UnEx (_, e) ->
            collect_expr_vars var_map e
        | _ ->
            var_map
    in
    let is_inout v =
        let isin =
            Str.string_match (Str.regexp ".*_IN_[0-9]+$") v 0 in
        let isout =
            Str.string_match (Str.regexp ".*_OUT_[0-9]+$") v 0 in
        isin || isout
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
    let var_map =
        List.fold_left collect_stmt_vars StringMap.empty proc#get_stmts in
    let bits = Bits.AND (List.map to_bits proc#get_stmts) in
    let form = Bits.to_sat var_map (new Sat.fresh_pool 1) bits in
    let inouts = List.filter is_inout (Sat.collect_vars form) in
    let out = open_out (sprintf "%s.bits" proc#get_name) in
    let ff = Format.formatter_of_out_channel out in
    Bits.format_bv_form ff bits;
    close_out out;
    let out = open_out (sprintf "%s.bdd" proc#get_name) in
    let ff = Format.formatter_of_out_channel out in
    Format.fprintf ff "%s" "# sat\n";
    Format.fprintf ff "(let R @,(exists [";
    List.iter (fun v -> Format.fprintf ff "%s @," v) inouts;
    Format.fprintf ff "]@, ";
    Sat.format_sat_form_polish ff form;
    Format.fprintf ff "))";
    Format.pp_print_flush ff ();
    close_out out


(* Enumerate all possible combinations of inputs and outputs. It works only
   after the counter abstraction. *)
let enum_in_outs solver caches prog proc =
    let ctr_ctx_tbl = caches#get_analysis#get_pia_ctr_ctx_tbl in
    let abbrv = (ctr_ctx_tbl#get_ctx proc#get_name)#abbrev_name in
    solver#push_ctx;
    solver#set_need_evidence true;
    solver#comment "enumerating inputs/outputs";
    let res, _ = Refinement.simulate_in_smt solver prog
        ctr_ctx_tbl [(abbrv, [(Expr (-1, Nop ""))]);
            (abbrv, [(Expr (-1, Nop ""))])] (Hashtbl.create 1) 1 in
    if res then begin
        printf "One value to take...\n";
        let vals = Refinement.parse_smt_evidence prog solver in
        Refinement.pretty_print_exprs (Hashtbl.find vals 0);
        (*Refinement.pretty_print_exprs (Hashtbl.find vals 1);*)
    end;
    solver#pop_ctx


(* this code deviates in a few moments from smtXducerPass *)
let to_xducer caches prog new_type_tab p =
    let roles = caches#get_analysis#get_var_roles in
    let is_visible v =
        match roles#get_role v with
        | VarRole.Scratch _ -> false
        | _ -> true
    in
    let reg_tbl = caches#get_struc#get_regions p#get_name in
    let loop_prefix = reg_tbl#get "loop_prefix" in
    let loop_body = reg_tbl#get "loop_body" in
    let lirs = (mir_to_lir (loop_body @ loop_prefix)) in
    let all_vars = (Program.get_shared prog)
        @ (Program.get_instrumental prog) @(Program.get_all_locals prog) in
    let vis_vs, hid_vs = List.partition is_visible all_vars in
    let cfg = mk_ssa true vis_vs hid_vs (mk_cfg lirs) in
    let transd = cfg_to_constraints p#get_name new_type_tab cfg in
    proc_replace_body p transd


let transform_to_bdd solver caches prog =
    let new_type_tab = (Program.get_type_tab prog)#copy in
    let new_procs =
        List.map (to_xducer caches prog new_type_tab) (Program.get_procs prog)
    in
    let xprog = (Program.set_type_tab new_type_tab
        (Program.set_procs new_procs prog)) in
    List.iter (proc_to_bdd xprog) new_procs;
    (* List.iter (enum_in_outs solver caches prog) (Program.get_procs prog) *)

