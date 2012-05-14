(* Write Promela code from its intermediate representation *)

open Printf;;

open Spin_ir;;
open Spin_ir_imp;;
open Spin_types;;

let indent level = String.make level ' ';;

let var_type_promela tp =
    match tp with
      TBIT -> "bit"
      | TBYTE -> "byte"
      | TSHORT -> "short"
      | TINT -> "int"
      | TUNSIGNED -> "unsigned"
      | TCHAN -> "chan"
      | TMTYPE -> "mtype"
;;

let write_stmt cout level s =
    match s with
    | Expr e -> fprintf cout "%s%s;\n" (indent level) (expr_s e)
    | Decl (v, i) ->
        fprintf cout "%s%s %s%s;\n" (indent level)
            (var_type_promela v#get_type) v#get_name
            (if i != Nop then " = " ^ (expr_s i) else "")
    | Label lab -> fprintf cout "lab%d:\n" lab
    | Else -> fprintf cout "else ->\n"
    | Atomic_beg -> fprintf cout "%satomic {\n" (indent level)
    | Atomic_end -> fprintf cout "%s} /* atomic */\n" (indent level)
    | D_step_beg -> fprintf cout "%sd_step {\n" (indent level)
    | D_step_end -> fprintf cout "%s} /* d_step */\n" (indent level)
    | Assert e -> fprintf cout "%sassert(%s);\n" (indent level) (expr_s e)
    | Assume e -> fprintf cout "%sassume(%s);\n" (indent level) (expr_s e)
    | Print (frmt, args) -> fprintf cout "%sprintf(\"%s\", %s); */\n"
        (indent level) frmt (Accums.str_join ", " (List.map expr_s args))
    | _ -> ()
;;

let rec write_cfg_blocks cout blocks level guard_first stop_lab blk =
    let is_stop_lab s =
        match s with
        | Label i -> i = stop_lab
        | _ -> false
    in
    if not blk#get_visit_flag && not (List.exists is_stop_lab blk#get_seq)
    then begin
        if guard_first then fprintf cout "%s::" (indent level);
        let skip_lab = ref guard_first in (* skip leading labels *)
        blk#set_visit_flag true;
        let visit_stmt s =
            match s with
            | Goto lab ->
                if lab <> stop_lab
                then begin
                    fprintf cout "%sgoto lab%d;\n" (indent level) lab;
                    (* actually, one successor *)
                    List.iter
                        (write_cfg_blocks cout blocks level false stop_lab)
                        blk#get_succ
                end
                (* else ignore, it is the exit from a guarded option of if *)
            | If (_, exit_lab) ->
                (* if/fi does not allow us to use a depth-first search *)
                fprintf cout "%sif\n" (indent level);
                List.iter
                    (write_cfg_blocks cout blocks (level + 2) true exit_lab)
                    blk#get_succ;
                fprintf cout "%sfi;\n" (indent level);
                write_cfg_blocks cout blocks level false stop_lab
                    (Hashtbl.find blocks exit_lab)
            | Label _ ->
                if not !skip_lab
                then write_stmt cout level s;
            | _ -> write_stmt cout (if !skip_lab then 2 else level) s;
                skip_lab := false
        in
        List.iter visit_stmt blk#get_seq
    end
;;
  
let write_proc cout level p =
    let tab = indent level in
    if p#get_active_expr != Nop
    then fprintf cout "%sactive[%s] " tab (expr_s p#get_active_expr);
    let args_s = Accums.str_join ", "
        (List.map
            (fun v -> (var_type_promela v#get_type) ^ " " ^ v#get_name)
        p#get_args) in
    fprintf cout "proctype %s(%s) {\n" p#get_name args_s;
    let blocks = Cfg.mk_cfg p#get_stmts in
    Hashtbl.iter (fun _ blk -> printf "%s\n" blk#str) blocks;
    write_cfg_blocks cout blocks (level + 2) false (-1) (Hashtbl.find blocks 0);
    Hashtbl.iter (fun _ blk -> blk#set_visit_flag false) blocks;
    fprintf cout "%s}\n" tab;
;;

let write_unit cout level u =
    match u with
    | Stmt s -> write_stmt cout level s
    | Proc p -> write_proc cout level p
    | _ -> ()
;;
