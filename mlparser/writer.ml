(* Write Promela code from its intermediate representation *)

open Printf;;

open Debug;;
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

let hflag_promela f =
    match f with
    | HHide -> "hide"
    | HShow -> "show"
    | HBitEquiv -> ""
    | HByteEquiv -> ":"
    | HFormalPar -> ""
    | HInlinePar -> ""
    | HTreatLocal -> "local"
    | HReadOnce -> ""
    | HSymbolic -> "symbolic"
    | HNone -> ""
;;

let rec write_stmt cout lvl s =
    let tab = (indent lvl) in
    match s with
    | MSkip _ -> fprintf cout "%sskip;\n" tab;
    | MExpr (_, e) -> fprintf cout "%s%s;\n" tab (expr_s e)
    | MDecl (_, v, e) ->
        let flags_as_s =
            (Accums.str_join " " (List.map hflag_promela v#get_flags))
        in
        fprintf cout "%s%s%s %s%s%s;\n" tab
            (if flags_as_s <> "" then flags_as_s ^ " " else "")
            (var_type_promela v#get_type) v#get_name
            (if v#get_isarray then sprintf "[%d]" v#get_num_elems else "")
            (if e != Nop then " = " ^ (expr_s e) else "")
    | MDeclProp (_, v, PropAll e) ->
            fprintf cout "#define %s ALL(%s)\n" v#get_name (expr_s e)
    | MDeclProp (_, v, PropSome e) ->
            fprintf cout "#define %s SOME(%s)\n" v#get_name (expr_s e)
    | MDeclProp (_, v, PropGlob e) ->
            fprintf cout "#define %s (%s)\n" v#get_name (expr_s e)
    | MLabel (_, l) -> fprintf cout "lab%d:\n" l
    | MAtomic (_, seq) ->
            fprintf cout "%satomic {\n" tab;
            List.iter (write_stmt cout (lvl + 2)) seq;
            fprintf cout "%s}\n" tab
    | MD_step (_, seq) ->
            fprintf cout "%sd_step {\n" tab;
            List.iter (write_stmt cout (lvl + 2)) seq;
            fprintf cout "%s}\n" tab
    | MGoto (_, l) -> fprintf cout "%sgoto lab%d;\n" tab l
    | MIf (_, opts) ->
            fprintf cout "%sif\n" tab;
            List.iter
                (function
                    | MOptGuarded seq ->
                            fprintf cout "%s  :: " tab;
                            write_stmt cout 0 (List.hd seq);
                            List.iter (write_stmt cout (lvl + 4)) (List.tl seq);

                    | MOptElse seq ->
                            fprintf cout "%s  :: else ->\n" tab;
                            List.iter (write_stmt cout (lvl + 4)) seq;
                ) opts;
            fprintf cout "%sfi;\n" tab;
    | MAssert (_, e) -> fprintf cout "%sassert(%s);\n" tab (expr_s e)
    | MAssume (_, e) -> fprintf cout "%sassume(%s);\n" tab (expr_s e)
    | MPrint (_, s, es) ->
            fprintf cout "%sprintf(\"%s\"%s);\n"
                tab s (List.fold_left (fun a e -> a ^ ", " ^ (expr_s e)) "" es)
;;
  
let write_proc cout lvl p =
    let tab = indent lvl in
    if p#get_active_expr != Nop
    then fprintf cout "\n%sactive[%s] " tab (expr_s p#get_active_expr);
    let args_s = Accums.str_join ", "
        (List.map
            (fun v -> (var_type_promela v#get_type) ^ " " ^ v#get_name)
        p#get_args) in
    fprintf cout "proctype %s(%s) {\n" p#get_name args_s;
    List.iter (write_stmt cout (lvl + 2)) p#get_stmts;
    fprintf cout "%s}\n\n" tab;
;;

let write_unit cout lvl u =
    match u with
    | Stmt s -> write_stmt cout lvl s
    | Proc p -> write_proc cout lvl p
    | _ -> ()
;;
