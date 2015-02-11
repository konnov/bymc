(* Write Promela code from its intermediate representation *)

open Printf

open Accums
open Serialize
open SpinIr
open SpinIrImp
open SpinTypes

open Debug

let indent level = String.make level ' '
let rec tabify ff level =
  if level > 0
  then begin
    Format.pp_print_space ff ();
    tabify ff (level - 1)
  end

let openb ff lvl need_tab =
    let box_lvl = if need_tab then (lvl + 2) else 2 in
    Format.pp_open_hovbox ff box_lvl;
    if need_tab then tabify ff lvl

let closeb ff =
    Format.pp_close_box ff ();
    Format.pp_print_newline ff ()

(* macros have another rule for a line break *)
let macro_newl out () = out "\\\n" 0 2

let var_type_promela tp =
    let base_str = function
      | TBIT -> "bit"
      | TBYTE -> "byte"
      | TSHORT -> "short"
      | TINT -> "int"
      | TUNSIGNED -> "unsigned"
      | TCHAN -> "chan"
      | TMTYPE -> "mtype"
      | TPROPOSITION -> "proposition"
      | TUNDEF -> raise (Failure "Undefined type")
    in
    let l, r = tp#range in
    if not tp#is_array && tp#has_range && l >= 0
    then "unsigned" (* bitwidth will be specified *)
    else base_str tp#basetype


(* if we know the range of a variable, we can specify its bit width *)        
let find_bit_width v_type =
    let l, r = v_type#range in
    if v_type#has_range && l >= 0
        && not v_type#is_array && v_type#basetype <> SpinTypes.TCHAN
    then bits_to_fit r
    else 0


let hflag_promela f =
    match f with
    | HHide -> "hide"
    | HShow -> "show"
    | HBitEquiv -> ""
    | HByteEquiv -> ""
    | HFormalPar -> ""
    | HInlinePar -> ""
    | HTreatLocal -> "local"
    | HReadOnce -> ""
    | HSymbolic -> "symbolic"
    | HNext -> "next"
    | HInstrumental -> "/* instrumental */"
    | HNone -> ""


let rec write_atomic_expr ff = function
    | PropAll e ->
        Format.fprintf ff "ALL(";
        fprint_expr_mangled ff e;
        Format.pp_print_string ff ")"
    | PropSome e ->
        Format.fprintf ff "SOME(";
        fprint_expr_mangled ff e;
        Format.pp_print_string ff ")"
    | PropGlob e ->
        Format.fprintf ff "(";
        fprint_expr_mangled ff e;
        Format.pp_print_string ff ")"
    | PropAnd (l, r) ->
        Format.pp_print_string ff "(";
        write_atomic_expr ff l;
        Format.fprintf ff ") @ && (";
        write_atomic_expr ff l;
        Format.pp_print_string ff ")"
    | PropOr (l, r) ->
        Format.pp_print_string ff "(";
        write_atomic_expr ff l;
        Format.fprintf ff ") @ || (";
        write_atomic_expr ff l;
        Format.pp_print_string ff ")"


let rec write_stmt type_tab annot ff lvl indent_first s =
    let write = function
    | MSkip _ ->
        openb ff lvl indent_first;
        Format.fprintf ff "skip;";
        closeb ff

    | MExpr (_, Nop comment) -> (* special treatment *)
        if comment <> ""
        then begin
            openb ff lvl indent_first;
            Format.fprintf ff "skip; /* %s */" comment;
            closeb ff
        end

    | MExpr (_, e) ->
        openb ff lvl indent_first;
        fprint_expr_mangled ff e;
        Format.pp_print_string ff ";";
        closeb ff

    | MDecl (_, v, e) ->
        openb ff lvl indent_first;
        let print_flags =
            let pf f =
                let s = hflag_promela f in
                if s <> "" then Format.fprintf ff "%s@ " s
            in
            List.iter pf v#get_flags
        in
        print_flags;
        let var_tp =
            try type_tab#get_type v
            with Not_found ->
                raise (Failure ("No type for the variable " ^ v#get_name))
        in
        Format.fprintf ff "%s@ " (var_type_promela var_tp);
        fprint_expr_mangled ff (Var v);
        if var_tp#is_array then Format.fprintf ff "[%d]" var_tp#nelems;
        let bit_width = find_bit_width var_tp in
        if bit_width <> 0
        then Format.fprintf ff ":%d" bit_width;

        if not_nop e then begin
            Format.fprintf ff "@ =@ ";
            fprint_expr_mangled ff e
        end;
        Format.pp_print_string ff ";"; 
        if var_tp#has_range then begin
            let l, r = var_tp#range in
            Format.fprintf ff " /* range: [%d, %d) */" l r
        end;
        closeb ff

    | MDeclProp (_, v, ae) ->
        let out, flush, newline, spaces =
            Format.pp_get_all_formatter_output_functions ff () in
        Format.pp_set_all_formatter_output_functions
            ff out flush (macro_newl out) spaces;
        openb ff lvl indent_first;
        Format.fprintf ff "#define %s (" v#get_name;
        write_atomic_expr ff ae;
        Format.pp_print_string ff ")";
        Format.pp_set_all_formatter_output_functions
            ff out flush newline spaces;
        closeb ff

    | MLabel (_, l) ->
        Format.fprintf ff "%s:@\n" l

    | MAtomic (_, seq) ->
        openb ff lvl indent_first;
        Format.pp_print_string ff "atomic {";
        closeb ff;
        List.iter (write_stmt type_tab annot ff (lvl + 2) true) seq;
        openb ff lvl true; Format.pp_print_string ff "}"; closeb ff

    | MD_step (_, seq) ->
        openb ff lvl indent_first;
        Format.pp_print_string ff "d_step {";
        closeb ff;
        List.iter (write_stmt type_tab annot ff (lvl + 2) true) seq;
        openb ff lvl true; Format.pp_print_string ff "}"; closeb ff

    | MGoto (_, l) ->
        openb ff lvl indent_first;
        Format.fprintf ff "goto %s;" l;
        closeb ff

    | MIf (_, opts) ->
        openb ff lvl indent_first; Format.pp_print_string ff "if"; closeb ff;
        List.iter
            (function
                | MOptGuarded seq ->
                    openb ff (lvl + 2) true; Format.fprintf ff "::@ @ @]";
                    write_stmt type_tab annot ff (lvl + 4) false (List.hd seq);
                    List.iter
                        (write_stmt type_tab annot ff (lvl + 6) true)
                        (List.tl seq);

                | MOptElse seq ->
                    let semi = if (List.length seq) = 0 then "" else "->" in
                    openb ff (lvl + 4) true;
                    Format.fprintf ff ":: else@ %s" semi;
                    closeb ff;
                    begin
                        match seq with
                        | [] -> ()
                        | hd :: tl ->
                            write_stmt type_tab annot ff (lvl + 6) false hd;
                            List.iter (write_stmt type_tab annot ff (lvl + 4) true) tl;
                    end
            ) opts;
        openb ff lvl true; Format.pp_print_string ff "fi;"; closeb ff;

    | MAssert (_, e) ->
        openb ff lvl indent_first;
        Format.pp_print_string ff "assert(";
        fprint_expr_mangled ff e;
        Format.pp_print_string ff ");";
        closeb ff

    | MAssume (_, e) ->
        openb ff lvl indent_first;
        Format.pp_print_string ff "/* assume(";
        fprint_expr_mangled ff e;
        Format.pp_print_string ff "); */";
        closeb ff

    | MHavoc (_, v) ->
        openb ff lvl indent_first;
        Format.fprintf ff "/* havoc(%s); */" v#get_name;
        closeb ff

    | MUnsafe (_, s) ->
        openb ff lvl indent_first;
        Format.fprintf ff "%s" s;
        closeb ff

    | MPrint (_, s, es) ->
        openb ff lvl indent_first;
        Format.fprintf ff "printf(\"%s\"" s;
        List.iter (fun e -> Format.fprintf ff ",@ "; fprint_expr_mangled ff e) es;
        Format.pp_print_string ff ");";
        closeb ff
    in
    let write_comment text =
        (* write down the annotation as a comment *)
        openb ff lvl indent_first;
        Format.fprintf ff "/* %s */" text;
        closeb ff
    in
    let annotate is_before =
        if Hashtbl.mem annot (m_stmt_id s)
        then match (Hashtbl.find annot (m_stmt_id s)) with
            | AnnotBefore text ->
                if is_before then write_comment text

            | AnnotAfter text ->
                if not is_before then write_comment text
    in
    annotate true;
    write s;
    annotate false

  
let write_proc type_tab annot ff lvl p =
    openb ff lvl true;
    if not_nop p#get_active_expr
    then begin Format.fprintf ff "active[%s]@ " (expr_s p#get_active_expr) end;
    Format.fprintf ff "proctype@ %s(" p#get_name;
    let p_arg delim v =
        if delim <> "" then begin Format.fprintf ff "%s@ " delim end;
        Format.fprintf ff "%s@ %s"
            (var_type_promela (type_tab#get_type v)) v#get_name
    in
    begin 
        match p#get_args with
        | [] -> ()
        | hd :: tl -> p_arg "" hd; List.iter (p_arg ",") tl
    end;

    Format.fprintf ff ")@ ";
    if not_nop p#get_provided then begin
        Format.fprintf ff "provided@ (%s" (expr_s p#get_provided);
        Format.fprintf ff ")@ "
    end;
    Format.pp_print_string ff "{";
    closeb ff;
    (* end of proctype signature, the body begins *)

    List.iter (write_stmt type_tab annot ff (lvl + 2) true) p#get_stmts;
    (* end the body *)

    openb ff lvl true; Format.pp_print_string ff "}"; closeb ff


let write_unit type_tab annot cout lvl u =
    let ff = Format.formatter_of_out_channel cout in
    match u with
    | Stmt s ->
        write_stmt type_tab annot ff lvl true s
    | Proc p ->
        write_proc type_tab annot ff lvl p
    | Ltl (name, exp) ->
        openb ff lvl true;
        Format.fprintf ff "ltl@ %s@ {@ " name;
        fprint_expr_mangled ff exp;
        Format.pp_print_string ff "}";
        closeb ff
    | _ -> ();
    Format.pp_print_flush ff ()


let write_to_file externalize_ltl name units type_tab annot =
    let fo = open_out name in
    let save_unit = function
        | Ltl (form_name, form) as u->
            (* Spin 6.2 supports inline formulas no longer than 1024 chars.
               It produces arbitrary compilation errors for those longer than
               its authors expected. We thus save the formula into a file. *)
            if externalize_ltl
            then begin
                let out = open_out (sprintf "%s.ltl" form_name) in
                fprintf out "%s\n" (expr_s form);
                close_out out
            end else
                write_unit type_tab annot fo 0 u
        | _ as u -> write_unit type_tab annot fo 0 u
    in
    List.iter save_unit units;
    close_out fo

