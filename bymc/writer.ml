(* Write Promela code from its intermediate representation *)

open Printf;;

open Debug;;
open SpinIr;;
open SpinIrImp;;
open SpinTypes;;

let indent level = String.make level ' ';;
let rec tabify ff level =
  if level > 0
  then begin
    Format.pp_print_space ff ();
    tabify ff (level - 1)
  end;;

let openb ff lvl need_tab =
    let box_lvl = if need_tab then (lvl + 2) else 2 in
    Format.pp_open_hovbox ff box_lvl;
    if need_tab then tabify ff lvl
;;
let closeb ff =
    Format.pp_close_box ff ();
    Format.pp_print_newline ff ()
;;
(* macros have another rule for a line break *)
let macro_newl out () = out "\\\n" 0 2;;

let var_type_promela tp =
    match tp with
      TBIT -> "bit"
      | TBYTE -> "byte"
      | TSHORT -> "short"
      | TINT -> "int"
      | TUNSIGNED -> "unsigned"
      | TCHAN -> "chan"
      | TMTYPE -> "mtype"
      | TPROPOSITION -> "proposition"
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


let rec write_atomic_expr ff = function
    | PropAll e ->
        Format.fprintf ff "ALL(";
        fprint_expr ff e;
        Format.pp_print_string ff ")"
    | PropSome e ->
        Format.fprintf ff "SOME(";
        fprint_expr ff e;
        Format.pp_print_string ff ")"
    | PropGlob e ->
        Format.fprintf ff "(";
        fprint_expr ff e;
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


let rec write_stmt ff lvl indent_first lab_tab s =
    match s with
    | MSkip _ ->
        openb ff lvl indent_first;
        Format.fprintf ff "skip;";
        closeb ff
    | MExpr (_, e) ->
        openb ff lvl indent_first;
        fprint_expr ff e;
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
        Format.fprintf ff "%s@ %s"(var_type_promela v#get_type) v#get_name;
        if v#is_array then Format.fprintf ff "[%d]" v#get_num_elems;
        if not_nop e then begin
            Format.fprintf ff "@ =@ ";
            fprint_expr ff e
        end;
        Format.pp_print_string ff ";"; 
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
        if Hashtbl.mem lab_tab l
        then Format.fprintf ff "%s:@\n" (Hashtbl.find lab_tab l)
        else Format.fprintf ff "lab%d:@\n" l
    | MAtomic (_, seq) ->
        openb ff lvl indent_first;
        Format.pp_print_string ff "atomic {";
        closeb ff;
        List.iter (write_stmt ff (lvl + 2) true lab_tab) seq;
        openb ff lvl true; Format.pp_print_string ff "}"; closeb ff
    | MD_step (_, seq) ->
        openb ff lvl indent_first;
        Format.pp_print_string ff "d_step {";
        closeb ff;
        List.iter (write_stmt ff (lvl + 2) true lab_tab) seq;
        openb ff lvl true; Format.pp_print_string ff "}"; closeb ff
    | MGoto (_, l) ->
        openb ff lvl indent_first;
        if Hashtbl.mem lab_tab l
        then Format.fprintf ff "goto %s;" (Hashtbl.find lab_tab l)
        else Format.fprintf ff "goto lab%d;" l;
        closeb ff
    | MIf (_, opts) ->
        openb ff lvl indent_first; Format.pp_print_string ff "if"; closeb ff;
        List.iter
            (function
                | MOptGuarded seq ->
                    openb ff (lvl + 2) true; Format.fprintf ff "::@ @ @]";
                    write_stmt ff (lvl + 4) false lab_tab (List.hd seq);
                    List.iter
                        (write_stmt ff (lvl + 6) true lab_tab)
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
                            write_stmt ff (lvl + 6) false lab_tab hd;
                            List.iter (write_stmt ff (lvl + 4) true lab_tab) tl;
                    end
            ) opts;
        openb ff lvl true; Format.pp_print_string ff "fi;"; closeb ff;
    | MAssert (_, e) ->
        openb ff lvl indent_first;
        Format.pp_print_string ff "assert(";
        fprint_expr ff e;
        Format.pp_print_string ff ");";
        closeb ff
    | MAssume (_, e) ->
        openb ff lvl indent_first;
        Format.pp_print_string ff "assume(";
        fprint_expr ff e;
        Format.pp_print_string ff ");";
        closeb ff
    | MHavoc (_, v) ->
        openb ff lvl indent_first;
        Format.fprintf ff "havoc(%s);" v#get_name;
        closeb ff
    | MUnsafe (_, s) ->
        openb ff lvl indent_first;
        Format.fprintf ff "%s" s;
        closeb ff
    | MPrint (_, s, es) ->
        openb ff lvl indent_first;
        Format.fprintf ff "printf(\"%s\"" s;
        List.iter (fun e -> Format.fprintf ff ",@ "; fprint_expr ff e) es;
        Format.pp_print_string ff ");";
        closeb ff
;;
  
let write_proc ff lvl p =
    openb ff lvl true;
    if not_nop p#get_active_expr
    then begin Format.fprintf ff "active[%s]@ " (expr_s p#get_active_expr) end;
    Format.fprintf ff "proctype@ %s(" p#get_name;
    let p_arg delim v =
        if delim <> "" then begin Format.fprintf ff "%s@ " delim end;
        Format.fprintf ff "%s@ %s" (var_type_promela v#get_type) v#get_name
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

    let labels = Hashtbl.create 10 in
    Hashtbl.iter
        (fun n l -> Hashtbl.add labels l#get_num n)
        p#labels_as_hash;

    List.iter (write_stmt ff (lvl + 2) true labels) p#get_stmts;
    (* end the body *)

    openb ff lvl true; Format.pp_print_string ff "}"; closeb ff
;;

let write_unit cout lvl u =
    let ff = Format.formatter_of_out_channel cout in
    match u with
    | Stmt s ->
        write_stmt ff lvl true (Hashtbl.create 0) s
    | Proc p ->
        write_proc ff lvl p
    | Ltl (name, exp) ->
        openb ff lvl true;
        Format.fprintf ff "ltl@ %s@ {@ " name;
        fprint_expr ff exp;
        Format.pp_print_string ff "}";
        closeb ff
    | _ -> ();
    Format.pp_print_flush ff ()
;;
