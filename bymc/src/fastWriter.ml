(** Converting a symbolic skeleton into the format of FASTer 2.1.
 *
 * FAST: http://tapas.labri.fr/trac/wiki/FASTer
 *
 * TODO: multiple process types
 *
 * @author Igor Konnov, 2014
 *)

open Accums
open Spin
open SpinIr
open SymbSkel

module F = Format

let ppn ff () = F.pp_print_newline ff ()



let print_def_expr ff e =
    F.fprintf ff "%s" (SpinIrImp.expr_s e)


let print_expr ?printex:(pex=print_def_expr) ?in_act:(ina=false) ff e =
    let rec p = function
    | BinEx (AND, l, r) ->
        F.fprintf ff "("; p l;
        F.fprintf ff ")@ && ("; p r; F.fprintf ff ")"

    | BinEx (OR, l, r) ->
        F.fprintf ff "("; p l; F.fprintf ff ")@ || "; 
        F.fprintf ff "("; p r; F.fprintf ff ")"

    | UnEx (NEG, r) ->
        F.fprintf ff "!("; p r; F.fprintf ff ")"

    | BinEx (EQ, l, r) ->
        if ina
        then begin
            p l; F.fprintf ff "@ = "; p r
        end
        else begin
            F.fprintf ff "(("; p l; F.fprintf ff "@ <= ";
            p r; F.fprintf ff ")";
            F.fprintf ff "@ && ("; p l; F.fprintf ff "@ >= "; p r;
            F.fprintf ff "))";
        end

    | BinEx (NE, l, r) ->
        F.fprintf ff "(("; p l; F.fprintf ff "@ < ";
        p r; F.fprintf ff ")";
        F.fprintf ff "@ || ("; p l; F.fprintf ff "@ > ";
        p r; F.fprintf ff "))"

    | UnEx (NEXT, Var v) ->
        F.fprintf ff "%s'" v#get_name

    | UnEx (NEXT, _) ->
        raise (Failure (Printf.sprintf "next(%s) is not supported"
            (SpinIrImp.expr_s e)))

    | _ as e ->
        pex ff e
    in
    p e


(* Sometimes we have division over a constant. Eliminate it by multiplying by
   the divisor.
 *)
let eliminate_div e =
    let rec divisor = function
        | BinEx (DIV, l, Const k) ->
             k * (divisor l)
        | BinEx (DIV, _, r) ->
             raise (Failure "Division over non-constant")
        | BinEx (MULT, l, r)
        | BinEx (MINUS, l, r)
        | BinEx (PLUS, l, r) ->
             (divisor l) * (divisor r)
        | _ -> 1
    in
    let rec mult div = function
        | BinEx (DIV, l, Const k) ->
             assert (div mod k = 0);
             if k = div
             then l
             else mult (div / k) l
        
        | BinEx (MULT, l, r) ->
             let ld, rd = divisor l, divisor r in
             BinEx (MULT, mult (ld * div / rd) l, mult rd r)

        | BinEx (MINUS as t, l, r)
        | BinEx (PLUS as t, l, r) ->
             BinEx (t, mult div l, mult div r)

        | UnEx (t, r) ->
             UnEx (t, mult div r)
             
        | Const k -> Const (k * div)
        | Var v -> BinEx (MULT, Const div, Var v)
        | e -> raise (Failure ("Unsupported: " ^ (SpinIrImp.expr_s e)))
    in
    let rec in_logical = function
        | BinEx (AND as t, l, r)
        | BinEx (OR as t, l, r) ->
            BinEx (t, in_logical l, in_logical r)
        | UnEx (NEG, r) ->
            UnEx (NEG, in_logical r)

        | BinEx (LT as t, l, r)
        | BinEx (GT as t, l, r)
        | BinEx (LE as t, l, r)
        | BinEx (GE as t, l, r)
        | BinEx (EQ as t, l, r)
        | BinEx (NE as t, l, r) ->
            let div = max (divisor l) (divisor r) in
            if div > 1
            then BinEx (t, mult div l, mult div r)
            else BinEx (t, l, r)

        | _ as e -> e
    in
    in_logical e


let write_vars ff skels =
    (* XXX: the locations of several processes might clash *)
    let collect_vars var_set sk =
        let add vs v = StrSet.add v#get_name vs in
        let var_set = List.fold_left add var_set sk.Sk.shared in
        let var_set = List.fold_left add var_set sk.Sk.params in
        let add_loc vs l = StrSet.add (Sk.locname l) vs in
        List.fold_left add_loc var_set sk.Sk.locs
    in
    let vars =
        StrSet.elements (List.fold_left collect_vars StrSet.empty skels) in
    let each_var i name =
        if i = 0
        then F.fprintf ff "%s" name
        else F.fprintf ff ",@ %s" name
    in
    F.fprintf ff "@[<hov 2>var ";
    List.iter2 each_var (range 0 (List.length vars)) vars;
    F.fprintf ff ";@]@,"


let write_rule ff prog sk num r =
    F.fprintf ff "@[<v 2>transition r%d := {@," num;
    F.fprintf ff "  from := normal;@,";
    F.fprintf ff "  to := normal;@,";
    F.fprintf ff "  guard := @[<hov 2>";
    let src_name = Sk.locname (List.nth sk.Sk.locs r.Sk.src) in
    let dst_name = Sk.locname (List.nth sk.Sk.locs r.Sk.dst) in
    F.fprintf ff "%s > 0@ " src_name;
    if r.Sk.guard <> Const 1
    then begin
        F.fprintf ff "&& ";
        print_expr ff (eliminate_div r.Sk.guard);
    end;
    F.fprintf ff "@];@,";
    F.fprintf ff "  action := @[<hov 2>";
    F.fprintf ff "%s' = %s - 1,@, %s' = %s + 1,"
        src_name src_name dst_name dst_name;
    let each_act n e =
        if n = 0
        then print_expr ff ~in_act:true e
        else begin
            F.fprintf ff ",@,";
            print_expr ff ~in_act:true e
        end
    in
    List.iter2 each_act (range 0 (List.length r.Sk.act)) r.Sk.act;
    F.fprintf ff "@];";
    F.fprintf ff "@]@,};@,"

let write_skel ff prog sk =
    List.iter2 (write_rule ff prog sk) (range 0 sk.Sk.nrules) sk.Sk.rules


let write_init_region ff prog skels init_form =
    F.fprintf ff "@[<hov 2>state = normal";
    let p_expr e =
        F.fprintf ff "@ && @[<h>";
        print_expr ff ~in_act:true (eliminate_div e);
        F.fprintf ff "@]"
    in
    List.iter p_expr (Program.get_assumes prog);
    let each_skel sk = List.iter p_expr sk.Sk.inits in
    List.iter each_skel skels;
    F.fprintf ff "@ && @[<h>";
    print_expr ff ~in_act:true init_form;
    F.fprintf ff "@]"


let write_bad_region ff prog skels bad_form =
    F.fprintf ff "@[<hov 2>state = normal";
    F.fprintf ff "@ && ";
    print_expr ff ~in_act:true bad_form


let write_cond_safety ff prog skels name init_form bad_form =
    let suffix = String.lowercase name in
    F.fprintf ff "@[<v 2>Region init_%s := {@," suffix;
    write_init_region ff prog skels init_form;
    F.fprintf ff "@]@,};@,";
    F.fprintf ff "@[<v 2>Region bad_%s := {@," suffix;
    write_bad_region ff prog skels bad_form;
    F.fprintf ff "@]@,};@,";
    F.fprintf ff "Region reach_%s := post*(init_%s, t);@," suffix suffix;
    F.fprintf ff "Region result_%s := reach_%s && bad_%s;@,"
        suffix suffix suffix;
    F.fprintf ff "print(result_%s);@," suffix;
    F.fprintf ff "if (isEmpty(result_%s))@," suffix;
    F.fprintf ff "  then print(\"specification %s is satisfied\");@,"
        (String.lowercase name);
    F.fprintf ff "  else print(\"specification %s is violated\");@,"
        (String.lowercase name);
    F.fprintf ff "endif@,"


let write_all_specs ff prog skels =
    let each_spec name s =
        match Ltl.classify_spec (Program.get_type_tab prog) s with
        | Ltl.CondGeneral e ->
            F.fprintf ff "@[<hov 2>/* %s is not supported:@," name;
            print_expr ff ~in_act:false e;
            F.fprintf ff " */@]@,@,";
        | Ltl.CondSafety (init, bad) ->
            let init = SymbSkel.expand_props_in_ltl prog skels init in
            let bad = SymbSkel.expand_props_in_ltl prog skels bad in
            write_cond_safety ff prog skels name init bad
    in
    F.fprintf ff "@[<v 2>strategy s1 {@,";
    F.fprintf ff "@[<v 0>";
    F.fprintf ff "Transitions t := {@[<hov>";
    let rec each_rule i sk =
        if i > 0 then F.fprintf ff ",@ ";
        F.fprintf ff "r%d" i;
        if i < (sk.Sk.nrules - 1)
        then each_rule (i + 1) sk
    in
    List.iter (each_rule 0) skels;
    F.fprintf ff "@]};@,";
    StrMap.iter each_spec (Program.get_ltl_forms prog);
    F.fprintf ff "@]";
    F.fprintf ff "@]@,}@,"


let model_name filename=
    let base = Filename.chop_extension (Filename.basename filename) in
    Str.global_replace (Str.regexp "[^A-Za-z0-9_]") "" base


let write_to_file filename rt prog skels =
    let fo = open_out filename in
    let ff = F.formatter_of_out_channel fo in
    F.pp_set_margin ff 80;
    let mname = model_name rt#caches#options.Options.filename in
    F.fprintf ff "@[<v 2>model %s {@," (String.uppercase mname);

    write_vars ff skels;
    F.fprintf ff "states normal;@\n@\n";
    List.iter (write_skel ff prog) skels;

    F.fprintf ff "@]@,}@,@,";
    write_all_specs ff prog skels;
    F.pp_print_flush ff ();
    close_out fo

