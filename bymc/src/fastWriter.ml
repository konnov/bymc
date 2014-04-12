(* Converting a symbolic skeleton into the format of FASTer 2.1.
 *
 * FAST: http://tapas.labri.fr/trac/wiki/FASTer
 *
 * Igor Konnov, 2014
 *)

open Accums
open Spin
open SpinIr
open SymbSkel

module F = Format

let ppn ff () = F.pp_print_newline ff ()

let print_expr ?in_act:(ina=false) ff e =
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
        F.fprintf ff "%s" (SpinIrImp.expr_s e)
    in
    p e


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
    F.fprintf ff "%s > 0@ && " src_name;
    print_expr ff r.Sk.guard; F.fprintf ff "@];@,";
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

type spec_t = 
    (* (p && <> !q) *)
    | CondSafety of token expr (* p *) * token expr (* q *)
    | Unsupported of token expr


let classify_spec prog = function
    (* (p -> [] q) *)
    | BinEx (IMPLIES, lhs, UnEx (ALWAYS, rhs)) as e ->
        if (Ltl.is_propositional (Program.get_type_tab prog) lhs)
            && (Ltl.is_propositional (Program.get_type_tab prog) rhs)
        then CondSafety (lhs, Ltl.normalize_form (UnEx (NEG, rhs)))
        else Unsupported e

    | BinEx (OR, lhs, UnEx (ALWAYS, rhs)) as e ->
        if (Ltl.is_propositional (Program.get_type_tab prog) lhs)
            && (Ltl.is_propositional (Program.get_type_tab prog) rhs)
        then CondSafety (Ltl.normalize_form (UnEx (NEG, lhs)),
                         Ltl.normalize_form (UnEx (NEG, rhs)))
        else Unsupported e

    | e -> Unsupported e


let write_quant ff prog skels ~is_exist e =
    let pname = Ltl.find_proc_name ~err_not_found:true e in
    let sk =
        try List.find (fun sk -> sk.Sk.name = pname) skels
        with Not_found -> raise (Failure ("No skeleton " ^ pname))
    in
    let var_names = List.map (fun v -> v#get_name) sk.Sk.locals in
    let is_matching_loc loc =
        let lookup = List.combine var_names loc in
        let val_fun = function
            | Var v ->
            begin
                try List.assoc v#get_name lookup
                with Not_found ->
                    raise (Failure (Printf.sprintf "Var %s not found" v#get_name))
            end

            | e ->
                raise (Failure ("val_fun(%s) is undefined" ^ (SpinIrImp.expr_s e)))
        in
        (SpinIrEval.Bool is_exist) = SpinIrEval.eval_expr val_fun e
    in
    let matching = List.filter is_matching_loc sk.Sk.locs in
    (* exists *)
    let each_loc not_first l =
        (* exists: there is a non-zero location *)
        if not_first && is_exist then F.fprintf ff "@ || ";
        (* forall: all other locations are zero *)
        if not_first && not is_exist then F.fprintf ff "@ && ";
        if is_exist
        then F.fprintf ff "(%s > 0)" (Sk.locname l)
        else F.fprintf ff "(%s = 0)" (Sk.locname l);
        true
    in
    F.fprintf ff "@[<hov 2>(";
    ignore (List.fold_left each_loc false matching);
    F.fprintf ff "@])"
    

let write_prop ff prog skels prop_form =
    let atomics = Program.get_atomics_map prog in
    let tt = Program.get_type_tab prog in
    let rec pr_atomic neg = function
        | PropGlob e ->
            print_expr ff ~in_act:true e

        | PropAll e ->
            write_quant ff prog skels ~is_exist:false e

        | PropSome e ->
            write_quant ff prog skels ~is_exist:true e

        | PropAnd (l, r) ->
            F.fprintf ff "("; pr_atomic neg l;
            F.fprintf ff ")@ && ("; pr_atomic neg r; F.fprintf ff ")"

        | PropOr (l, r) ->
            F.fprintf ff "("; pr_atomic neg l;
            F.fprintf ff ")@ || ("; pr_atomic neg r; F.fprintf ff ")"
    in
    let rec pr neg = function
    | BinEx (AND as t, l, r)
    | BinEx (OR as t, l, r) ->
        let op, nop = if t = AND then "&&", "||" else "||", "&&" in
        F.fprintf ff "("; pr neg l;
        F.fprintf ff ")@ %s (" (if neg then nop else op);
        pr neg r; F.fprintf ff ")"

    | UnEx (NEG, r) ->
        pr (not neg) r

    | Var v ->
        let op = if neg then "!" else "" in
        if (tt#get_type v)#basetype = SpinTypes.TPROPOSITION
        then pr_atomic neg (StrMap.find v#get_name atomics)
        else F.fprintf ff "%s%s" op v#get_name

    | e ->
        let ne = if neg then UnEx (NEG, e) else e in
        print_expr ff ~in_act:true (Ltl.normalize_form ne)
    in
    pr false prop_form


let write_init_region ff prog skels init_form =
    F.fprintf ff "@[<hov 2>state = normal";
    let p_expr e =
        F.fprintf ff "@ && @[<h>";
        print_expr ff ~in_act:true e;
        F.fprintf ff "@]"
    in
    List.iter p_expr (Program.get_assumes prog);
    let each_skel sk = List.iter p_expr sk.Sk.inits in
    List.iter each_skel skels


let write_bad_region ff prog skels bad_form =
    F.fprintf ff "@[<hov 2>state = normal";
    F.fprintf ff "@ && ";
    write_prop ff prog skels bad_form


let write_cond_safety ff prog skels name init_form bad_form =
    F.fprintf ff "@[<v 2>strategy %s {@," (String.lowercase name);
    F.fprintf ff "@[<v 2>Region init := {@,";
    write_init_region ff prog skels init_form;
    F.fprintf ff "@]@,};@,";
    F.fprintf ff "@[<v 2>Region bad := {@,";
    write_bad_region ff prog skels bad_form;
    F.fprintf ff "@]@,};@,";
    F.fprintf ff "Transitions t := {@[<hov>";
    let rec each_rule i sk =
        if i > 0 then F.fprintf ff ",@ ";
        F.fprintf ff "r%d" i;
        if i < (sk.Sk.nrules - 1)
        then each_rule (i + 1) sk
    in
    List.iter (each_rule 0) skels;
    F.fprintf ff "@]};@,";
    F.fprintf ff "Region reach := post*(init, t);@,";
    F.fprintf ff "Region result := reach && bad;@,";
    F.fprintf ff "print(result);@,";
    F.fprintf ff "if (isEmpty(result))@,";
    F.fprintf ff "  then print(\"safe\");@,";
    F.fprintf ff "  else print(\"unsafe\");@,";
    F.fprintf ff "endif@,";
    F.fprintf ff "@]@,}@,"


let write_all_specs ff prog skels =
    let each_spec name s =
        match classify_spec prog s with
        | Unsupported e ->
            F.fprintf ff "@[<hov 2>/* %s is not supported:@," name;
            print_expr ff ~in_act:false e;
            F.fprintf ff " */@]@,@,";
        | CondSafety (init, bad) ->
            write_cond_safety ff prog skels name init bad
    in
    F.fprintf ff "@[<v 0>";
    StrMap.iter each_spec (Program.get_ltl_forms prog);
    F.fprintf ff "@]"


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

