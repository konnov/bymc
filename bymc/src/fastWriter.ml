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
            F.fprintf ff "("; p l; F.fprintf ff "@ <= ";
            p r; F.fprintf ff ")";
            F.fprintf ff "@ || ("; p l; F.fprintf ff "@ >= "; p r;
            F.fprintf ff ")";
        end

    | BinEx (NE, l, r) ->
        F.fprintf ff "("; p l; F.fprintf ff "@ < ";
        p r; F.fprintf ff ")";
        F.fprintf ff "@ || ("; p l; F.fprintf ff "@ > ";
        p r; F.fprintf ff ")"

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
    F.fprintf ff "var ";
    List.iter2 each_var (range 0 (List.length vars)) vars;
    F.fprintf ff ";@\n"


let write_rule ff prog num r =
    F.fprintf ff "transition@ r%d := {@\n" num;
    F.fprintf ff "  from := normal;@\n";
    F.fprintf ff "  to := normal;@\n";
    F.fprintf ff "  guard := @[<hov 2>";
    print_expr ff r.Sk.guard; F.fprintf ff "];@\n";
    F.fprintf ff "  action := @[<hv 2>";
    let each_act n e =
        if n = 0
        then print_expr ff ~in_act:true e
        else begin
            F.fprintf ff ",@ ";
            print_expr ff ~in_act:true e
        end
    in
    List.iter2 each_act (range 0 (List.length r.Sk.act)) r.Sk.act;
    F.fprintf ff ";@\n";
    F.fprintf ff "};@\n@\n"


let write_skel ff prog sk =
    List.iter2 (write_rule ff prog) (range 0 sk.Sk.nrules) sk.Sk.rules

let model_name filename=
    let base = Filename.chop_extension (Filename.basename filename) in
    Str.global_replace (Str.regexp "[^A-Za-z0-9_]") "" base


let write_to_file filename rt prog skels =
    let fo = open_out filename in
    let ff = F.formatter_of_out_channel fo in
    F.pp_set_margin ff 80;
    let mname = model_name rt#caches#options.Options.filename in
    F.fprintf ff "model@ %s@ {@ " (String.uppercase mname);

    write_vars ff skels;
    F.fprintf ff "states normal;@\n@\n";
    List.iter (write_skel ff prog) skels;

    F.fprintf ff "}@\n";
    F.pp_print_flush ff ();
    close_out fo

