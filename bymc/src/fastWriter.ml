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

let ppn ff () = Format.pp_print_newline ff ()

(* TODO: use Format.printf *)
let rec expr_s = function
    | BinEx (EQ, l, r) ->
        Printf.sprintf "%s = %s" (expr_s l) (expr_s r)
    | UnEx (NEXT, e) ->
        Printf.sprintf "%s'" (expr_s e)
    | _ as e -> SpinIrImp.expr_s e


let write_vars ff skels =
    (* XXX: the locations of several processes might clash *)
    let collect_vars var_set sk =
        let add vs v = StrSet.add v#get_name vs in
        let var_set = List.fold_left add var_set sk.Sk.shared in
        let add_loc vs l = StrSet.add (Sk.locname l) vs in
        List.fold_left add_loc var_set sk.Sk.locs
    in
    let vars =
        StrSet.elements (List.fold_left collect_vars StrSet.empty skels) in
    let each_var i name =
        if i = 0
        then Format.fprintf ff "%s" name
        else Format.fprintf ff ",@ %s" name
    in
    Format.fprintf ff "var ";
    List.iter2 each_var (range 0 (List.length vars)) vars;
    Format.fprintf ff ";";
    Format.pp_print_newline ff ()


let write_rule ff prog num r =
    Format.fprintf ff "transition@ r%d := {" num; ppn ff ();
    Format.fprintf ff "  from := normal;"; ppn ff ();
    Format.fprintf ff "  to := normal;"; ppn ff ();
    Format.fprintf ff "  guard := %s;" (expr_s r.Sk.guard); ppn ff ();
    Format.fprintf ff "  action := ";
    let each_act n e =
        if n = 0
        then Format.fprintf ff "%s" (expr_s e)
        else Format.fprintf ff ",@ %s" (expr_s e)
    in
    List.iter2 each_act (range 0 (List.length r.Sk.act)) r.Sk.act;
    Format.fprintf ff ";";
    Format.fprintf ff "};"; ppn ff (); ppn ff ()


let write_skel ff prog sk =
    List.iter2 (write_rule ff prog) (range 0 sk.Sk.nrules) sk.Sk.rules


let write_to_file filename rt prog skels =
    let fo = open_out filename in
    let ff = Format.formatter_of_out_channel fo in
    let name =
        Filename.chop_extension
            (Filename.basename rt#caches#options.Options.filename) in
    Format.fprintf ff "model@ %s@ {@ " (String.uppercase name);

    Format.pp_open_hvbox ff 2;

    write_vars ff skels;
    Format.fprintf ff "states normal;"; ppn ff (); ppn ff ();
    List.iter (write_skel ff prog) skels;

    Format.pp_close_box ff ();
    Format.fprintf ff "}";
    ppn ff ();
    Format.pp_print_flush ff ();
    close_out fo

