(*
 * Optimize the process description by computing a summary and encoding
 * it back into the loop body.
 *
 * This optimization works only with a finite-state process description.
 *
 * The optimization is disabled by default. To enable it, pass -O opt.enable=1
 *
 * Igor Konnov, 2014
 *)

open Batteries

open Printf

open Accums
open Debug
open SymbSkel
open Plugin
open PorBounds
open Spin
open SpinIr


let feed_comp_from_skel rt prog proc sk =
    let reg_tab = (rt#caches#find_struc prog)#get_regions proc#get_name in
    let loop_sig = SkelStruc.extract_loop_sig prog reg_tab proc in
    let prev_next = SkelStruc.get_prev_next loop_sig in
    let add_to_map map (prev, next) = StrMap.add prev#get_name next map in
    let pn_map = List.fold_left add_to_map StrMap.empty prev_next in
    let loc_to_expr ~is_next loc =
        let each_local var value =
            let v = if is_next
                then StrMap.find var#get_name pn_map
                else var
            in
            BinEx ((if is_next then ASGN else EQ), Var v, IntConst value)
        in
        List.map2 each_local sk.Sk.locals loc
    in
    let mir_of e = MExpr (fresh_id (), e) in
    let rule_to_opt r =
        let src = List.nth sk.Sk.locs r.Sk.src in
        let dst = List.nth sk.Sk.locs r.Sk.dst in
        let src_exp = list_to_binex AND (loc_to_expr ~is_next:false src) in
        let dst_asgns = List.map mir_of (loc_to_expr ~is_next:true dst) in
        let guard = mir_of (BinEx (AND, src_exp, r.Sk.guard)) in
        let map_act = function
            | BinEx (EQ, UnEx (NEXT, l), r) -> BinEx (ASGN, l, r)
            | _ as e -> raise (Failure ("Unexpected " ^ SpinIrImp.expr_s e))
        in
        let actions = List.map (mir_of % map_act) r.Sk.act in
        MOptGuarded (guard :: dst_asgns @ actions)
    in
    let big_if = MIf (fresh_id (), List.map rule_to_opt sk.Sk.rules) in
    let body = proc#get_stmts in
    let decl = reg_tab#get "decl" body in
    let init = reg_tab#get "init" body in
    let loop_prefix = reg_tab#get "loop_prefix" body in
    let update = reg_tab#get "update" body in
    let loop_body = MAtomic (fresh_id (), big_if :: update) in
    let new_body = decl @ init @ loop_prefix @ [loop_body] in
    proc_replace_body proc new_body


class opt_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        method transform rt =
            let prog = self#get_input0 in
            let opt_prog =
                let en = Options.get_plugin_opt rt#caches#options "opt.enable"
                in
                if Some "1" = en
                then begin
                    rt#caches#set_struc prog (SkelStruc.compute_struc prog);
                    let each_proc proc =
                        let sk = self#extract_proc rt prog proc in
                        feed_comp_from_skel rt prog proc sk
                    in
                    let new_procs = List.map each_proc (Program.get_procs prog) in
                    let oprog = Program.set_procs new_procs prog in
                    Writer.write_to_file false "opt.prm"
                        (Program.units_of_program oprog)
                        (Program.get_type_tab oprog)
                        (Hashtbl.create 10);
                    oprog
                end else prog
            in
            opt_prog


        method extract_proc rt prog proc =
            logtm INFO ("  > Computing the summary of " ^ proc#get_name);
            let sk = Summary.summarize rt prog proc in
            logtm INFO
                (sprintf "  > The summary has %d locations and %d rules"
                    sk.Sk.nlocs sk.Sk.nrules);
            logtm INFO ("  > Searching for reachable local states...");
            let sk = SymbSkel.keep_reachable sk in

            logtm INFO
                (sprintf "  > Found %d reachable locations and %d rules"
                    sk.Sk.nlocs sk.Sk.nrules);
            (* remove self-loops *)
            let sk = SymbSkel.filter_rules (fun r -> r.Sk.src <> r.Sk.dst) sk in
            (* deal with the effects of interval abstraction *)
            logtm INFO ("  > Optimizing guards...");
            let sk = SymbSkel.optimize_guards sk in
            Sk.to_file (sprintf "skel-%s.sk" proc#get_name) sk;
            logtm INFO ("    [DONE]");
            sk

        method update_runtime rt =
            let prog = self#get_output in
            rt#caches#set_struc prog (SkelStruc.compute_struc prog)
    end

