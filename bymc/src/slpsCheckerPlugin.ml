(*
 * Checking the properties using semi-linear regular path schema
 * that is computed with respect to the diameter, cf. porBounds
 *
 * Igor Konnov, 2014
 *)

open Printf

open Accums
open Debug
open SymbSkel
open Plugin
open PorBounds
open Spin
open SpinIr

let can_handle_spec prog _ s =
    match Ltl.classify_spec prog s with
    | Ltl.CondSafety (_, _) -> true
    | _ -> false


let get_proper_specs opts prog skels =
    let forms = Program.get_ltl_forms prog in
    let tt = Program.get_type_tab prog in
    let is_good name form =
        let asked = opts.Options.spec in
        (asked = "all" || asked = name) && (can_handle_spec tt name form)
    in
    let good, bad = StrMap.partition is_good forms in
    let p name _ =
        if opts.Options.spec <> "all" && opts.Options.spec <> name
        then printf "      > Skipped %s (since you asked)\n" name
        else printf "      > Skipped %s (not reachability)\n" name
    in
    StrMap.iter p bad;
    SymbSkel.expand_props_in_ltl_forms prog skels good


class slps_checker_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        method transform rt =
            let sprog = self#get_input0 in
            rt#caches#set_struc sprog (SkelStruc.compute_struc sprog);
            let each_proc skels proc =
                let sk = self#extract_proc rt sprog proc in
                sk :: skels
            in
            let skels =
                List.fold_left each_proc [] (Program.get_procs sprog)
            in
            let sk = match skels with
                | [sk] -> sk
                | skels -> SymbSkel.fuse skels "Fuse"
            in
            Sk.to_file "fuse.sk" sk;
            let loc_vars = IntMap.values sk.Sk.loc_vars in
            let ntt = (Program.get_type_tab sprog)#copy in
            let set_type v = ntt#set_type v (new data_type SpinTypes.TUNSIGNED) in
            BatEnum.iter set_type loc_vars;

            let tree, deps = PorBounds.make_schema_tree rt#solver sk in
            PorBounds.D.to_dot "flow.dot" sk deps;

            let nleafs = PorBounds.tree_leafs_count tree in
            let num = ref 0 in (* XXX *)
            let on_leaf length =
                num := !num + 1;
                logtm INFO (sprintf "    checked path schema: %4d length: %4d progress: %2d%%"
                !num length (!num * 100 / nleafs))
            in

            let check_tree name form tree =
                SlpsChecker.is_error_tree rt ntt sk on_leaf name form deps tree
            in
            log INFO "  > Running SlpsChecker...";
            log INFO (sprintf "    > %d schemas to inspect..." nleafs);
            let each_form name form =
                num := 0;
                logtm INFO (sprintf "      > Checking %s..." name);
                let err = check_tree name form tree in
                let msg =
                    if err
                    then sprintf "    > SLPS: counterexample for %s found" name
                    else sprintf "      > Spec %s holds" name
                in
                log INFO msg
            in
            let specs = get_proper_specs rt#caches#options sprog skels in
            StrMap.iter each_form specs;
            sprog

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
            ()
    end

