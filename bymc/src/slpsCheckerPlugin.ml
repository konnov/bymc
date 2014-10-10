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

let can_handle_spec prog _ s =
    match Ltl.classify_spec prog s with
    | Ltl.CondSafety (_, _) -> true
    | _ -> false


let get_proper_specs prog skels =
    let forms = Program.get_ltl_forms prog in
    let tt = Program.get_type_tab prog in
    let good, bad = StrMap.partition (can_handle_spec tt) forms in
    let p name _ =
        printf "      > Skipped %s (not reachability)\n" name in
    StrMap.iter p bad;
    SymbSkel.expand_props_in_ltl_forms prog skels good


class slps_checker_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        method transform rt =
            let sprog = self#get_input0 in
            rt#caches#set_struc sprog (SkelStruc.compute_struc sprog);
            let each_proc (skels, prog) proc =
                let sk, new_prog = self#extract_proc rt prog proc in
                (sk :: skels, new_prog)
            in
            let skels, prog =
                List.fold_left each_proc ([], sprog) (Program.get_procs sprog)
            in
            let dom_size = rt#caches#analysis#get_pia_dom#length in
            (* TODO: there must be only one skeleton for all process types! *)
            assert (1 = (List.length skels));
            let sk = List.hd skels in
            let tt = Program.get_type_tab prog in
            let tree = PorBounds.compute_diam rt#solver dom_size sk in

            let nleafs = PorBounds.tree_leafs_count tree in
            let num = ref 0 in (* XXX *)
            let on_leaf length =
                num := !num + 1;
                logtm INFO (sprintf "    checked path schema: %4d length: %4d progress: %2d%%"
                !num length (!num * 100 / nleafs))
            in

            let check_tree name form tree =
                SlpsChecker.is_error_tree rt tt sk on_leaf name form tree
            in
            log INFO "  > Running SlpsChecker...";
            log INFO (sprintf "    > %d schemas to inspect..." nleafs);
            let each_form name form =
                num := 0;
                printf "      > Checking %s...\n" name;
                let err = check_tree name form tree in
                if err
                then printf "    > SLPS: counterexample for %s found\n" name
                else printf "      > Spec %s holds\n" name
            in
            let specs = get_proper_specs prog skels in
            StrMap.iter each_form specs;
            prog

        method extract_proc rt prog proc =
            logtm INFO ("  > Computing the summary of " ^ proc#get_name);
            let sk, new_prog = Summary.summarize rt prog proc in
            logtm INFO
                (sprintf "  > The summary has %d locations and %d rules"
                    sk.Sk.nlocs sk.Sk.nrules);
            logtm INFO ("  > Searching for reachable local states...");
            let sk = SymbSkel.keep_reachable sk in
            logtm INFO
                (sprintf "  > Found %d reachable locations and %d rules"
                    sk.Sk.nlocs sk.Sk.nrules);
            let sk = SymbSkel.filter_rules (fun r -> r.Sk.src <> r.Sk.dst) sk in
            Sk.to_file (sprintf "skel-%s.sk" proc#get_name) sk;
            logtm INFO ("    [DONE]");
            sk, new_prog

        method update_runtime rt =
            ()
    end

