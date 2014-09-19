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


class slps_checker_plugin_t (plugin_name: string)
        (sk_plugin: SymbSkelPlugin.symb_skel_plugin_t)
        (por_bounds_plugin: PorBoundsPlugin.por_bounds_plugin_t) =
    object(self)
        inherit analysis_plugin_t plugin_name

        method transform rt =
            let input = self#get_input0 in
            let tt = Program.get_type_tab input in
            let tree = por_bounds_plugin#representative_tree in

            (* TODO: there must be only one skeleton for all process types! *)
            assert ((List.length sk_plugin#skels) = 1);
            let sk = List.hd sk_plugin#skels in
            let nleafs = PorBounds.tree_leafs_count tree in
            let num = ref 0 in (* XXX *)
            let on_leaf _ =
                num := !num + 1;
                logtm INFO (sprintf "    checked path schema: %4d progress: %2d%%" !num
                (!num * 100 / nleafs))
            in

            let check_tree form tree =
                SlpsChecker.is_error_tree rt tt sk on_leaf form tree
            in
            log INFO "  > Running SlpsChecker...";
            log INFO (sprintf "    > %d schemas to inspect..." nleafs);
            let each_form name form =
                printf "      > Checking %s...\n" name;
                let err = check_tree form tree in
                if err
                then printf "    > SLPS: counterexample for %s found\n" name
                else printf "      > Spec %s holds\n" name
            in
            let specs = get_proper_specs input sk_plugin#skels in
            StrMap.iter each_form specs;
            input

        method update_runtime rt =
            ()
    end

