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
            let paths = por_bounds_plugin#representative_paths in
            (* TODO: there must be only one skeleton for all process types! *)
            assert ((List.length sk_plugin#skels) = 1);
            let sk = List.hd sk_plugin#skels in
            let npaths = List.length paths in

            let each_path form err i path =
                let percent = i * 100 / npaths in
                if err
                then true
                else begin
                    logtm INFO (sprintf "      > inspecting path schema %d (%d%% done)" i percent);
                    let is_err = SlpsChecker.is_error_path rt tt sk form path in
                    if is_err then log INFO "      [ERR]";
                    is_err
                end
            in
            log INFO "  > Running SlpsChecker...";
            log INFO (sprintf "    > %d schemas to inspect..." npaths);
            let each_form name form =
                printf "      > Checking %s...\n" name;
                let err = List.fold_left2 (each_path form) false (range 0 npaths) paths in
                if err then printf "    > SLPS: counterexample for %s found\n" name;
            in
            let specs = get_proper_specs input sk_plugin#skels in
            StrMap.iter each_form specs;
            input

        method update_runtime rt =
            ()
    end

