(*
 * Checking the properties using semi-linear regular path scheme
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
            let each_sk error_found sk =
                let each_path err p =
                    if err
                    then true
                    else not (SlpsChecker.check_path rt tt sk p)
                in
                if error_found
                then true
                else List.fold_left each_path false paths
            in
            log INFO "  > Running SlpsChecker...";
            if List.fold_left each_sk false sk_plugin#skels
            then Printf.printf "    > SLPS: counterexample found\n";
            input

        method update_runtime rt =
            ()
    end

