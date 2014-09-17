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

(*
let can_handle_spec prog s =
    match Ltl.classify_spec prog s with
    | Ltl.CondSafety (_, _) -> true
    | _ -> false
    *)


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
            let specs = SymbSkel.expand_props_in_ltl input sk_plugin#skels in

            let each_path err i path =
                let each_form name form err =
                    (*
                    if not (can_handle_spec input form)
                    then begin
                        log INFO (sprintf "      > Spec %s is not supported" name);
                        false
                    end
                    else *) if SlpsChecker.is_error_path rt tt sk form path
                    then begin
                        log INFO (sprintf "      > Spec %s is violated" name);
                        true
                    end
                    else false
                in
                if err
                then true
                else begin
                    log INFO (sprintf "      > inspecting path scheme %d" i);
                    let is_err = StrMap.fold each_form specs false in
                    log INFO (if is_err then "      [ERR]" else "      [OK]");
                    is_err
                end
            in
            log INFO "  > Running SlpsChecker...";
            let npaths = List.length paths in
            let err = List.fold_left2 each_path false (range 0 npaths) paths in
            if err
            then Printf.printf "    > SLPS: counterexample found\n";
            input

        method update_runtime rt =
            ()
    end

