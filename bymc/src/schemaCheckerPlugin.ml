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
            let sk = Summary.summarize_optimize_fuse rt sprog in
            if "bounds" <> rt#caches#options.Options.spec
            then self#check rt sprog sk
            else begin (* compute the bounds using the summary *)
                let dom = rt#caches#analysis#get_pia_dom in
                let dom_size = dom#length in
                PorBounds.compute_diam rt#solver dom_size sk;
            end;
            sprog


        method check rt sprog sk =
            let loc_vars = IntMap.values sk.Sk.loc_vars in
            let ntt = (Program.get_type_tab sprog)#copy in
            let set_type v = ntt#set_type v (new data_type SpinTypes.TUNSIGNED) in
            BatEnum.iter set_type loc_vars;

            let tree, deps = PorBounds.make_schema_tree rt#solver sk in
            PorBounds.D.to_dot "flow.dot" sk deps;

            let nleafs = PorBounds.tree_leafs_count tree in
            let npaths, minlen, maxlen, totallen =
                    ref 0, ref max_int, ref 0, ref 0 in
            let reset_stat () =
                npaths := 0; minlen := max_int; maxlen := 0; totallen := 0
            in
            let update_stat length =
                npaths := !npaths + 1;
                minlen := min length !minlen;
                maxlen := max length !maxlen;
                totallen := !totallen + length
            in
            let print_stat () =
                if !npaths = 0
                then npaths := 1;
                log INFO (sprintf "  > npaths = %d, min length = %d, max length = %d, avg length = %d"
                    !npaths !minlen !maxlen (!totallen / !npaths));
            in

            let lasttime = ref (Unix.time ()) in
            let on_leaf length =
                update_stat length;
                let newtime = Unix.time () in
                if (newtime -. !lasttime) > 5.0
                then begin
                    lasttime := newtime;
                    logtm INFO (sprintf "    checked path schema: %4d length: %4d progress: %2d%%"
                    !npaths length (!npaths * 100 / nleafs))
                end
            in
            let check_tree name form tree =
                SchemaChecker.is_error_tree rt ntt sk on_leaf name form deps tree
            in

            log INFO "  > Running SlpsChecker...";
            log INFO (sprintf "    > %d schemas to inspect..." nleafs);
            let each_form name form =
                reset_stat ();
                logtm INFO (sprintf "      > Checking %s..." name);
                let err = check_tree name form tree in
                let msg =
                    if err
                    then sprintf "    > SLPS: counterexample for %s found" name
                    else sprintf "      > Spec %s holds" name
                in
                log INFO msg;
                print_stat ()
            in
            let specs = get_proper_specs rt#caches#options sprog [sk] in
            StrMap.iter each_form specs


        method update_runtime rt =
            ()
    end

