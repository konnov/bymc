(**
 Checking the properties using semi-linear regular path schema
 that is computed with respect to the diameter
 
 @see PorBounds, SchemaChecker, SchemaCheckerLtl
 
 @author Igor Konnov, 2014-2016
 *)

open Printf

open Accums
open Debug
open SymbSkel
open Plugin
open PorBounds
open Spin
open SpinIr

module L = SchemaCheckerLtl

let is_safety_spec tt s =
    match Ltl.classify_spec tt s with
    | Ltl.CondSafety (_, _) -> true
    | _ -> false


(* TODO: use the formulas directly from the skeleton *)
let get_proper_specs opts prog skels check_fun =
    let forms = Program.get_ltl_forms prog in
    let is_good name form =
        let asked = opts.Options.spec in
        let expanded = expand_props_in_ltl prog skels form in
        Debug.ltrace Trc.scl
            (lazy (sprintf " expanded %s = %s\n" name (SpinIrImp.expr_s expanded)));
        (asked = "all" || asked = name) && (check_fun expanded)
    in
    let good, bad = StrMap.partition is_good forms in
    let p name _ =
        if opts.Options.spec <> "all" && opts.Options.spec <> name
        then printf "      > Skipped %s (since you asked)\n" name
        else printf "      > Skipped %s (not supported)\n" name
    in
    StrMap.iter p bad;
    SymbSkel.expand_props_in_ltl_forms prog skels good


class slps_checker_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        method is_ltl tech =
            tech <> Some "cav15" && tech <> Some "cav15-opt"

        method transform rt =
            let sprog = self#get_input0 in
            let tech = Options.get_plugin_opt rt#caches#options "schema.tech" in
            let sk = Summary.summarize_optimize_fuse rt sprog
                ~keep_selfloops:(self#is_ltl tech)
                    (* reachability is blind to self-loops *)
            in
            self#set_options rt;
            if "bounds" <> rt#caches#options.Options.spec
            then self#check tech rt sprog sk
            else begin (* compute the bounds using the summary *)
                let dom = rt#caches#analysis#get_pia_dom in
                let dom_size = dom#length in
                PorBounds.compute_diam rt#solver dom_size sk;
            end;
            sprog


        method check_reachability_cav15 rt sprog sk tt =
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
                log INFO (sprintf "  > nschemas = %d, min length = %d, max length = %d, avg length = %d"
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
                SchemaChecker.is_error_tree rt tt sk on_leaf name form deps tree
            in

            log INFO "  > Running SchemaChecker (the CAV'15 reachability version)...";
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
            let specs =
                get_proper_specs rt#caches#options sprog [sk] (is_safety_spec tt) in
            StrMap.iter each_form specs


        method check_ltl rt sprog sk tt =
            let flow_opt = SchemaOpt.is_flow_opt_enabled () in
            let deps = PorBounds.compute_deps ~against_only:flow_opt rt#solver sk in
            PorBounds.D.to_dot "flow.dot" sk deps;

            let check name form =
                L.find_error rt tt sk name form deps
            in
            log INFO "  > Running SchemaCheckerLtl (on the fly)...";
            let each_form name form =
                logtm INFO (sprintf "      > Checking %s..." name);
                let result = check name form in
                let msg =
                    if result.L.m_is_err_found
                    then sprintf "    > SLPS: counterexample for %s found" name
                    else sprintf "      > Spec %s holds" name
                in
                log INFO msg;
                printf "%s\n" (L.stat_s result.L.m_stat)
            in
            let can_handle f =
                let negated = Ltl.normalize_form (UnEx (NEG, f)) in
                L.can_handle_spec tt sk negated
            in
            let fprog = Ltl.embed_fairness sprog in
            let specs =
                get_proper_specs rt#caches#options fprog [sk] can_handle in
            StrMap.iter each_form specs


        method check tech rt sprog sk =
            let loc_vars = IntMap.values sk.Sk.loc_vars in
            let ntt = (Program.get_type_tab sprog)#copy in
            let set_type v = ntt#set_type v (new data_type SpinTypes.TUNSIGNED) in
            BatEnum.iter set_type loc_vars;

            if self#is_ltl tech
            then self#check_ltl rt sprog sk ntt
            else self#check_reachability_cav15 rt sprog sk ntt

        method update_runtime rt =
            ()

        method set_options rt =
            let opts = rt#caches#options in
            let getopt s = Options.get_plugin_opt opts s in
            let is_enabled opt = 
                opt = Some "1" || opt = Some "true" in
            let is_disabled no_opt = 
                no_opt = Some "1" || no_opt = Some "true" in
            let no_flow_opt = getopt "schema.noflowopt" in
            let no_reach_opt = getopt "schema.noreachopt" in
            let no_adaptive_reach_opt = getopt "schema.noadaptive" in
            let incremental = getopt "schema.incremental" in

            let reach_on =
                if no_reach_opt <> None
                (* a manually set option overrides everything *)
                then not (is_disabled no_reach_opt)
                else if is_enabled incremental
                    then begin
                        Debug.log INFO "  # schema.incremental=1 sets schema.noreachopt=1";
                        true  (* enable in the incremental mode *)
                    end else begin
                        Debug.log INFO "  # schema.incremental=0 sets schema.noreachopt=0";
                        false (* disable in the non-incremental mode *)
                    end
            in
            let adaptive_on =
                if no_adaptive_reach_opt <> None
                (* a manually set option overrides everything *)
                then not (is_disabled no_adaptive_reach_opt)
                else if is_enabled incremental
                    then begin
                        Debug.log INFO "  # schema.incremental=1 sets schema.noadaptive=1";
                        true (* enable in the incremental mode *)
                    end else begin
                        Debug.log INFO "  # schema.incremental=0 sets schema.noadaptive=0";
                        false  (* disable in the non-incremental mode *)
                    end
            in

            SchemaOpt.set_incremental (is_enabled incremental);
            Debug.log INFO
                (sprintf "  # The incremental mode is %s"
                    (if is_enabled incremental then "enabled" else "disabled"));

            SchemaOpt.set_flow_opt (not (is_disabled no_flow_opt));
            Debug.log INFO
                (sprintf "  # The control flow optimization is %s"
                    (if is_disabled no_flow_opt then "disabled" else "enabled"));

            SchemaOpt.set_reach_opt reach_on;
            Debug.log INFO
                (sprintf "  # The reachability optimization is %s"
                    (if reach_on then "enabled" else "disabled"));

            SchemaOpt.set_adaptive_reach_opt adaptive_on;
            Debug.log INFO
                (sprintf "  # The adaptive reachability optimization is %s"
                    (if adaptive_on then "enabled" else "disabled"));
    end

