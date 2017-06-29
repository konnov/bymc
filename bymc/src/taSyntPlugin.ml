open Printf

open Accums
open Debug
open Options
open Plugin
open PorBounds
open Program
open Spin
open SymbSkel
open SchemaSmt
open Smt

open TaSynt

module L = SchemaCheckerLtl

(**
  Synthesizing threshold automata using CEGYS.

  @author Igor Konnov, 2016-2017

  TODO: extract large pieces of code into a separate module
 *)
class ta_synt_plugin_t (plugin_name: string) (ta_source: TaSource.ta_source_t) =
    object(self)
        inherit transform_plugin_t plugin_name
        inherit TaSource.ta_source_t

        val mutable m_out_skel: Sk.skel_t option = None
        val mutable m_synt_solver = None (* we need own our copy here to keep counterex. *)
        val mutable m_unknowns_vec: (string * Spin.token SpinIr.expr) list = []
        val mutable m_n_cexs = 0
        val mutable m_is_mpi = true (* using MPI for synthesis in parallel *)

        method transform rt =
            let template_skel = ta_source#get_ta in
            self#init rt;
            (* disable incompatible options *)
            SchemaOpt.set_incremental false;
            SchemaOpt.set_reach_opt false;
            SchemaOpt.set_use_guard_predicates true; (* BUGFIX-20170628 *)
            (* introduce variables for the location counters *)
            let loc_vars = IntMap.values template_skel.Sk.loc_vars in
            let ntt = (Program.get_type_tab self#get_input0)#copy in
            let new_data_type = new SpinIr.data_type SpinTypes.TUNSIGNED in
            let set_type v = ntt#set_type v new_data_type in
            BatEnum.iter set_type loc_vars;
            (* verify/refine loop *)
            let rec loop () =
                log INFO ("> Next unknowns to try: " ^ (unknowns_vec_s m_unknowns_vec));
                let fixed_skel = replace_unknowns_in_skel template_skel m_unknowns_vec in
                Sk.to_file "synt.ta" fixed_skel;
                let finished =
                    if is_ta_vacuous rt#solver fixed_skel
                    then begin
                        log INFO "> Assumptions are violated";
                        if self#is_master
                        then begin
                            exclude_unknowns (get_some m_synt_solver)
                                template_skel.Sk.assumes m_unknowns_vec;
                            not (self#update_master rt)
                        end
                        else not (self#update_worker rt)
                    end else begin
                        (* Compute the dependencies by instantiating the unknowns,
                           while keeping all the expressions symbolic.
                           We will need it to generalize a counterexample.
                         *)
                        let flow_opt = SchemaOpt.is_flow_opt_enabled () in
                        let symb_deps = PorBounds.compute_deps
                            ~against_only:flow_opt
                            ~ex_rewrite_f:(TaSynt.replace_unknowns_in_expr m_unknowns_vec)
                            rt#solver template_skel
                        in
                        (* assign values to the unknowns *)
                        let fixed_deps =
                            replace_unknowns_in_deps symb_deps m_unknowns_vec
                        in
                        (* verify *)
                        let has_cex =
                            self#has_counterex rt ntt fixed_skel fixed_deps in
                        (* debug begins *)
                        if not has_cex
                        then begin
                            (* double check with a sequential verifier *)
                            if m_is_mpi && self#is_master then begin
                                log INFO ("> The parallel verifier reports OK");
                                log INFO ("> Checking with the sequential verifier");
                                m_is_mpi <- false;
                                let has_seq_cex = self#has_counterex rt ntt fixed_skel fixed_deps in
                                m_is_mpi <- true;
                                if has_seq_cex
                                then begin
                                    log ERROR ("> The sequential verifier has found a bug");
                                    assert false;
                                end
                            end
                        end;
                        (* debug ends *)
                        not has_cex || not (self#do_refine rt ntt symb_deps fixed_skel);
                    end
                in
                if finished
                then log INFO (sprintf "> Finished after %d refinements" m_n_cexs)
                else loop ()
            in
            loop ();
            self#get_input0

        method private has_counterex rt type_tab fixed_skel fixed_deps =
            (* call the ltl technique *)
            log INFO "  > Running SchemaCheckerLtl (on the fly)...";
            let do_check form_type forms =
                let check_fun = (* TODO: use a functor somewhere! *)
                    if m_is_mpi
                    then L.find_error_in_many_forms_parallel
                    else L.find_error_in_many_forms_interleaved
                in
                match check_fun rt type_tab fixed_skel forms fixed_deps with
                | None ->
                    log INFO (sprintf "      > %s specifications hold" form_type);
                    false

                | Some name ->
                    log INFO (sprintf "    > SLPS: counterexample for %s found" name);
                    true
            in
            (* check the propositional formulas first, as they are the easiest *)
            let all_forms = StrMap.bindings fixed_skel.Sk.forms in
            let is_prop (_, f) = Ltl.is_propositional type_tab f in
            let prop_forms, ltl_forms = List.partition is_prop all_forms in
            (do_check "Propositional" prop_forms) || (do_check "Temporal" ltl_forms)

        method private update_worker rt =
            match (Mpi.broadcast None 0 Mpi.comm_world) with
            | None ->
                    log INFO "> Master node reports no solution. Aborting.";
                    false

            | Some vec ->
                    m_unknowns_vec <- vec;
                    true

        method private update_master rt =
            let synt_solver = self#get_synt_solver rt in
            let template_skel = ta_source#get_ta in
            if not synt_solver#check
            then begin
                log INFO (sprintf "> Collected %d counterexamples in total" m_n_cexs);
                log INFO "> NO SOLUTION EXIST. Oops.";
                if m_is_mpi
                then ignore (Mpi.broadcast None 0 Mpi.comm_world);
                false
            end else begin
                let vec = self#find_unknowns synt_solver template_skel in
                if vec = m_unknowns_vec
                then begin
                    log INFO "> REFINEMENT IS STUCK. The vector of unknowns is not changing...";
                    log INFO ("  > Unknowns vector: " ^ (unknowns_vec_s vec));
                    if m_is_mpi
                    then ignore (Mpi.broadcast None 0 Mpi.comm_world);
                    false
                end else begin
                    m_unknowns_vec <- vec;
                    if m_is_mpi
                    then ignore (Mpi.broadcast (Some vec) 0 Mpi.comm_world);
                    true
                end
            end


        method do_refine rt type_tab symb_deps fixed_skel =
            if not self#is_master
            then self#update_worker rt
            else begin
                let template_skel = ta_source#get_ta in
                let new_cex = C.load_cex "cex-fixme.scm" in
                C.save_cex (sprintf "cex%d.scm" m_n_cexs) new_cex;
                m_n_cexs <- m_n_cexs + 1;
                let synt_solver = self#get_synt_solver rt in
                TaSynt.push_counterexample rt#solver synt_solver type_tab
                    fixed_skel symb_deps template_skel m_unknowns_vec new_cex;
                self#update_master rt
            end


        method private init rt =
            let template_skel = ta_source#get_ta in
            let mk0 v = (v#get_name, SpinIr.IntConst 0) in
            m_unknowns_vec <- List.map mk0 template_skel.Sk.unknowns;
            log INFO ("> Starting with: " ^ (unknowns_vec_s m_unknowns_vec));
            if self#is_master then begin
                (* in MPI mode, only the master is running the generator *)
                let synt_solver = self#get_synt_solver rt in
                let unsigned = new SpinIr.data_type SpinTypes.TUNSIGNED in
                let signed = new SpinIr.data_type SpinTypes.TINT in
                let append_var tp v = synt_solver#append_var_def v tp in
                List.iter (append_var signed) (template_skel.Sk.unknowns);
                List.iter (append_var unsigned) (template_skel.Sk.params);
                let assume e = ignore (synt_solver#append_expr e) in
                List.iter assume template_skel.Sk.assumes;
            end


        method private get_ta =
            match m_out_skel with
            | Some sk -> sk
            | None -> raise (Failure "ta_synt_plugin_t must have been called")


        method private get_synt_solver rt =
            match m_synt_solver with
            | Some solver ->
                solver

            | None ->
                let solver = rt#solver#clone_not_started "synt" in
                solver#start;
                m_synt_solver <- Some solver;
                solver

        method private find_unknowns synt_solver template =
            let q = synt_solver#get_model_query in
            let try_var v = ignore (Smt.Q.try_get q (SpinIr.Var v)) in
            List.iter try_var template.Sk.unknowns;
            let new_query = synt_solver#submit_query q in
            let map v =
                match Smt.Q.try_get new_query (SpinIr.Var v) with
                    | Smt.Q.Result e ->
                        (v#get_name, e)

                    | Smt.Q.Cached ->
                        raise (Failure "Unexpected Cached")
            in
            List.map map template.Sk.unknowns

        method private is_master =
            not m_is_mpi || 0 = (Mpi.comm_rank Mpi.comm_world)

        method dispose rt =
            (self#get_synt_solver rt)#stop

        method update_runtime rt =
            ()

        method decode_trail _ path =
            path

        method refine _ _ =
            (false, self#get_input0)

    end

