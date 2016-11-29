open Printf

open Accums
open Debug
open Options
open Plugin
open Program
open Spin
open SymbSkel
open SchemaSmt
open Smt

open TaSynt

(**
  Synthesizing threshold automata using CEGYS.

  @author Igor Konnov, 2016
 *)
class ta_synt_plugin_t (plugin_name: string) (ta_source: TaSource.ta_source_t) =
    object(self)
        inherit transform_plugin_t plugin_name
        inherit TaSource.ta_source_t

        val mutable m_out_skel: Sk.skel_t option = None
        val mutable m_synt_solver = None (* we need own our copy here to keep counterex. *)
        val mutable m_unknowns_vec: (string * Spin.token SpinIr.expr) list = []
        val mutable m_n_cexs = 0

        method transform rt =
            let template_skel = ta_source#get_ta in
            if m_unknowns_vec = []
            then begin
                let mk0 v = (v#get_name, SpinIr.IntConst 0) in
                m_unknowns_vec <- List.map mk0 template_skel.Sk.unknowns;
                log INFO ("> Starting with: " ^ (unknowns_vec_s m_unknowns_vec));
                let synt_solver = self#get_synt_solver rt in
                let int_type = new SpinIr.data_type SpinTypes.TUNSIGNED in
                let append_var v = synt_solver#append_var_def v int_type in
                List.iter append_var (template_skel.Sk.unknowns)
            end;
            let out_skel = replace_unknowns template_skel m_unknowns_vec in
            Sk.to_file "synt.ta" out_skel;
            m_out_skel <- Some out_skel;
            self#get_input0


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

        method update_runtime rt =
            ()

        method decode_trail _ path =
            path

        method refine rt path =
            let template_skel = ta_source#get_ta in
            let new_cex = C.load_cex "cex-fixme.scm" in
            C.save_cex (sprintf "cex%d.scm" m_n_cexs) new_cex;
            m_n_cexs <- m_n_cexs + 1;
            let synt_solver = self#get_synt_solver rt in
            let type_tab = Program.get_type_tab self#get_input0 in
            let fixed_skel = replace_unknowns template_skel m_unknowns_vec in
            let flow_opt = SchemaOpt.is_flow_opt_enabled () in
            let deps =
                PorBounds.compute_deps ~against_only:flow_opt rt#solver fixed_skel
            in
            TaSynt.push_counterexample rt#solver synt_solver type_tab fixed_skel deps template_skel new_cex;
            if not synt_solver#check
            then begin
                log INFO (sprintf "Collected %d counterexamples in total" m_n_cexs);
                log INFO ("(synt-no-solution)");
                (false, self#get_output)
            end else begin
                m_unknowns_vec <- self#find_unknowns synt_solver template_skel;
                log INFO ("> Next unknowns to try: " ^ (unknowns_vec_s m_unknowns_vec));
                (true, self#get_output)
            end

        method private find_unknowns synt_solver template =
            let q = synt_solver#get_model_query in
            let try_var v = ignore (Smt.Q.try_get q (SpinIr.Var v)) in
            List.iter try_var template.Sk.unknowns;
            let new_query = synt_solver#submit_query q in
            let map v =
                match Smt.Q.try_get new_query (Var v) with
                    | Smt.Q.Result e ->
                        (v#get_name, e)

                    | Smt.Q.Cached ->
                        raise (Failure "Unexpected Cached")
            in
            List.map map template.Sk.unknowns

    end

