open AbsInterval
open AbsCounter
open Debug
open Invariant
open PiaCtrCtx
open PiaDataCtx
open PiaDataPlugin
open Plugin
open Program
open Writer

class pia_counter_plugin_t (plugin_name: string) (data_p: pia_data_plugin_t) =
    object(self)
        inherit transform_plugin_t plugin_name

        val mutable m_ctr_abs_ctx_tbl: ctr_abs_ctx_tbl option = None
        val mutable m_ref_step = 0 (* refinement step *)
        val mutable m_vass = Program.empty

        method transform rtm prog =
            let caches = rtm#caches in
            let solver = rtm#solver in
            let dom = caches#analysis#get_pia_dom in
            let roles = caches#analysis#get_var_roles in
            let proc_names = 
                if self#has_opt rtm "procs"
                then Str.split (Str.regexp_string ",") (self#get_opt rtm "procs")
                else List.map (fun p -> p#get_name) (Program.get_procs prog)
            in
            let is_included p = List.mem p#get_name proc_names in
            let procs = List.filter is_included (Program.get_procs prog) in

            let ctx = new ctr_abs_ctx_tbl dom roles prog procs in
            m_ctr_abs_ctx_tbl <- Some ctx;
            caches#analysis#set_pia_ctr_ctx_tbl ctx;

            (* construct VASS *)
            if m_ref_step = 0
            then begin
                let old_pia_data = caches#analysis#get_pia_data_ctx in
                (* we need data abstraction with a hack,
                   don't abstract shared *)
                let pia_data = new pia_data_ctx roles in
                pia_data#set_hack_shared true;
                caches#analysis#set_pia_data_ctx pia_data;
                let int_prog = do_interval_abstraction solver caches
                        data_p#get_input proc_names in
                let vass =
                    self#make_vass solver dom caches int_prog proc_names false
                in
                log INFO "  check the invariants";
                check_all_invariants rtm vass;
                m_vass <-
                    self#make_vass solver dom caches int_prog proc_names true;
                caches#analysis#set_pia_data_ctx old_pia_data
            end;

            (* construct counter abstraction *)
            let funcs = new abs_ctr_funcs dom prog solver in
            log INFO "> Constructing counter abstraction";
            let ctrabs_prog =
                do_counter_abstraction funcs solver caches prog proc_names
            in
            write_to_file false "abs-counter-general.prm"
                (units_of_program ctrabs_prog) (get_type_tab ctrabs_prog);
            log INFO "[DONE]";
            ctrabs_prog

        method private make_vass solver dom caches prog proc_names embed_inv =
            log INFO "> Constructing VASS...";
            let vass_funcs = new vass_funcs dom prog solver in
            vass_funcs#set_embed_inv embed_inv;
            let vass_prog =
                do_counter_abstraction vass_funcs solver caches prog proc_names
            in
            write_to_file false "abs-vass.prm"
                (units_of_program vass_prog) (get_type_tab vass_prog);
            log INFO "> Constructing SMT transducers...";
            let xducer_prog = SmtXducerPass.do_xducers caches vass_prog in
            write_to_file false "abs-xducers.prm"
                (units_of_program xducer_prog) (get_type_tab xducer_prog);
            log INFO "  [DONE]"; flush stdout;
            xducer_prog

        method update_runtime rtm =
            match m_ctr_abs_ctx_tbl with
            | Some c -> rtm#caches#analysis#set_pia_ctr_ctx_tbl c
            | _ -> ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, path)
    end

