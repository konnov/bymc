open AbsCounter
open Debug
open PiaCtrCtx
open Plugin
open Program
open Writer

class pia_counter_plugin_t (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        val mutable m_ctr_abs_ctx_tbl: ctr_abs_ctx_tbl option = None

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
            let funcs = new abs_ctr_funcs dom prog solver in
            log INFO "> Constructing counter abstraction";
            let ctrabs_prog =
                do_counter_abstraction funcs solver caches prog proc_names
            in
            write_to_file false "abs-counter-general.prm"
                (units_of_program ctrabs_prog) (get_type_tab ctrabs_prog);
            log INFO "[DONE]";
            ctrabs_prog

        method update_runtime rtm =
            match m_ctr_abs_ctx_tbl with
            | Some c -> rtm#caches#analysis#set_pia_ctr_ctx_tbl c
            | _ -> ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, path)
    end
