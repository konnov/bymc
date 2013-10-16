open AbsInterval
open Debug
open PiaDataCtx
open Plugin
open Program

class pia_data_plugin_t (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        val mutable m_pia_data_ctx: pia_data_ctx option = None

        method transform rt prog =
            let caches = rt#caches in
            let ctx = new pia_data_ctx (caches#analysis#get_var_roles prog) in
            m_pia_data_ctx <- Some ctx;
            caches#analysis#set_pia_data_ctx ctx;

            let proc_names = if self#has_opt rt "procs"
            then Str.split (Str.regexp_string ",") (self#get_opt rt "procs")
            else List.map (fun p -> p#get_name) (Program.get_procs prog)
            in
            log INFO "> Constructing interval abstraction";
            let intabs_prog =
                do_interval_abstraction rt prog proc_names in
            Writer.write_to_file false "abs-interval.prm"
                (units_of_program intabs_prog) (get_type_tab intabs_prog);
            log INFO "[DONE]";
            intabs_prog

        method update_runtime rt =
            match m_pia_data_ctx with
            | Some c -> rt#caches#analysis#set_pia_data_ctx c
            | _ -> ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)
    end

