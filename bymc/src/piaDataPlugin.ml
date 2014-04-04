open AbsInterval
open Debug
open PiaDataCtx
open Plugin
open Program
open SkelStruc
open VarRole

class pd_plugin_t ?(keep_shared = false) (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        val mutable m_pia_data_ctx: pia_data_ctx option = None

        method transform rt =
            let prog = self#get_input0 in
            let caches = rt#caches in
            let ctx = new pia_data_ctx (caches#analysis#get_var_roles prog) in
            ctx#set_hack_shared keep_shared;
            m_pia_data_ctx <- Some ctx;
            caches#analysis#set_pia_data_ctx ctx;

            let proc_names = if self#has_opt rt "procs"
            then Str.split (Str.regexp_string ",") (self#get_opt rt "procs")
            else List.map (fun p -> p#get_name) (Program.get_procs prog)
            in
            log INFO "> Constructing interval abstraction";
            let intabs_prog =
                do_interval_abstraction rt prog proc_names in
            let fname = if keep_shared
                then "abs-interval-semi.prm"
                else "abs-interval.prm" in
            Writer.write_to_file false fname
                (units_of_program intabs_prog) (get_type_tab intabs_prog)
                (Hashtbl.create 10);
            log INFO "[DONE]";
            intabs_prog

        method update_roles rt prog =
            let ctx = Accums.get_some m_pia_data_ctx in
            let dom = rt#caches#analysis#get_pia_dom in
            let upper = dom#length - 1 in
            let new_roles = new var_role_tbl in
            let each_var abs_role conc_role v =
                if ctx#var_needs_abstraction v
                then new_roles#add v abs_role
                else new_roles#add v conc_role
            in
            List.iter
                (each_var (VarRole.SharedBoundedInt (0, upper)) SharedUnbounded)
                (Program.get_shared prog);
            List.iter
                (each_var (VarRole.BoundedInt (0, upper)) LocalUnbounded)
                (Program.get_all_locals prog);
            rt#caches#analysis#set_var_roles prog new_roles
            

        method update_runtime rt =
            (* update regions *)
            rt#caches#set_struc self#get_output (compute_struc self#get_output);
            (* update variable roles *)
            self#update_roles rt self#get_output;
            (* update context *)
            match m_pia_data_ctx with
            | Some c -> rt#caches#analysis#set_pia_data_ctx c
            | _ -> ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)
    end

