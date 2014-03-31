open Plugin
open VarRole

class vr_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        val mutable m_roles: var_role_tbl option =  None
        
        method get_roles =
            match m_roles with
            | Some r -> r
            | None -> raise (Plugin_error "No result computed")

        method transform rt =
            let prog = self#get_input0 in
            let r = identify_var_roles prog in
            m_roles <- Some r;
            prog

        method update_runtime rt =
            match m_roles with
            | Some r ->
                rt#caches#analysis#set_var_roles self#get_output r
            | _ -> ()
    end

