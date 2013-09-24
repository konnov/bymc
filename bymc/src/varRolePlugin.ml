open Plugin
open VarRole

class var_role_plugin_t (plugin_name: string) =
    object
        inherit analysis_plugin_t plugin_name

        val mutable m_roles: var_role_tbl option =  None
        
        method get_roles =
            match m_roles with
            | Some r -> r
            | None -> raise (Plugin_error "No result computed")

        method transform rtm prog =
            m_roles <- Some (identify_var_roles prog);
            prog

        method update_runtime rtm =
            match m_roles with
            | Some r -> rtm#caches#analysis#set_var_roles r
            | _ -> ()
    end

