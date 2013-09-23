open PiaDom
open Plugin

class pia_dom_plugin_t =
    object(self)
        inherit analysis_plugin_t

        val mutable m_dom: pia_domain option =  None

        method transform rtm prog =
            let roles = rtm#caches#analysis#get_var_roles in
            m_dom <- Some (create rtm#solver roles prog);
            prog

        method update_runtime rtm =
            match m_dom with
            | Some d -> rtm#caches#analysis#set_pia_dom d
            | _ -> ()
    end

