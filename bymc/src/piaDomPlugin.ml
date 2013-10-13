open Debug
open PiaDom
open Plugin
open SpinIr

class pia_dom_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        val mutable m_dom: pia_domain option =  None

        method transform rtm prog =
            let roles = rtm#caches#analysis#get_var_roles prog in
            let pxz = (self#has_opt rtm "pxz02")
                && (self#get_opt rtm "pxz02") <> "0" in
            if pxz
            then begin
                m_dom <- Some (new pia_domain [Const 0; Const 1; Const 2]);
                log INFO "   forced (0, 1, \\infty) by Pnueli, Xu, Zuck 2002"
            end else m_dom <- Some (create rtm#solver roles prog);
            prog

        method update_runtime rtm =
            match m_dom with
            | Some d -> rtm#caches#analysis#set_pia_dom d
            | _ -> ()
    end

