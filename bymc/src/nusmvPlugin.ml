open Printf

open Debug
open Plugin

class nusmv_plugin_t (plugin_name: string) (out_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        method is_disabled rtm =
            rtm#caches#options.Options.mc_tool <> Options.ToolNusmv

        method transform rt prog =
            let solver = rt#solver in
            let caches = rt#caches in
            log INFO (sprintf "> writing NuSMV model to %s.smv..." out_name);
            let struc = new Infra.proc_struc_cache in
            let extract_reg proc =
                let reg_tab = SkelStruc.extract_skel proc#get_stmts in
                struc#set_regions proc#get_name reg_tab
            in
            List.iter extract_reg (Program.get_procs prog);
            rt#caches#set_struc prog struc;
            NusmvPass.transform solver caches
                NusmvPass.LocalShared out_name prog;
            log INFO "[DONE]";
            prog

        method update_runtime _ =
            ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)
    end

