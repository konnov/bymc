open Printf

open Debug
open Plugin

class nusmv_plugin_t (out_name: string) =
    object(self)
        inherit transform_plugin_t

        method transform rtm prog =
            let caches = rtm#caches in
            if caches#options.Options.mc_tool <> Options.ToolNusmv
            then prog
            else begin
                let solver = rtm#solver in
                log INFO (sprintf "> writing NuSMV model to %s.smv..." out_name);
                let _ = SkelStruc.pass caches prog in
                NusmvPass.transform solver caches NusmvPass.LocalShared
                    out_name prog;
                log INFO "[DONE]";
                prog
            end

        method update_runtime _ =
            ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, path)
    end

