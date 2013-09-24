open Printf

open Debug
open PiaDataPlugin
open Plugin

class nusmv_ctr_cluster_plugin_t (plugin_name: string)
        (out_name: string) (pia_data_plugin: pia_data_plugin_t) =

    object(self)
        inherit transform_plugin_t plugin_name

        method transform rtm prog =
            let caches = rtm#caches in
            let solver = rtm#solver in
            if caches#options.Options.mc_tool <> Options.ToolNusmv
            then prog
            else begin
                log INFO (sprintf
                    "> writing clusterized NuSMV model to %s.smv..." out_name);
                let intabs_prog = pia_data_plugin#get_output in
                NusmvCounterClusterPass.transform
                    solver caches out_name intabs_prog prog;
                log INFO "[DONE]";
                prog
            end

        method update_runtime _ =
            ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, path)
    end

