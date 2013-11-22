open Printf

open Debug
open PiaDataPlugin
open Plugin

class nusmv_ctr_cluster_plugin_t (plugin_name: string)
        (out_name: string) (pia_data_plugin: pia_data_plugin_t) =

    object(self)
        inherit transform_plugin_t plugin_name

        method is_disabled rt =
            rt#caches#options.Options.mc_tool <> Options.ToolNusmv

        method transform rt prog =
            let caches = rt#caches in
            let solver = rt#solver in
            log INFO (sprintf
                "> writing ssa NuSMV model to %s.smv..." "main-ssa");
            let intabs_prog = pia_data_plugin#get_output in
            NusmvSsaEncoding.transform rt "main-ssa" intabs_prog self#get_input;
            NusmvSsaEncoding.mk_counter_reach
                rt "main-ssa-reach" intabs_prog self#get_input;
            log INFO (sprintf
                "> writing clusterized NuSMV model to %s.smv... SKIPPED" out_name);
            let roles =
                rt#caches#analysis#get_var_roles pia_data_plugin#get_input in
            (*
            NusmvCounterClusterPass.transform
                solver caches roles out_name intabs_prog prog;
                *)
            log INFO "[DONE]";
            prog

        method update_runtime _ =
            ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)
    end

