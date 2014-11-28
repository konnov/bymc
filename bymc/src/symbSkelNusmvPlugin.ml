
open Printf

open Debug
open Plugin

class skel_nusmv_plugin_t (plugin_name: string) (out_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        method is_disabled rt =
            rt#caches#options.Options.mc_tool <> Options.ToolNusmv

        method transform rt =
            log INFO (sprintf
                "> writing summary NuSMV model to %s.smv..." "main-sum");
            let prog = self#get_input0 in
            let intabs_prog = self#get_input1 in
            let sk = Summary.summarize_optimize_fuse rt intabs_prog in
            SymbSkelNusmv.transform rt "main-sum" intabs_prog prog [sk];
            log INFO "[DONE]";
            prog

        method update_runtime _ =
            ()

        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)
    end
