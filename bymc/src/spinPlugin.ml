open Printf

open Debug
open Plugin
open Program
open Writer

class spin_plugin_t (plugin_name: string) (out_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        method transform rtm prog =
            if rtm#caches#options.Options.mc_tool <> Options.ToolSpin
            then prog
            else begin
                let filename = out_name ^ ".prm" in
                log INFO (sprintf "> Writing Promela model %s..." out_name);
                let f_prog = Ltl.embed_fairness prog in
                (* TODO: give it a better name like target-spin? *)
                write_to_file true filename
                    (units_of_program f_prog) (get_type_tab f_prog);
                f_prog
            end

        method update_runtime _ =
            ()

        (* we don't know yet how to refine the data abstraction *)
        method decode_trail _ path = path

        method refine _ path = (false, path)
    end

