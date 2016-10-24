
open Plugin
open SymbSkel

(**
  A plugin that converts a program in Promela into a threshold automaton.

  @author Igor Konnov, 2016
  *)

class promela_to_ta_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t(plugin_name)

        val mutable m_skel: Sk.skel_t option = None

        method get_ta =
            match m_skel with
            | Some sk -> sk
            | None ->
                let m =
                    "Plugin promela_to_ta_plugin_t has not been called yet"
                in
                raise (Failure m)

        method transform rt =
            (* Since the current definition of analysis_plugin_t requires
               us to transform a Program to a Program, we cannot return a
               threshold automaton directly. Instead of that, we keep it as
               an attribute that can be accessed with a method.
             *)
            let sprog = self#get_input0 in
            let tech = Options.get_plugin_opt rt#caches#options "schema.tech" in
            let is_ltl = tech <> Some "cav15" && tech <> Some "cav15-opt" in
            (* keep self-loops only for liveness properties *)
            let sk =
                Summary.summarize_optimize_fuse rt sprog ~keep_selfloops:is_ltl
            in
            m_skel <- Some sk;
            sprog

        method update_runtime rt =
            ()

    end

