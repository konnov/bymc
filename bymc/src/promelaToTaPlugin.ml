
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

        method transform rt =
            (* Since the current definition of analysis_plugin_t requires
               us to transform a Program to a Program, we cannot return a
               threshold automaton directly. Instead of that, we keep it as
               an attribute that can be accessed with a method.
             *)
            self#get_input0

        method update_runtime rt =
            ()

    end

