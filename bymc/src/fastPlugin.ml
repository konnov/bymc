(*
 * Computing execution bounds using partial order reduction.
 *
 * Igor Konnov, 2014
 *)

open Printf

open Accums
open Debug
open SymbSkel
open Plugin

class fast_plugin_t (plugin_name: string)
        (sk_plugin: SymbSkelPlugin.symb_skel_plugin_t) =
    object(self)
        inherit analysis_plugin_t plugin_name

        method transform rt =
            let prog = self#get_input0 in
            FastWriter.write_to_file "model.fst" rt prog sk_plugin#skels;
            prog

        method update_runtime rt =
            ()
    end

