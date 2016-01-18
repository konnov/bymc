(*
 * Transforming process skeletons into the FAST format.
 *
 * see http://tapas.labri.fr/trac/wiki/FASTer
 *
 * Igor Konnov, 2014
 *)

open Printf

open Accums
open Debug
open Plugin

class fast_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        method transform rt =
            let prog = self#get_input0 in
            let sk = Summary.summarize_optimize_fuse rt prog
                    ~keep_selfloops:false in
            FastWriter.write_to_file "model.fst" rt prog [sk];
            prog

        method update_runtime rt =
            ()
    end

