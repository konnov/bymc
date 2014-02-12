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
open PorBounds

class por_bounds_plugin_t (plugin_name: string)
        (sk_plugin: SymbSkelPlugin.symb_skel_plugin_t) =
    object(self)
        inherit analysis_plugin_t plugin_name

        method transform rt prog =
            List.iter
                (fun s -> ignore (PorBounds.compute_diam rt#solver s))
                sk_plugin#skels;
            prog

        method update_runtime rt =
            ()
    end

