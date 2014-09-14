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
        
        val mutable m_paths: PorBounds.path_t list = []

        method transform rt =
            let dom = rt#caches#analysis#get_pia_dom in
            let dom_size = dom#length in
            (* TODO: construct the paths for several process types properly *)
            m_paths <- List.fold_left
                (fun l s -> l @ (PorBounds.compute_diam rt#solver dom_size s))
                [] sk_plugin#skels;
            self#get_input0

        method update_runtime rt =
            ()

        method representative_paths = m_paths
    end

