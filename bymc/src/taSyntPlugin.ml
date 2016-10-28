open Printf

open Accums
open Debug
open Options
open Plugin
open Program
open Spin
open SymbSkel

open TaSynt

(**
  Synthesizing threshold automata using CEGYS.

  @author Igor Konnov, 2016
 *)
class ta_synt_plugin_t (plugin_name: string) (ta_source: TaSource.ta_source_t) =
    object(self)
        inherit transform_plugin_t plugin_name
        inherit TaSource.ta_source_t

        val mutable m_out_skel: Sk.skel_t option = None

        method transform rt =
            let in_skel = ta_source#get_ta in
            let iter = vec_iter_init in_skel 4 in
            let vec = iter_to_unknowns_vec iter in
            log INFO
                ("> Replacing the unknowns: " ^ (unknowns_vec_s vec));
            let out_skel = replace_unknowns in_skel vec in
            m_out_skel <- Some out_skel;
            Sk.to_file "synt.ta" out_skel;
            self#get_input0


        method get_ta =
            match m_out_skel with
            | Some sk -> sk
            | None ->
                let m =
                    "Plugin ta_synt_plugin_t has not been called yet"
                in
                raise (Failure m)


        method update_runtime rt =
            ()

        method decode_trail _ path =
            path

        method refine _ path =
            (false, self#get_output)

    end

