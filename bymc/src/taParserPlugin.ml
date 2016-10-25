open Printf

open Accums
open Debug
open Options
open Parse
open Plugin
open Program
open SkelStruc
open Spin
open SymbSkel
open Writer

(**
  This plugin invokes a parser of threshold automata.
 *)
class ta_parser_plugin_t (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name
        inherit TaSource.ta_source_t

        val mutable m_skel: Sk.skel_t option = None

        method transform rt =
            let opts = rt#caches#options in
            let filename =
                if opts.filename <> ""
                then opts.filename
                else raise (Failure ("File not found: " ^ opts.filename))
            in
            log INFO (sprintf "> Parsing %s..." filename);
            let sk = self#parse filename in
            m_skel <- Some sk;

            Sk.to_file "original.ta" sk;
            log INFO "  [DONE]";
            log INFO (sprintf "> #locs: %d, nrules: %d, #forms: %d"
                sk.Sk.nlocs sk.Sk.nrules (StrMap.cardinal sk.Sk.forms));
            (* just return the empty program, the TA will be accessed by get_ta *)
            let data_type_tab = new SpinIr.data_type_tab in
            let unsigned = new SpinIr.data_type SpinTypes.TUNSIGNED in
            let set_type v = data_type_tab#set_type v unsigned in
            List.iter set_type sk.Sk.params;
            List.iter set_type sk.Sk.shared;
            Program.set_assumes sk.Sk.assumes
                (Program.set_type_tab data_type_tab
                    (Program.set_params sk.Sk.params
                        (Program.set_shared sk.Sk.shared Program.empty)))


        method parse filename =
            TaIrBridge.skel_of_ta (TaParser.parse_file filename)

        method get_ta =
            match m_skel with
            | Some sk -> sk
            | None ->
                let m =
                    "Plugin promela_to_ta_plugin_t has not been called yet"
                in
                raise (Failure m)


        method update_runtime rt =
            let prog = self#get_output in
            (* introduce the parameters and the basic constraints on them *)
            let append_var v = rt#solver#append_var_def v (get_type prog v) in
            List.iter append_var (get_params prog);
            let append_expr e = ignore (rt#solver#append_expr e) in
            List.iter append_expr (get_assumes prog);
            if not rt#solver#check
            then raise (Program.Program_error "Basic assertions are contradictory")

        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)

    end

