open Printf

open Debug
open Options
open Parse
open Plugin
open Program
open Spin
open Writer

class promela_parser_plugin_t (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        method transform rt _ =
            let opts = rt#caches#options in
            let filename, basename, dirname =
                if opts.filename <> ""
                then opts.filename,
                    Filename.basename opts.filename,
                    Filename.dirname opts.filename
                else raise (Failure ("File not found: " ^ opts.filename))
            in
            log INFO (sprintf "> Parsing %s..." basename);
            let prog = parse_promela filename basename dirname in
            write_to_file false "original.prm"
                (units_of_program prog) (get_type_tab prog);
            log INFO "  [DONE]";
            log DEBUG (sprintf "#units: %d" (List.length (units_of_program prog)));
            log DEBUG (sprintf "#vars: %d" (get_type_tab prog)#length);
            prog

        method update_runtime rt =
            let prog = self#get_output in
            let smt_of_asrt e =
                sprintf "(assert %s)" (Smt.expr_to_smt e) in
            let var_to_smt v =
                let tp = get_type prog v in
                Smt.var_to_smt v tp in
            let smt_exprs =
                List.append
                    (List.map var_to_smt (get_params prog))
                    (List.map smt_of_asrt (get_assumes prog))
            in
            List.iter rt#solver#append smt_exprs;
            if not rt#solver#check
            then raise (Program.Program_error "Basic assertions are contradictory")

        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)
    end

