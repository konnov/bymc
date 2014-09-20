open Printf

open Accums
open Debug
open Options
open Parse
open Plugin
open Program
open SkelStruc
open Spin
open Writer

class pp_plugin_t (plugin_name: string) =
    object(self)
        inherit transform_plugin_t plugin_name

        val mutable m_plugin_opts = StrMap.empty

        method transform rt =
            let opts = rt#caches#options in
            let filename, basename, dirname =
                if opts.filename <> ""
                then opts.filename,
                    Filename.basename opts.filename,
                    Filename.dirname opts.filename
                else raise (Failure ("File not found: " ^ opts.filename))
            in
            log INFO (sprintf "> Parsing %s..." basename);
            let prog, pragmas = parse_promela opts filename basename dirname in
            m_plugin_opts <- self#find_options rt pragmas;
            self#check_version;
            let new_plugin_opts =
                StrMap.fold StrMap.add
                    rt#caches#options.plugin_opts m_plugin_opts
            in
            rt#caches#set_options
                { rt#caches#options with plugin_opts = new_plugin_opts };

            write_to_file false "original.prm"
                (units_of_program prog) (get_type_tab prog)
                (Hashtbl.create 10);
            log INFO "  [DONE]";
            log DEBUG (sprintf "#units: %d" (List.length (units_of_program prog)));
            log DEBUG (sprintf "#vars: %d" (get_type_tab prog)#length);
            prog

        method update_runtime rt =
            let prog = self#get_output in
            let new_plugin_opts =
                StrMap.fold StrMap.add
                    rt#caches#options.plugin_opts m_plugin_opts
            in
            rt#caches#set_options
                { rt#caches#options with plugin_opts = new_plugin_opts };
            let append_var v = rt#solver#append_var_def v (get_type prog v) in
            List.iter append_var (get_params prog);
            let append_expr e = ignore (rt#solver#append_expr e) in
            List.iter append_expr (get_assumes prog);
            if not rt#solver#check
            then raise (Program.Program_error "Basic assertions are contradictory");
            (* update regions *)
            rt#caches#set_struc prog (compute_struc prog);

        method decode_trail _ path = path

        method refine _ path = (false, self#get_output)

        method find_options rt pragmas =
            let add_opt s (n, t) =
                if n = "option"
                then let key, value = parse_plugin_opt t in
                    StrMap.add key value s
                else s
            in
            List.fold_left add_opt StrMap.empty pragmas

        method check_version =
            try
                let req_s = StrMap.find "bymc.version" m_plugin_opts in
                let components = Str.split (Str.regexp_string ".") req_s in
                let req = List.map int_of_string components in
                let ver_s =
                    str_join "." (List.map string_of_int Options.version) in
                if req > Options.version
                then raise (Program.Program_error
                    (sprintf "This is version %s, but at least %s is required"
                        ver_s req_s))
            with Not_found ->
                ()

    end

