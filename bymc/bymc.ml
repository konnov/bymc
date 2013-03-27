open Printf
open Str
open Map

open Infra
open Options
open Parse
open Program

open Abstract
open Instantiation
open Writer
open Debug


let write_to_file name units type_tab =
    let fo = open_out name in
    List.iter (write_unit type_tab fo 0) units;
    close_out fo


let main () =
    try
        let opts = parse_options in
        current_verbosity_level := if opts.verbose then DEBUG else INFO;
        let caches =
            new pass_caches opts (new analysis_cache) (new proc_struc_cache) in
        let filename, basename, dirname =
            if Array.length Sys.argv > 1
            then opts.filename,
                Filename.basename opts.filename, Filename.dirname opts.filename
            else raise (Failure (sprintf "File not found: %s" opts.filename))
        in
        log INFO (sprintf "> Parsing %s..." basename);
        let prog = parse_promela filename basename dirname in
        write_to_file "original.prm"
            (units_of_program prog) (get_type_tab prog);
        log INFO "  [DONE]";
        log DEBUG (sprintf "#units: %d" (List.length (units_of_program prog)));
        log DEBUG (sprintf "#vars: %d" (get_type_tab prog)#length);
        match opts.action with
        | OptAbstract ->
            let solver = Program.run_smt_solver prog in (* one solver log! *)
            check_all_invariants caches solver prog;
            let _ = do_abstraction caches solver true prog in
            let _ = solver#stop in ()
        | OptRefine ->
            let solver = Program.run_smt_solver prog in (* one solver log! *)
            let _ = do_refinement caches solver opts.trail_name prog in
            let _ = solver#stop in ()
        | OptCheckInv ->
            printf "WARNING: -i is deprecated, invariants are checked automatically\n"
        | OptSubstitute ->
            let units = units_of_program prog in
            let new_units = do_substitution opts.param_assignments units in
            write_to_file "concrete.prm" new_units (get_type_tab prog);
        | _ -> printf "No options given. Bye.\n"
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1


let _ =
    try
        (* pay the price of easier debugging *)
        Printexc.record_backtrace true;
        main ()
    with e ->
        if Printexc.backtrace_status ()
        then begin
            fprintf stdout "\nException: %s\n\n" (Printexc.to_string e);
            Printexc.print_backtrace stdout
        end else begin
            fprintf stdout "\nException: %s\n\n" (Printexc.to_string e);
            fprintf stdout "(Trace is not available. Compile with -g?\n"
        end
