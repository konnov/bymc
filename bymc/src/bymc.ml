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


let main () =
    try
        let opts = parse_options in
        current_verbosity_level := if opts.verbose then DEBUG else INFO;
        let caches =
            new pass_caches opts (new analysis_cache) (new proc_struc_cache) in
        let solver = new Smt.yices_smt in
        solver#start;
        let rt = new Runtime.runtime_t solver caches
        in
        match opts.action with
        | OptAbstract ->
            let _ = do_abstraction rt in
            let _ = solver#stop in ()
        | OptRefine -> ()
            (*
            let _ = do_refinement caches solver opts.trail_name prog in
            let _ = solver#stop in ()
            *)
        | OptSubstitute -> ()
                (*
            let units = units_of_program prog in
            let new_units = do_substitution opts.param_assignments units in
            write_to_file "concrete.prm" new_units (get_type_tab prog);
            *)
        | _ -> printf "No options given. Bye.\n"
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1


let _ =
    let print_trace () =
        fprintf stderr " -----------------------------------------------\n";
        Printexc.print_backtrace stderr;
        fprintf stderr " -----------------------------------------------\n"
    in
    (* pay the price of easier debugging *)
    Printexc.record_backtrace true;
    try
        main ()
    with e ->
        if Printexc.backtrace_status ()
        then begin
            fprintf stdout "\nException: %s\n\n" (Printexc.to_string e);
            print_trace ()
        end else begin
            fprintf stdout "\nException: %s\n\n" (Printexc.to_string e);
            fprintf stdout "(Trace is not available. Compile with -g?\n"
        end
