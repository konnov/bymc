open Map
open Printf
open Str
open Sys

open Infra
open Abstract
open Debug
open InstantiationPlugin
open Options
open PromelaParserPlugin
open Plugin
open Program

let version = "ByMC-0.3.0-dev"
let banner =
    sprintf
        "*** This is %s. Homepage: http://forsyte.at/software/bymc ***" version

let main () =
    try
        printf "\n%s\n\n" banner;
        let opts = parse_options in
        Debug.initialize_debug opts;
        let caches = new pass_caches opts (new analysis_cache) in
        let solver = new Smt.yices_smt in
        solver#start;
        let rt = new Runtime.runtime_t solver caches in
        begin
            match opts.action with
            | OptAbstract ->
                let _ = do_abstraction rt in ()
            | OptRefine ->
                new_refine rt
            | OptSubstitute ->
                let chain = new plugin_chain_t in
                chain#add_plugin
                    (new promela_parser_plugin_t "promelaParser");
                chain#add_plugin
                    (new instantiation_plugin_t "inst");
                let _ = chain#transform rt Program.empty in ()

            | _ -> printf "No options given. Bye.\n"
        end;
        let _ = solver#stop in ()
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1


let _ =
    let print_trace _ =
        fprintf stderr " -----------------------------------------------\n";
        Printexc.print_backtrace stderr;
        fprintf stderr " -----------------------------------------------\n";
        flush stderr
    in
    let on_exception e =
        if Printexc.backtrace_status ()
        then begin
            fprintf stdout "\nException: %s\n\n" (Printexc.to_string e);
            print_trace ();
            Pervasives.exit 1
        end else begin
            fprintf stdout "\nException: %s\n\n" (Printexc.to_string e);
            fprintf stdout "(Trace is not available. Compile with -g?\n";
            Pervasives.exit 1
        end
    in
    (* pay the price of easier debugging *)
    Printexc.record_backtrace true;
    let q _ =
        fprintf stderr "Stack trace:\n";
        flush stderr;
        raise Break
    in
    ignore (Sys.set_signal Sys.sigusr1 (Signal_handle q));
    ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [sigint]);
    try main ()
    with e -> on_exception e

