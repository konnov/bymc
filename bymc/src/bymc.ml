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


let banner =
    sprintf "*** This is %s. Homepage: http://forsyte.at/software/bymc ***"
        version_full

let print_version_if_needed opts =
    match opts.action with
    | OptVersion ->
        printf "%s\n" version_full;
        Pervasives.exit 1
    | _ -> ()


let run_solver opts =
    let mk_solver =
        match opts.smt with
        | SmtYices ->
                new Smt.yices_smt "yices"

        | SmtLib2 args ->
                let prog = args.(0) in
                let args = Array.sub args 1 ((Array.length args) - 1) in
                new Smt.lib2_smt prog args

        | SmtMathsat5 ->
                MsatLoader.load_plugin_mathsat4ml opts.Options.plugin_dir;
                new Smt.mathsat5_smt
    in
    let solver = mk_solver in
    if Some "1" = (Options.get_plugin_opt opts "smt.log")
    then solver#set_enable_log true;
    if Some "1" = (Options.get_plugin_opt opts "smt.lockstep")
    then solver#set_enable_lockstep true;
    solver


let main () =
    let opts = parse_options () in
    print_version_if_needed opts;
    try
        printf "\n%s\n\n" banner;
        Debug.initialize_debug opts;
        let caches = new pass_caches opts (new analysis_cache) in
        let solver = run_solver opts in
        solver#start;
        let rt = new Runtime.runtime_t solver caches in
        begin
            match opts.action with
            | OptAbstract ->
                let chain = ChainFactory.create_chain opts.chain in
                let _ = do_abstraction rt chain in ()

            | OptRefine ->
                do_refine rt

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
    with e ->
        on_exception e

