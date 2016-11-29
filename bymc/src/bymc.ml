open Batteries

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

    | _ ->
        ()


let run_solver opts =
    let mk_solver =
        match opts.smt with
        | SmtYices ->
                new Smt.yices_smt "main" "yices"

        | SmtLib2 args ->
                let prog = args.(0) in
                let args = Array.sub args 1 ((Array.length args) - 1) in
                new Smt.lib2_smt "main" prog args

        | SmtMathsat5 ->
                MsatLoader.load_plugin_mathsat4ml opts.Options.plugin_dir;
                new Smt.mathsat5_smt "main"
    in
    let solver = mk_solver in
    if Some "1" = (Options.get_plugin_opt opts "smt.log")
    then solver#set_enable_log true;
    if Some "1" = (Options.get_plugin_opt opts "smt.lockstep")
    then solver#set_enable_lockstep true;
    if Some "1" = (Options.get_plugin_opt opts "smt.unsat.cores")
    then solver#set_need_unsat_cores true;
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
                let chain = ChainFactory.create_chain opts.input opts.chain in
                ignore (do_verification rt chain)

            | OptRefine ->
                do_refine rt

            | OptAbstractRefineLight ->
                let chain = ChainFactory.create_chain opts.input opts.chain in
                ignore (abstract_verify_refine_light rt chain);
                chain#dispose rt;

            | _ ->
                printf "No options given. Bye.\n"
        end;
        let _ = solver#stop in
        log INFO "Bye!"
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1


let _ =
    (* pay the price of easier debugging *)
    Printexc.record_backtrace true;
    let quit _ =
        fprintf stderr "Stack trace:\n";
        flush stderr;
        raise Break
    in
    (* use the following command to break out of the program with a stack trace:
       kill -SIGUSR1 pid *) 
    ignore (Sys.set_signal Sys.sigusr1 (Signal_handle quit));
    ignore (Unix.sigprocmask Unix.SIG_UNBLOCK [sigint]);
    Debug.wrap_with_stack_trace_on_exception main

