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
    | _ -> ()


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
                let _ = do_abstraction rt chain in ()

            | OptRefine ->
                do_refine rt

            | _ -> printf "No options given. Bye.\n"
        end;
        let _ = solver#stop in ()
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1


let print_backtrace _ =
    fprintf stderr " -----------------------------------------------\n";
    Printexc.print_backtrace stderr;
(*
    The following code is now but incompatible with the outdated installation
    at our benchmarking server. Uncomment as soon as the benchmarking server
    is up-to-date.
    let print_prev_slot prev cnt =
        if prev <> ""
        then if cnt = 1
            then fprintf stderr "%s\n" prev
            else fprintf stderr "%s\n  (repeats %d times)\n" prev cnt
    in
    let bt = Printexc.get_raw_backtrace () in

    let p _ =
        match Printexc.backtrace_slots bt with
        | None -> fprintf stderr "No backtrace information available\n"
        | Some slots ->
            let ps (prev, cnt) i slot =
                match Printexc.Slot.format i slot with
                | Some s ->
                    if s <> prev
                    then begin
                        print_prev_slot prev cnt;
                        (s, 1)          (* a new line *)
                    end else
                        (prev, 1 + cnt) (* one more occurence of the same line *)

                | None -> (prev, cnt)
            in
            let prev, cnt = Array.fold_lefti ps ("", 0) slots in
            print_prev_slot prev cnt
    in
    p ();
*)
    fprintf stderr " -----------------------------------------------\n"

        

let _ =
    let on_exception e =
        if Printexc.backtrace_status ()
        then begin
            fprintf stdout "\nException: %s\n\n" (Printexc.to_string e);
            print_backtrace ();
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

