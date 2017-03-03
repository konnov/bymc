(*
  Simple logging/debugging facility.
  It might be slow and inefficient as hell, but it does its job well:
  Other modules print the important messages; On-demand tracing
  allows me to debug the code much faster than without the module.

  Pass -O trace.mods=mod1,mod2 to enable tracing in a specific module.
  The codes are defined in the module trc.

  Igor Konnov 2012-2013.
 *)

open Printf

open Accums
open Options

type verbosity = QUIET | ERROR | WARN | INFO | DEBUG

let current_verbosity_level = ref INFO (* extremely long on purpose *)
(* when debugging, one can enable tracing of specific modules
  on command line *)
let enabled_trace_modules = Hashtbl.create 1024

let initialize_debug opts =
    if opts.verbose then current_verbosity_level := DEBUG;
    if StringMap.mem "trace.mods" opts.plugin_opts
    then let mods = Str.split (Str.regexp_string ",")
        (StringMap.find "trace.mods" opts.plugin_opts) in
        List.iter (fun m -> Hashtbl.add enabled_trace_modules m 1) mods


let enable_tracing _ mod_name =
    Hashtbl.replace enabled_trace_modules mod_name 1


let disable_tracing _ mod_name =
    while Hashtbl.mem enabled_trace_modules mod_name do
        Hashtbl.remove enabled_trace_modules mod_name
    done


let verbosity_s = function
    | QUIET -> ""
    | ERROR -> "ERR  "
    | WARN -> "WARN: "
    | INFO -> " "
    | DEBUG -> " --- "

let may_log level =
    let to_num = function
        | QUIET -> 0
        | ERROR -> 1
        | WARN -> 2
        | INFO -> 3
        | DEBUG -> 4
    in
    (to_num level) <= (to_num !current_verbosity_level)

let log level message =
    if may_log level
    then begin
      Printf.printf "%s %s\n" (verbosity_s level) message;
      flush stdout;
    end

let logtm level message =
    if may_log level
    then begin
      Printf.printf "%s: %s %s\n"
        (short_time_now ()) (verbosity_s level) message;
      flush stdout;
    end

(*
  Trace output. To enable tracing of FOO and BAR, pass an option:
    -O trace.mods=FOO,BAR.

  When debugging a unit test, add manually calls to enable_tracing
  and disable_tracing (see above).
 *)
let trace (mod_code: string) (text_fun: unit -> string) =
    if Hashtbl.mem enabled_trace_modules mod_code
    then begin
        printf "@%s*%s* %s" (short_time_now ()) mod_code (text_fun ());
        flush stdout
    end

(*
  Trace output using lazy types, which are much nicer than functions.
  To enable tracing of FOO and BAR, pass an option:
    -O trace.mods=FOO,BAR.

  When debugging a unit test, add manually calls to enable_tracing
  and disable_tracing (see above).
 *)
let ltrace (mod_code: string) (text: string lazy_t) =
    if Hashtbl.mem enabled_trace_modules mod_code
    then begin
        printf "@%s*%s* %s" (short_time_now ()) mod_code (Lazy.force text);
        flush stdout
    end


let print_backtrace bt =
    fprintf stderr " -----------------------------------------------\n";
    let print_prev_slot prev cnt =
        if prev <> ""
        then if cnt = 1
            then fprintf stderr "%s\n" prev
            else fprintf stderr "%s\n  (repeats %d times)\n" prev cnt
    in
    let p _ =
        match Printexc.backtrace_slots bt with
        | None -> fprintf stderr "No backtrace information available\n"
        | Some slots ->
            fprintf stderr " (%d slots)\n" (Array.length slots);
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
            let prev, cnt = BatArray.fold_lefti ps ("", 0) slots in
            print_prev_slot prev cnt
    in
    p ();
    fprintf stderr " -----------------------------------------------\n"

(**
  Run the provided function  and print a stack trace on exception.
  Use this function to find the problem cause.
 *)
let wrap_with_stack_trace_on_exception f =
    let on_exception e =
        if Printexc.backtrace_status ()
        then begin
            (* bugfix: save the backtrace immediately, as the later fprintf might damage it *)
            let bt = Printexc.get_raw_backtrace () in
            fprintf stderr "\nException: %s\n\n" (Printexc.to_string e);
            print_backtrace bt
            (*Printexc.print_backtrace stderr*)
        end else begin
            fprintf stderr "\nException: %s\n\n" (Printexc.to_string e);
            fprintf stderr "(Trace is not available. Compile with -g?\n";
            Pervasives.exit 1
        end
    in
    (* pay the price of easier debugging *)
    Printexc.record_backtrace true;
    try f ()
    with e -> on_exception e

