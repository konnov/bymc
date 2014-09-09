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

(* Trace output. To enable tracing of FOO and BAR, pass an option:
    -O trace.mods=FOO,BAR *)
let trace (mod_code: string) (text_fun: unit -> string) =
    if Hashtbl.mem enabled_trace_modules mod_code
    then begin
        printf "@%s*%s* %s" (short_time_now ()) mod_code (text_fun ());
        flush stdout
    end

