open Printf;;

open Parse;;
open Abstract;;
open Writer;;
open Debug;;

type options =
    {
        abstract: bool; refine: bool; trail_name: string; filename: string;
        verbose: bool
    }

let parse_options =
    let opts = ref {
        abstract = false; refine = false; trail_name = ""; filename = "";
        verbose = false
    } in
    (Arg.parse
        [
            ("-a", Arg.Unit (fun () -> opts := {!opts with abstract = true}),
             "Produce abstraction of a Promela program.");
            ("-c", Arg.String
             (fun s -> opts := {!opts with refine = true; trail_name = s}),
             "Check feasibility of a counterexample produced by spin -t (not a *.trail!).");
            ("-v", Arg.Unit (fun () -> opts := {!opts with verbose = true}),
             "Produce lots of verbose output (you are warned).");
        ]
        (fun s ->
            if !opts.filename = "" then opts := {!opts with filename = s})
        "Use: run [-a] [-c spin_sim_out] promela_file");

    !opts
;;

let write_to_file name units =
    let fo = open_out name in
    List.iter (write_unit fo 0) units;
    close_out fo
;;

let _ =
    try
        current_verbosity_level := INFO (*INFO*);
        let opts = parse_options in
        let filename, basename, dirname =
            if Array.length Sys.argv > 1
            then opts.filename,
                Filename.basename opts.filename, Filename.dirname opts.filename
            else raise (Failure (sprintf "File not found: %s" opts.filename))
        in
        log INFO (sprintf "> Parsing %s..." basename);
        let units = parse_promela filename basename dirname in
        write_to_file "original.prm" units;
        log DEBUG (sprintf "#units: %d" (List.length units));
        if opts.abstract
        then let _ = do_abstraction units in ()
        else if opts.refine
        then let _ = do_refinement opts.trail_name units in ()
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1

