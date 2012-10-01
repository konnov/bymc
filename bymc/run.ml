open Printf;;

open Parse;;
open Abstract;;
open Substitution;;
open Writer;;
open Debug;;

type action_option = OptAbstract | OptRefine | OptCheckInv | OptSubstitute | OptNone

type options =
    {
        action: action_option; trail_name: string; filename: string;
        inv_name: string; param_assignments: string;
        verbose: bool
    }

let parse_options =
    let opts = ref {
        action = OptNone; trail_name = ""; filename = ""; inv_name = "";
        param_assignments = "";
        verbose = false
    } in
    (Arg.parse
        [
            ("-a", Arg.Unit (fun () -> opts := {!opts with action = OptAbstract}),
             "Produce abstraction of a Promela program.");
            ("-t", Arg.String
             (fun s -> opts := {!opts with action = OptRefine; trail_name = s}),
             "Check feasibility of a counterexample produced by spin -t (not a *.trail!).");
            ("-i", Arg.String
             (fun s -> opts := {!opts with action = OptCheckInv; inv_name = s}),
             "Check if an atomic proposition is an invariant!.");
            ("-s", Arg.Unit (fun () ->
                opts := {!opts with action = OptSubstitute; param_assignments = ""}),
             "Substitute parameters into the code and produce standard Promela.");
            ("-v", Arg.Unit (fun () -> opts := {!opts with verbose = true}),
             "Produce lots of verbose output (you are warned).");
        ]
        (fun s -> if !opts.filename = "" then opts := {!opts with filename = s})
        "Use: run [-a] [-i invariant] [-c spin_sim_out] [-e x=num,y=num] promela_file");

    !opts
;;

let write_to_file name units =
    let fo = open_out name in
    List.iter (write_unit fo 0) units;
    close_out fo
;;

let _ =
    try
        let opts = parse_options in
        current_verbosity_level := if opts.verbose then DEBUG else INFO;
        let filename, basename, dirname =
            if Array.length Sys.argv > 1
            then opts.filename,
                Filename.basename opts.filename, Filename.dirname opts.filename
            else raise (Failure (sprintf "File not found: %s" opts.filename))
        in
        log INFO (sprintf "> Parsing %s..." basename);
        let units = parse_promela filename basename dirname in
        write_to_file "original.prm" units;
        log INFO "  [DONE]";
        log DEBUG (sprintf "#units: %d" (List.length units));
        match opts.action with
          OptAbstract -> let _ = do_abstraction true units in ()
        | OptRefine -> let _ = do_refinement opts.trail_name units in ()
        | OptCheckInv -> let _ = check_invariant opts.inv_name units in ()
        | OptSubstitute ->
            let new_units = do_substitution opts.param_assignments units in
            write_to_file "concrete.prm" new_units;
        | _ -> printf "No options given. Bye.\n"
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1

