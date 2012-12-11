open Printf;;
open Str;;
open Map
module StringMap = Map.Make(String)

open Parse;;
open Program;;
open Abstract;;
open Instantiation;;
open Writer;;
open Debug;;

type action_option = OptAbstract | OptRefine | OptCheckInv | OptSubstitute | OptNone

type options =
    {
        action: action_option; trail_name: string; filename: string;
        inv_name: string; param_assignments: int StringMap.t;
        verbose: bool
    }

let parse_key_values str =
    let parse_pair map s =
        if string_match (regexp "\\([a-zA-Z0-9]+\\)=\\([0-9]+\\)") s 0
        then StringMap.add (matched_group 1 s) (int_of_string (matched_group 2 s)) map
        else raise (Arg.Bad ("Wrong key=value pair: " ^ s))
    in
    let pairs = split (regexp ",") str in
    List.fold_left parse_pair StringMap.empty pairs
;;

let parse_options =
    let opts = ref {
        action = OptNone; trail_name = ""; filename = ""; inv_name = "";
        param_assignments = StringMap.empty;
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
            ("-s", Arg.String (fun s ->
                opts := {!opts with action = OptSubstitute;
                    param_assignments = parse_key_values s}),
             "Substitute parameters into the code and produce standard Promela.");
            ("-v", Arg.Unit (fun () -> opts := {!opts with verbose = true}),
             "Produce lots of verbose output (you are warned).");
        ]
        (fun s -> if !opts.filename = "" then opts := {!opts with filename = s})
        "Use: run [-a] [-i invariant] [-c spin_sim_out] [-e x=num,y=num] promela_file");

    !opts
;;

let write_to_file name units type_tab =
    let fo = open_out name in
    List.iter (write_unit type_tab fo 0) units;
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
        let prog = parse_promela filename basename dirname in
        write_to_file "original.prm"
            (units_of_program prog) (get_type_tab prog);
        log INFO "  [DONE]";
        log DEBUG (sprintf "#units: %d" (List.length (units_of_program prog)));
        log DEBUG (sprintf "#vars: %d" (get_type_tab prog)#length);
        match opts.action with
        | OptAbstract ->
            let solver = Program.run_smt_solver prog in (* one solver log! *)
            check_all_invariants solver prog;
            let _ = do_abstraction solver true prog in
            let _ = solver#stop in ()
        | OptRefine ->
            let solver = Program.run_smt_solver prog in (* one solver log! *)
            let _ = do_refinement solver opts.trail_name prog in
            let _ = solver#stop in ()
        | OptCheckInv -> ()
        | OptSubstitute ->
            let units = units_of_program prog in
            let new_units = do_substitution opts.param_assignments units in
            write_to_file "concrete.prm" new_units (get_type_tab prog);
        | _ -> printf "No options given. Bye.\n"
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1

