open Printf;;

open Parse;;
open Abstract;;
open Writer;;
open Debug;;

let _ =
    try
        current_verbosity_level := INFO;

        let filename, basename, dirname =
            if Array.length Sys.argv > 1
            then Sys.argv.(1), Filename.basename Sys.argv.(1),
                 Filename.dirname Sys.argv.(1)
            else raise (Failure "Use: program filename")
        in
        log INFO (sprintf "> Parsing %s..." basename);
        let units = parse_promela filename basename dirname
        in
        log DEBUG (sprintf "#units: %d" (List.length units));
        let new_units = do_abstraction units in
        let fo = open_out "abs1.prm" in
        List.iter (write_unit fo 0) new_units;
        close_out fo
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1

