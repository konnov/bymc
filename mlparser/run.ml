open Printf;;

open Parse;;
open Abstract;;
open Writer;;
open Debug;;

let write_to_file name units =
    let fo = open_out name in
    List.iter (write_unit fo 0) units;
    close_out fo
;;

let _ =
    try
        current_verbosity_level := DEBUG (*INFO*);

        let filename, basename, dirname =
            if Array.length Sys.argv > 1
            then Sys.argv.(1), Filename.basename Sys.argv.(1),
                 Filename.dirname Sys.argv.(1)
            else raise (Failure "Use: program filename")
        in
        log INFO (sprintf "> Parsing %s..." basename);
        let units = parse_promela filename basename dirname in
        write_to_file "original.prm" units;
        log DEBUG (sprintf "#units: %d" (List.length units));
        let new_units = do_abstraction units in
        write_to_file "abs-counter.prm" new_units
    with End_of_file ->
        log ERROR "Premature end of file";
        exit 1

