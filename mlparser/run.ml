open Printf;;

open Parse;;

let _ =
    try
        let filename, basename, dirname =
            if Array.length Sys.argv > 1
            then Sys.argv.(1), Filename.basename Sys.argv.(1),
                 Filename.dirname Sys.argv.(1)
            else raise (Failure "Use: program filename")
        in
        let units = parse_promela filename basename dirname
        in
        printf "#units: %d\n" (List.length units)
    with End_of_file ->
        print_string "Premature end of file\n";
        exit 1

