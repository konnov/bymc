open Printf

let load_plugin_mathsat4ml plugin_dir =
    try
        if !Msat.is_loaded
        then raise (Failure "mathsat4ml is already loaded");

        printf "# loading mathsat4ml plugin...\n"; flush stdout;
        Dynlink.loadfile (plugin_dir ^ "/mathsat4ml.cmxs");
        printf "# success\n";

        if not !Msat.is_loaded
        then raise (Failure "failed to load mathsat4ml")
    with Dynlink.Error e ->
        printf "error: %s\n" (Dynlink.error_message e);
        printf "Did you compile mathsat4ml in plugins?\n";
        raise (Failure "Failed to load mathsat4ml")

