open Printf

let _ =
    let is_required = ref 0 in
    (Arg.parse
        [
            ("--load", Arg.Int (fun i -> is_required := i), "--load <int>")
        ]
        (fun _ -> ())
        "Use: prog --load <int>"
    );
    if !is_required = 0
    then printf "The plugin is not required. Skipped.\n"
    else begin
        try
            printf "is mathsat4ml loaded = %b\n" (!Msat.is_loaded);
            printf "loading mathsat4ml plugin...\n";
            flush stdout;
            Dynlink.loadfile "../plugin/mathsat4ml.cmxs";
            printf "success\n";
            printf "have you seen any message?\n";
            printf "is mathsat4ml loaded = %b\n" (!Msat.is_loaded);
            printf "creating one instance...\n";
            flush stdout;
            let msat = (!Msat.p_create) () in
            printf "destroying the instance...\n";
            flush stdout;
            ignore ((!Msat.p_destroy) msat);
            printf "done...\n";
            flush stdout;
        with Dynlink.Error e ->
            printf "error: %s\n" (Dynlink.error_message e)
    end

