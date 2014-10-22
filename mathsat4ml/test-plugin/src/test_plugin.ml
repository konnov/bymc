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
            printf "foo_int = %d\n" (!Foo.foo_int);
            printf "loading the plugin...\n";
            flush stdout;
            Dynlink.loadfile "../plugin/mathsat4ml.cmxs";
            printf "loaded\n";
            printf "have you seen any message?\n";
            printf "foo_int = %d\n" (!Foo.foo_int);
            printf "calling start...\n";
            flush stdout;
            ignore ((!Foo.p_start) ());
            printf "calling stop...\n";
            flush stdout;
            ignore ((!Foo.p_stop) ());
            printf "done...\n";
            flush stdout;
        with Dynlink.Error e ->
            printf "error: %s\n" (Dynlink.error_message e)
    end

