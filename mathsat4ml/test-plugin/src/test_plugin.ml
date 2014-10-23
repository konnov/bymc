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
            printf "creating one instance...\n"; flush stdout;
            let msat = (!Msat.p_create) () in
            printf "declaring int x, y...\n"; flush stdout;
            (!Msat.p_declare_int) msat "x";
            (!Msat.p_declare_int) msat "y";

            printf "asserting x > y...\n"; flush stdout;
            let res = (!Msat.p_assert) msat "(> x y)" in
            assert (res <> -1);
            printf "solving...\n"; flush stdout;
            let res = (!Msat.p_solve) msat in
            printf "result = %d\n" res; flush stdout;
            assert (res = 1);

            printf "get_model_value('x')\n"; flush stdout;
            let value = (!Msat.p_get_model_value) msat "x" in
            printf "result: %s\n" value; flush stdout;

            printf "get_model_value('y')\n"; flush stdout;
            let value = (!Msat.p_get_model_value) msat "y" in
            printf "result: %s\n" value; flush stdout;

            printf "push\n"; flush stdout;
            (!Msat.p_push) msat;

            printf "asserting x < y...\n"; flush stdout;
            let res = (!Msat.p_assert) msat "(< x y)" in
            printf "solving...\n"; flush stdout;
            let res = (!Msat.p_solve) msat in
            printf "result = %d\n" res; flush stdout;
            assert (res = 0);

            printf "pop\n"; flush stdout;
            (!Msat.p_pop) msat;

            printf "assert('= x 0')...\n"; flush stdout;
            let res = (!Msat.p_assert) msat "(= x 42)" in
            printf "solve...\n"; flush stdout;
            let res = (!Msat.p_solve) msat in
            printf "result = %d\n" res; flush stdout;
            assert (res = 1);

            printf "get_model_value('x')\n"; flush stdout;
            let value = (!Msat.p_get_model_value) msat "x" in
            printf "result: %s\n" value; flush stdout;
            assert (value = "42");

            printf "destroying the instance...\n"; flush stdout;
            ignore ((!Msat.p_destroy) msat);
            printf "done...\n";
            flush stdout;
        with Dynlink.Error e ->
            printf "error: %s\n" (Dynlink.error_message e)
    end

