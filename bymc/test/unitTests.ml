open OUnit

let _ =
    let all = "all-tests" >:::
    [
        PipeCmdTest.suite;
        AccumsTest.suite;
        SsaTest.suite;
        AbsCounterTest.suite;
    ]
    in
    run_test_tt_main all

