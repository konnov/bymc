open OUnit

let _ =
    let all = "all-tests" >:::
    [
        TaSyntTest.suite;
        PipeCmdTest.suite;
        SmtTest.suite;
        AccumsTest.suite;
        SsaTest.suite;
        AbsCounterTest.suite;
        PiaCtrRefinementTest.suite;
        SymbSkelTest.suite;
        SummaryTest.suite;
        PorBoundsTest.suite;
        PosetTest.suite;
        SchemaCheckerLtlTest.suite;
        TaIrBridgeTest.suite;
        TaParserTest.suite;
    ]
    in
    run_test_tt_main all

