open OUnit
open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open SymbSkel


let prepare () =
    let opts = Options.empty in
    let caches = new Infra.pass_caches opts (new Infra.analysis_cache) in
    let tt = new data_type_tab in
    let pc = new_var "pc" in
    tt#set_type pc (mk_int_range 0 3);
    let x, y, n, t = new_var "x", new_var "y", new_var "n", new_var "t" in
    let a, b = new_var "a", new_var "b" in
    n#set_symbolic; t#set_symbolic;
    List.iter
        (fun v -> tt#set_type v (new data_type SpinTypes.TUNSIGNED))
        [x; y; n; t];
    let add_loc map i =
        let loc = new_var (sprintf "loc%d" i) in
        IntMap.add i loc map
    in
    let locFoo_map = List.fold_left add_loc IntMap.empty (range 0 3) in
    tt, locFoo_map, pc, x, y, n, t, a, b


let mk_foo params =
    let tt, locFoo_map, pc, x, y, n, t, a, b = params in
    let mk_eq loc_map loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    {
        Sk.name = "foo";
        Sk.nlocs = 3; Sk.locs = [ [0]; [1]; [2] ];
        Sk.locals = [ pc ];
        Sk.shared = [ x; y ];
        Sk.params = [ n; t ];
        Sk.unknowns = [ a; b ];
        Sk.nrules = 0;
        Sk.rules = [];
        Sk.inits = [
            BinEx (EQ, Var x, IntConst 0);
            mk_eq locFoo_map 0 (BinEx (MINUS, Var n, Var t));
            mk_eq locFoo_map 1 (IntConst 0);
        ];
        Sk.loc_vars = locFoo_map;
        Sk.assumes = [];
        Sk.forms = StrMap.singleton "safety"
            (UnEx (ALWAYS, mk_eq locFoo_map 1 (IntConst 0)))
    }


let test_next_unknowns_vec _ =
    let tt, locFoo_map, pc, x, y, n, t, a, b = prepare () in
    let sk = mk_foo (tt, locFoo_map, pc, x, y, n, t, a, b) in
    let init_vec = TaSynt.init_unknowns_vec sk in
    (* check the specs *)
    assert_equal ("a", IntConst 0) (List.nth init_vec 0);
    assert_equal ("b", IntConst 0) (List.nth init_vec 1);
    ()


let suite = "taSynt-suite" >:::
    [
        "test_next_unknowns_vec" >:: test_next_unknowns_vec;
    ]

