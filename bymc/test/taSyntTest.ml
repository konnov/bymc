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
    let pairs_s es =
        let p (n, e) = sprintf "(%s, %s)" n (SpinIrImp.expr_s e) in
        "[" ^ (Accums.str_join ", " (List.map p es)) ^ "]"
    in
    let assert_equal_pairs expected_s actual =
        let actual_s = pairs_s actual in
        assert_equal actual_s expected_s
            ~msg:(sprintf "expected %s, found %s" expected_s actual_s)
    in
    (* check the initial vector *)
    let iter0 = TaSynt.vec_iter_init sk 2 in
    let vec0 = TaSynt.iter_to_unknowns_vec iter0 in
    assert_equal_pairs "[(a, 0), (b, 0)]" vec0;
    (* the next vectors *)
    let rec check iter exp_list =
        match exp_list with
        | [] -> iter

        | hd :: tl ->
            let next_iter = TaSynt.vec_iter_next iter in
            let next_vec = TaSynt.iter_to_unknowns_vec next_iter in
            assert_equal_pairs hd next_vec;
            check next_iter tl
    in
    let expected_list = [
        "[(a, 1), (b, 0)]"; "[(a, -1), (b, 0)]";
        "[(a, 0), (b, 1)]"; "[(a, 0), (b, -1)]";
        "[(a, 1), (b, 1)]"; "[(a, -1), (b, 1)]";
            "[(a, 1), (b, -1)]"; "[(a, -1), (b, -1)]";
        "[(a, 2), (b, 0)]"; "[(a, -2), (b, 0)]";
        "[(a, 3), (b, 0)]"; "[(a, -3), (b, 0)]";
        "[(a, 2), (b, 1)]"; "[(a, -2), (b, 1)]";
            "[(a, 2), (b, -1)]"; "[(a, -2), (b, -1)]";
        "[(a, 3), (b, 1)]"; "[(a, -3), (b, 1)]";
            "[(a, 3), (b, -1)]"; "[(a, -3), (b, -1)]";
        "[(a, 0), (b, 2)]"; "[(a, 0), (b, -2)]";
        "[(a, 1), (b, 2)]"; "[(a, -1), (b, 2)]";
            "[(a, 1), (b, -2)]"; "[(a, -1), (b, -2)]";
        "[(a, 0), (b, 3)]"; "[(a, 0), (b, -3)]";
        "[(a, 1), (b, 3)]"; "[(a, -1), (b, 3)]";
            "[(a, 1), (b, -3)]"; "[(a, -1), (b, -3)]";
        "[(a, 2), (b, 2)]"; "[(a, -2), (b, 2)]";
            "[(a, 2), (b, -2)]"; "[(a, -2), (b, -2)]";
        "[(a, 3), (b, 2)]"; "[(a, -3), (b, 2)]";
            "[(a, 3), (b, -2)]"; "[(a, -3), (b, -2)]";
        "[(a, 2), (b, 3)]"; "[(a, -2), (b, 3)]";
            "[(a, 2), (b, -3)]"; "[(a, -2), (b, -3)]";
        "[(a, 3), (b, 3)]"; "[(a, -3), (b, 3)]";
            "[(a, 3), (b, -3)]"; "[(a, -3), (b, -3)]";
    ]
    in
    let next_iter = TaSynt.vec_iter_next (check iter0 expected_list) in
    assert_equal true (TaSynt.vec_iter_end next_iter)
        ~msg:"expected the iterator end"


let suite = "taSynt-suite" >:::
    [
        "test_next_unknowns_vec" >:: test_next_unknowns_vec;
    ]

