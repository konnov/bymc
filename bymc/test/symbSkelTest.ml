open OUnit
open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open SymbSkel

let ge l r = BinEx (GE, Var l, Var r)

let lt l r = BinEx (LT, Var l, Var r)

let asgn l e = BinEx (EQ, UnEx (NEXT, Var l), e)

let keep x = BinEx (EQ, UnEx (NEXT, Var x), Var x)

let (+) v i = BinEx (PLUS, Var v, IntConst i)

let tru = IntConst 1

let mk_rule src dst guard act = { Sk.src; Sk.dst; Sk.guard; Sk.act }

let str_of_ints is = List.map string_of_int is |> str_join ", "

let str_of_vars vs = List.map (fun v -> v#get_name) vs |> str_join ", "

let str_of_exprs es = List.map (fun e -> expr_s e) es |> str_join ", "


let prepare () =
    let opts = Options.empty in
    let caches = new Infra.pass_caches opts (new Infra.analysis_cache) in
    let tt = new data_type_tab in
    let pc = new_var "pc" in
    tt#set_type pc (mk_int_range 0 3);
    let x, y, n, t = new_var "x", new_var "y", new_var "n", new_var "t" in
    n#set_symbolic; t#set_symbolic;
    List.iter
        (fun v -> tt#set_type v (new data_type SpinTypes.TUNSIGNED))
        [x; y; n; t];
    let add_loc map i =
        let loc = new_var (sprintf "loc%d" i) in
        IntMap.add i loc map
    in
    let locFoo_map = List.fold_left add_loc IntMap.empty (range 0 3) in
    tt, locFoo_map, pc, x, y, n, t


let prepare2 () =
    let opts = Options.empty in
    let caches = new Infra.pass_caches opts (new Infra.analysis_cache) in
    let tt = new data_type_tab in
    let pc1, pc2 = new_var "pc1", new_var "pc2" in
    List.iter (fun v -> tt#set_type v (mk_int_range 0 3)) [pc1; pc2];
    let x, y, n, t = new_var "x", new_var "y", new_var "n", new_var "t" in
    n#set_symbolic; t#set_symbolic;
    List.iter
        (fun v -> tt#set_type v (new data_type SpinTypes.TUNSIGNED))
        [x; y; n; t];
    let add_loc map i =
        let loc = new_var (sprintf "loc%d" i) in
        IntMap.add i loc map
    in
    let locFoo_map = List.fold_left add_loc IntMap.empty (range 0 3) in
    let locBar_map = List.fold_left add_loc IntMap.empty (range 0 3) in
    tt, locFoo_map, locBar_map, pc1, pc2, x, y, n, t


let mk_foo_bar params =
    let tt, locFoo_map, locBar_map, pc1, pc2, x, y, n, t = params in
    let mk_eq loc_map loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    let skFoo = {
        Sk.name = "foo";
        Sk.nlocs = 3; Sk.locs = [ [0]; [1]; [2] ];
        Sk.locals = [ pc1 ]; Sk.shared = [ x; y ]; Sk.params = [ n; t ];
        Sk.nrules = 2;
        Sk.rules = [
            mk_rule 0 1 (lt y t) [ keep x; keep y ];
            mk_rule 1 2 tru [ asgn x (x + 1); keep y ];
        ];
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
    in
    let skBar = {
        Sk.name = "bar";
        Sk.nlocs = 3; Sk.locs = [ [0]; [1]; [2] ];
        Sk.locals = [ pc2 ]; Sk.shared = [ x; y ]; Sk.params = [ n; t ];
        Sk.nrules = 2;
        Sk.rules = [
            mk_rule 0 1 (ge x t) [ keep x; keep y ];
            mk_rule 1 2 tru [ keep x; asgn y (y + 1) ];
        ];
        Sk.inits = [
            mk_eq locBar_map 0 (Var t);
            mk_eq locBar_map 1 (IntConst 0);
            BinEx (EQ, Var x, IntConst 0);
        ];
        Sk.loc_vars = locBar_map;
        Sk.assumes = [];
        Sk.forms = StrMap.singleton "liveness"
            (UnEx (EVENTUALLY, mk_eq locFoo_map 1 (IntConst 0)))
    }
    in
    (skFoo, skBar)


let test_fuse_several _ =
    let params = prepare2 () in
    let skFoo, skBar = mk_foo_bar params in
    let tt, locFoo_map, locBar_map, pc1, pc2, x, y, n, t = params in
    let fused = SymbSkel.fuse [skFoo; skBar] "fusion" in
    assert_equal "fusion" fused.Sk.name
        ~msg:(sprintf "expected 'fusion', found %s" fused.Sk.name);
    assert_equal 6 fused.Sk.nlocs
        ~msg:(sprintf "expected 6 locations, found %d" fused.Sk.nlocs);
    assert_equal 4 fused.Sk.nrules
        ~msg:(sprintf "expected 4 rules, found %d" fused.Sk.nrules);
    assert_equal [x; y] fused.Sk.shared
        ~msg:(sprintf "expected [x; y], found [%s]" (str_of_vars fused.Sk.shared));
    assert_equal [n; t] fused.Sk.params
        ~msg:(sprintf "expected [x; y], found [%s]" (str_of_vars fused.Sk.params));
    assert_equal [pc1; pc2] fused.Sk.locals
        ~msg:(sprintf "expected [x; y], found [%s]" (str_of_vars fused.Sk.locals));
    assert_equal 4 (List.length fused.Sk.rules)
        ~msg:(sprintf "expected 4 rules, found %d" (List.length fused.Sk.rules));
    let r0 = List.nth fused.Sk.rules 0 in
    let r1 = List.nth fused.Sk.rules 1 in
    let r2 = List.nth fused.Sk.rules 2 in
    let r3 = List.nth fused.Sk.rules 3 in
    assert_equal (List.nth skFoo.Sk.rules 0) r0
        ~msg:("expected rule 0, found smth else");
    assert_equal (List.nth skFoo.Sk.rules 1) r1
        ~msg:("expected rule 1, found smth else");
    let assert_rule r src dst orig =
        if r.Sk.src <> src
        then assert_failure (sprintf "expected src=%d" src);
        if r.Sk.dst <> dst
        then assert_failure (sprintf "expected dst=%d" dst);
        assert_equal orig.Sk.guard r.Sk.guard
            ~msg:(sprintf "expected guard %s, found %s"
                (expr_s orig.Sk.guard) (expr_s r.Sk.guard));
        assert_equal orig.Sk.act r.Sk.act
            ~msg:(sprintf "expected act %s, found %s"
                (str_of_exprs orig.Sk.act) (str_of_exprs r.Sk.act));
    in
    assert_rule r0 0 1 (List.nth skFoo.Sk.rules 0);
    assert_rule r1 1 2 (List.nth skFoo.Sk.rules 1);
    assert_rule r2 3 4 (List.nth skBar.Sk.rules 0);
    assert_rule r3 4 5 (List.nth skBar.Sk.rules 1);

    assert_equal 6 (List.length fused.Sk.locs)
        ~msg:(sprintf "expected 6 rules, found %d" (List.length fused.Sk.locs));

    let assert_loc exp_loc loc =
        assert_equal exp_loc loc
            ~msg:(sprintf "expected loc %s, found loc %s"
                (Sk.locname exp_loc) (Sk.locname loc))
    in
    assert_equal "loc0_X" (Sk.locname (List.nth fused.Sk.locs 0))
        ~msg:"expected loc0_X";
    assert_loc [0; -1] (List.nth fused.Sk.locs 0);
    assert_loc [1; -1] (List.nth fused.Sk.locs 1);
    assert_loc [2; -1] (List.nth fused.Sk.locs 2);
    assert_loc [-1; 0] (List.nth fused.Sk.locs 3);
    assert_loc [-1; 1] (List.nth fused.Sk.locs 4);
    assert_loc [-1; 2] (List.nth fused.Sk.locs 5);
    assert_equal "locX_2" (Sk.locname (List.nth fused.Sk.locs 5))
        ~msg:"expected locX_2";

    assert_equal 5 (List.length fused.Sk.inits)
        ~msg:(sprintf "expected 5 rules, found %d" (List.length fused.Sk.inits));

    let assert_loc name i =
        let loc = IntMap.find i fused.Sk.loc_vars in
        assert_equal name loc#get_name
            ~msg:(sprintf "expected %s, found %s" name loc#get_name)
    in
    assert_loc "loc0_X" 0;
    assert_loc "loc1_X" 1;
    assert_loc "loc2_X" 2;
    assert_loc "locX_0" 3;
    assert_loc "locX_1" 4;
    assert_loc "locX_2" 5;

    let assert_init exp_s i =
        let exp = List.nth fused.Sk.inits i in
        assert_equal exp_s (expr_s exp)
            ~msg:(sprintf "expected %s, found %s" exp_s (expr_s exp))
    in
    assert_init "(x == 0)" 0;
    assert_init "(loc0_X == (n - t))" 1;
    assert_init "(loc1_X == 0)" 2;
    assert_init "(locX_0 == t)" 3;
    assert_init "(locX_1 == 0)" 4;
    (* check the specs *)
    assert_equal 2 (StrMap.cardinal fused.Sk.forms)
        ~msg:(sprintf "expected two LTL formulas, found %d"
            (StrMap.cardinal fused.Sk.forms))


let test_fuse_several_same_forms _ =
    let params = prepare2 () in
    let skFoo, _ = mk_foo_bar params in
    try
        ignore (SymbSkel.fuse [skFoo; skFoo] "fusion");
        assert_failure "expected a failure"
    with Failure _ ->
        () (* ok *)


let test_optimize_guards _ =
    let tt, locFoo_map, pc, x, y, n, t = prepare () in
    let mk_eq loc_map loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    let interval v a b =
        BinEx (AND, BinEx (GE, Var v, a), BinEx (LT, Var v, b))
    in
    let g1 = list_to_binex OR [
        interval x (IntConst 1) (Var t);
        interval x (Var t) (BinEx (MULT, IntConst 2, Var t));
        interval x (BinEx (MULT, IntConst 2, Var t)) (BinEx (MINUS, Var n, Var t));
    ] in
    let g2 = list_to_binex OR [
        interval y (IntConst 1) (Var t);
        interval y (Var t) (BinEx (MULT, IntConst 3, Var t));
        interval y (BinEx (MULT, IntConst 3, Var t)) (Var n);
    ] in
    let g3 = BinEx (OR, g1, g2) in
    let skFoo = {
        Sk.name = "foo";
        Sk.nlocs = 3; Sk.locs = [ [0]; [1]; [2] ];
        Sk.locals = [ pc ]; Sk.shared = [ x; y ]; Sk.params = [ n; t ];
        Sk.nrules = 2;
        Sk.rules = [
            mk_rule 0 1 g1 [ keep x; keep y ];
            mk_rule 1 2 g3 [ asgn x (x + 1); keep y ];
        ];
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
    in
    let sk = SymbSkel.optimize_guards skFoo in
    let r0 = List.nth sk.Sk.rules 0 in
    let r1 = List.nth sk.Sk.rules 1 in
    let exp0 = (interval x (IntConst 1) (BinEx (MINUS, Var n, Var t))) in
    assert_equal exp0 r0.Sk.guard
        ~msg:(sprintf "expected optimized guard %s, found %s"
            (expr_s exp0) (expr_s r0.Sk.guard));
    let y_or_x =
        BinEx (OR,
            (interval y (IntConst 1) (Var n)),
            (interval x (IntConst 1) (BinEx (MINUS, Var n, Var t)))
        )
    and x_or_y =
        BinEx (OR,
            (interval x (IntConst 1) (BinEx (MINUS, Var n, Var t))),
            (interval y (IntConst 1) (Var n))
        )
    in
    assert_bool 
        (sprintf "found %s, expected one of %s and %s"
                (expr_s r1.Sk.guard) (expr_s x_or_y) (expr_s y_or_x))
        (x_or_y = r1.Sk.guard || y_or_x = r1.Sk.guard);
    (* check the specs *)
    assert_equal 1 (StrMap.cardinal sk.Sk.forms)
        ~msg:(sprintf "expected one LTL formula, found %d"
            (StrMap.cardinal sk.Sk.forms))


let suite = "symbSkel-suite" >:::
    [
        "test_fuse_several" >:: test_fuse_several;
        "test_fuse_several_same_forms" >:: test_fuse_several_same_forms;
        "test_optimize_guards" >:: test_optimize_guards;
    ]

