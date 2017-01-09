open OUnit
open Printf

open Accums
open Spin
open SpinIr
open SpinIrImp
open SymbSkel
open SchemaSmt

module PB = PorBounds


let prepare () =
    let opts = Options.empty in
    let caches = new Infra.pass_caches opts (new Infra.analysis_cache) in
    let tt = new data_type_tab in
    let pc = new_var "pc" in
    tt#set_type pc (mk_int_range 0 3);
    let x, n, t = new_var "x", new_var "n", new_var "t" in
    let a, b = new_var "a", new_var "b" in
    n#set_symbolic; t#set_symbolic;
    List.iter
        (fun v -> tt#set_type v (new data_type SpinTypes.TUNSIGNED))
        [x; n; t];
    let add_loc map i =
        let loc = new_var (sprintf "loc%d" i) in
        IntMap.add i loc map
    in
    let locFoo_map = List.fold_left add_loc IntMap.empty (range 0 3) in
    tt, locFoo_map, pc, x, n, t, a, b


let mk_foo params =
    (* loc_0 --- x >= an ---> loc_1 --- x >= bt ---> loc_ 2 *)
    let tt, locFoo_map, pc, x, n, t, a, b = params in
    let mk_eq loc_map loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    {
        Sk.name = "foo";
        Sk.nlocs = 3; Sk.locs = [ [0]; [1]; [2] ];
        Sk.locals = [ pc ];
        Sk.shared = [ x ];
        Sk.params = [ n; t ];
        Sk.unknowns = [ a; b ];
        Sk.nrules = 0;
        Sk.rules = [
            {
                Sk.src = 0; Sk.dst = 1;
                Sk.guard = BinEx (GE, Var x, BinEx (MULT, Var a, Var n));
                Sk.act = [(BinEx (EQ, UnEx (NEXT, Var x),
                                     BinEx (PLUS, Var x, IntConst 1)))]
            };
            {
                Sk.src = 1; Sk.dst = 2;
                Sk.guard = BinEx (GE, Var x, BinEx (MULT, Var b, Var t));
                Sk.act = [(BinEx (EQ, UnEx (NEXT, Var x), Var x))]
            };
        ];
        Sk.inits = [
            BinEx (EQ, Var x, IntConst 0);
            mk_eq locFoo_map 0 (BinEx (MINUS, Var n, Var t));
            mk_eq locFoo_map 1 (IntConst 0);
            mk_eq locFoo_map 2 (IntConst 0);
        ];
        Sk.loc_vars = locFoo_map;
        Sk.assumes = [];
        Sk.forms = StrMap.singleton "safety"
            (UnEx (ALWAYS, mk_eq locFoo_map 2 (IntConst 0)))
    }


let test_next_unknowns_vec _ =
    let tt, locFoo_map, pc, x, n, t, a, b = prepare () in
    let sk = mk_foo (tt, locFoo_map, pc, x, n, t, a, b) in
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


let test_is_cex_applicable _ =
    let tt, locFoo_map, pc, x, n, t, a, b = prepare () in
    let sk = mk_foo (tt, locFoo_map, pc, x, n, t, a, b) in
    let unknowns_vec = [("a", IntConst 2); ("b", IntConst 1)] in
    let fixed_skel = TaSynt.replace_unknowns_in_skel sk unknowns_vec in
    let cex0 = {
        C.f_form_name = "unforg";
        C.f_loop_index = 1;
        C.f_init_state =
            Accums.str_map_of_pair_list StrMap.empty [
                ("n", 2); ("t", 2); ("x", 2);
                ("loc_0", 2);  ("loc_1", 0); ("loc_2", 0);
            ];
        C.f_moves = [
            { C.f_rule_no = 0; C.f_accel = 1 };
            { C.f_rule_no = 1; C.f_accel = 1 };
        ];
        C.f_iorder = [0; 1];
        C.f_po_struc = [C.PO_init_struc; C.PO_tl_struc];
    }
    in
    assert_equal false (TaSynt.is_cex_applicable fixed_skel cex0)
        ~msg:"expected the counterexample 0 to be inapplicable";
    let cex1 = {
        C.f_form_name = "unforg";
        C.f_loop_index = 1;
        C.f_init_state =
            Accums.str_map_of_pair_list StrMap.empty [
                ("n", 2); ("t", 1); ("x", 2);
                ("loc_0", 2);  ("loc_1", 0); ("loc_2", 0);
            ];
        C.f_moves = [
            { C.f_rule_no = 1; C.f_accel = 1 };
        ];
        C.f_iorder = [0; 1];
        C.f_po_struc = [C.PO_init_struc; C.PO_tl_struc];
    }
    in
    assert_equal true (TaSynt.is_cex_applicable fixed_skel cex1)
        ~msg:"expected the counterexample 1 to be applicable";
    let cex2 = {
        C.f_form_name = "unforg";
        C.f_loop_index = 1;
        C.f_init_state =
            Accums.str_map_of_pair_list StrMap.empty [
                ("n", 1); ("t", 3); ("x", 2);
                ("loc_0", 2);  ("loc_1", 0); ("loc_2", 0);
            ];
        C.f_moves = [
            { C.f_rule_no = 0; C.f_accel = 1 };
            { C.f_rule_no = 1; C.f_accel = 1 };
        ];
        C.f_iorder = [0; 1];
        C.f_po_struc = [C.PO_init_struc; C.PO_tl_struc];
    }
    in
    assert_equal true (TaSynt.is_cex_applicable fixed_skel cex2)
        ~msg:"expected the counterexample 2 to be applicable";
    (* this is a counterexample that should not be applicable,
       but it was found to be (spuriously) applicable *)
    let cex3 = {
        C.f_form_name = "unforg";
        C.f_loop_index = 1;
        C.f_init_state =
            Accums.str_map_of_pair_list StrMap.empty [
                ("n", 2); ("t", 3); ("x", 2);
                ("loc_0", 2);  ("loc_1", 0); ("loc_2", 0);
            ];
        C.f_moves = [
            { C.f_rule_no = 0; C.f_accel = 1 };
            { C.f_rule_no = 1; C.f_accel = 1 };
        ];
        C.f_iorder = [0; 1];
        C.f_po_struc = [C.PO_init_struc; C.PO_tl_struc];
    }
    in
    assert_equal false (TaSynt.is_cex_applicable fixed_skel cex3)
        ~msg:"expected the counterexample 3 to be inapplicable"


(*
Merge equivalent conditions into one.
E.g., x >= a, x >= 2 * a, x >= 3 * a will be merged into one when a = 0.
*)
let test_merge_in_deps _ =
    (* prepare the test set *)
    let x, a, b = new_var "x", new_var "a", new_var "b" in
    a#set_symbolic; b#set_symbolic;
    let tt = new data_type_tab in
    let set_type v = tt#set_type v (new data_type SpinTypes.TUNSIGNED) in
    List.iter set_type [x; a; b];
    let mk_cond coeff rhs =
        BinEx (GE, Var x, BinEx (MULT, IntConst coeff, Var rhs))
    in
    let c1, c2, c3, c4 = mk_cond 1 a, mk_cond 2 a, mk_cond 3 a, mk_cond 1 b in
    let id1, id2, id3, id4 =
        PSet.new_thing (), PSet.new_thing (), PSet.new_thing (), PSet.new_thing ()
    in
    (* the TA is: 0 =c1,c2=> 1 =c2,c3=> 2 =c4=> 3 *)
    let cond_map =
        let map_add m (k, v) = PB.PSetEltMap.add k v m in
        List.fold_left map_add PB.PSetEltMap.empty
        [(id1, c1); (id2, c2); (id3, c3); (id4, c4)]
    in
    let mk_set ids =
        let set_add s id = PSet.add id s in
        List.fold_left set_add PSet.empty ids
    in
    let rule_pre =
        let setmap_add m (no, ids) = IntMap.add no (mk_set ids) m in
        List.fold_left setmap_add IntMap.empty
            [ (0, [id1; id2]);   (1, [id2; id3]);   (2, [id4]) ]
    in
    let umask = mk_set [id1; id2; id3; id4] in
    let uconds = [
        ("U1", id1, c1, PB.Unlock);
        ("U2", id2, c2, PB.Unlock);
        ("U3", id3, c3, PB.Unlock);
        ("U4", id4, c4, PB.Unlock);
    ]
    in
    let cond_imp =
        let setmap_add m (id, ids) = PB.PSetEltMap.add id (mk_set ids) m in
        List.fold_left setmap_add PB.PSetEltMap.empty
            [ (id1, []); (id2, [id1]); (id3, [id1; id2]); (id4, []) ]
    in
    let deps = {
        PB.D.empty with
        rule_pre; umask; uconds; cond_map;
    }
    in
    (* do the test *)
    let unknowns_vec = [("a", IntConst 0); ("b", IntConst 1)] in
    let new_deps = TaSynt.merge_in_deps deps in
    assert_equal 2 (PB.PSetEltMap.cardinal deps.PB.D.cond_map)
        ~msg:"expected cardinality 2"


let suite = "taSynt-suite" >:::
    [
        "test_next_unknowns_vec" >:: test_next_unknowns_vec;
        "test_is_cex_applicable" >:: test_is_cex_applicable;
        "test_merge_in_deps" >:: test_merge_in_deps;
    ]

