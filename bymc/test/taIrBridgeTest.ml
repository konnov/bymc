open Batteries
open BatPrintf
open OUnit

open Accums
open TaIr
open SymbSkel

let assert_equal_expr l r =
    let ls = SpinIrImp.expr_s l in
    let rs = SpinIrImp.expr_s r in
    assert_equal ls rs
        ~msg:(sprintf "'%s' != '%s'" ls rs)


let assert_eq_int_map lm rm =
    let lm_size, rm_size = IntMap.cardinal lm, IntMap.cardinal rm in
    assert_equal lm_size rm_size
        ~msg:(sprintf "map sizes are not equal: %d and %d" lm_size rm_size);

    let test_elems i =
        let v = IntMap.find i lm in
        let w = IntMap.find i rm in
        assert_equal v#get_name w#get_name
            ~msg:(sprintf "%s != %s" v#get_name w#get_name)
    in
    List.iter test_elems (BatList.of_enum (IntMap.keys lm))


let assert_eq_str_map lm rm =
    let lm_size, rm_size = StrMap.cardinal lm, StrMap.cardinal rm in
    assert_equal lm_size rm_size
        ~msg:(sprintf "map sizes are not equal: %d and %d" lm_size rm_size);

    let test_elems i =
        let le_s = SpinIrImp.expr_s (StrMap.find i lm) in
        let re_s = SpinIrImp.expr_s (StrMap.find i rm) in
        assert_equal le_s re_s
            ~msg:(sprintf "expected equal expressions, found: %s and %s"
                le_s re_s)
    in
    List.iter test_elems (BatList.of_enum (StrMap.keys lm))


let assert_equal_rule lr rr =
    assert_equal lr.Sk.src rr.Sk.src
        ~msg:(sprintf "rule src are not equal: %d != %d" lr.Sk.src rr.Sk.src);
    assert_equal lr.Sk.dst rr.Sk.dst
        ~msg:(sprintf "rule dst are not equal: %d != %d" lr.Sk.dst rr.Sk.dst);
    assert_equal_expr lr.Sk.guard rr.Sk.guard;
    List.iter2 (fun la ra -> assert_equal_expr la ra) lr.Sk.act rr.Sk.act



let expect_skel expected actual =
    let is_var_eq v w =
        v#get_name = w#get_name
    in
    let assert_vars_eq ~msg:m vs ws =
        assert_bool m (List.for_all2 is_var_eq vs ws)
    in
    assert_equal expected.Sk.name actual.Sk.name
        ~msg:"names are not equal";
    assert_equal expected.Sk.nlocs actual.Sk.nlocs
        ~msg:"nlocs are not equal";
    assert_equal expected.Sk.locs actual.Sk.locs
        ~msg:"locs are not equal";
    assert_vars_eq expected.Sk.locals actual.Sk.locals
        ~msg:"locals are not equal";
    assert_vars_eq expected.Sk.shared actual.Sk.shared
        ~msg:"shared are not equal";
    assert_vars_eq expected.Sk.params actual.Sk.params
        ~msg:"params are not equal";
    List.iter2 assert_equal_expr expected.Sk.assumes actual.Sk.assumes;
    List.iter2 assert_equal_expr expected.Sk.inits actual.Sk.inits;
    assert_eq_int_map expected.Sk.loc_vars actual.Sk.loc_vars;
    assert_equal expected.Sk.nrules actual.Sk.nrules
        ~msg:"nrules are not equal";
    List.iter2 assert_equal_rule expected.Sk.rules actual.Sk.rules;
    assert_eq_str_map expected.Sk.forms actual.Sk.forms


let test_skel_of_ta _ =
    let ds =
        [ Local "x"; Shared "g"; Param "n" ]
    in
    let locs = [ ("loc_0", [0]); ("loc_1", [1]) ] in
    let rules = [ {
        Ta.src_loc = 0; Ta.dst_loc = 1;
        guard = Cmp (Geq (Var "x", Add (Var "n", Int 1)));
        action = Cmp (Eq (NextVar "g", Add (Var "g", Int 1)))
    } ] in
    let assumes = [Gt (Var "n", Int 42)] in
    let mk0 name = LtlCmp (Eq (Var name, Int 0)) in
    let unforg =
        LtlImplies (mk0 "loc_0", LtlG (mk0 "loc_1")) in
    let specs = StrMap.singleton "unforg" unforg in
    let inits = [ (Eq (Var "loc_0", Int 0)) ] in
    let ta =
        TaIr.mk_ta "foo" ds assumes locs inits rules specs
    in
    let x = SpinIr.new_var "x" in
    let g = SpinIr.new_var "g" in
    let n = SpinIr.new_var "n" in
    let loc_0 = SpinIr.new_var "loc_0" in
    let loc_1 = SpinIr.new_var "loc_1" in
    let unforg_exp =
        SpinIr.BinEx (Spin.IMPLIES,
            SpinIr.BinEx (Spin.EQ, SpinIr.Var loc_0, SpinIr.IntConst 0),
            SpinIr.UnEx (Spin.ALWAYS,
                SpinIr.BinEx (Spin.EQ, SpinIr.Var loc_1, SpinIr.IntConst 0)))
    in
    let sk = {
        Sk.name = "foo";
        Sk.nlocs = 2;
        Sk.locs = [[0]; [1]];
        Sk.locals = [x];
        Sk.shared = [g];
        Sk.params = [n];
        Sk.assumes =
            [ SpinIr.BinEx (Spin.GT, SpinIr.Var n, SpinIr.IntConst 42) ];
        Sk.inits = [ (SpinIr.BinEx (Spin.EQ, SpinIr.Var loc_0, SpinIr.IntConst 0)) ];
        Sk.loc_vars =
            Accums.IntMap.add 1 loc_1 (Accums.IntMap.singleton 0 loc_0);
        Sk.nrules = 1;
        Sk.rules = [{
            Sk.src = 0;
            Sk.dst = 1;
            Sk.guard =
                SpinIr.BinEx (Spin.GE,
                    SpinIr.Var x,
                    SpinIr.BinEx (Spin.PLUS, SpinIr.Var n, SpinIr.IntConst 1));
            Sk.act = [
                SpinIr.BinEx (Spin.EQ,
                    SpinIr.UnEx (Spin.NEXT, SpinIr.Var g),
                    SpinIr.BinEx (Spin.PLUS, SpinIr.Var g, SpinIr.IntConst 1))];
        }];
        Sk.forms = Accums.StrMap.singleton "unforg" unforg_exp;
    } in
    expect_skel sk (TaIrBridge.skel_of_ta ta)


let suite = "taIrBridge-suite" >:::
    [
        "test_skel_of_ta" >:: test_skel_of_ta;
    ]

