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


let assert_equal_map lm rm =
    assert_equal (IntMap.cardinal lm) (IntMap.cardinal rm)
        ~msg:"maps are not equal";

    let test_elems i =
        let v = IntMap.find i lm in
        let w = IntMap.find i rm in
        assert_equal v#get_name w#get_name
        ~msg:(sprintf "%s != %s" v#get_name w#get_name)
    in
    List.iter test_elems (BatList.of_enum (IntMap.keys lm))


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
    assert_equal_map expected.Sk.loc_vars actual.Sk.loc_vars;
    assert_equal expected.Sk.nrules actual.Sk.nrules
        ~msg:"nrules are not equal";
    List.iter2 assert_equal_rule expected.Sk.rules actual.Sk.rules


let test_skel_of_ta _ =
    let ds =
        [ Local "x"; Shared "g"; Param "n" ]
    in
    let locs = [ ("loc_a", [0]); ("loc_b", [1]) ] in
    let rules = [ {
        Ta.src_loc = 0; Ta.dst_loc = 1;
        guard = Cmp (Geq (Var "x", Add (Var "n", Int 1)));
        action = Cmp (Eq (NextVar "g", Add (Var "g", Int 1)))
    } ] in
    let assumes = [Gt (Var "n", Int 42)] in
    let mk0 name = LtlCmp (Eq (Var name, Int 0)) in
    let unforg = LtlImplies (mk0 "loc_a", LtlG (mk0 "loc_b")) in
    let forms = StrMap.singleton "unforg" unforg in
    let ta = TaIr.mk_ta "foo" ds assumes locs [] rules forms in
    let x = SpinIr.new_var "x" in
    let g = SpinIr.new_var "g" in
    let n = SpinIr.new_var "n" in
    let sk = {
        Sk.name = "foo";
        Sk.nlocs = 2;
        Sk.locs = [[0]; [1]];
        Sk.locals = [x];
        Sk.shared = [g];
        Sk.params = [n];
        Sk.assumes =
            [ SpinIr.BinEx (Spin.GT, SpinIr.Var n, SpinIr.IntConst 42) ];
        Sk.inits = [];
        Sk.loc_vars = Accums.IntMap.singleton 0 x;
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
        Sk.forms = Accums.StrMap.empty;
    } in
    expect_skel sk (TaIrBridge.skel_of_ta ta)


let suite = "taIrBridge-suite" >:::
    [
        "test_skel_of_ta" >:: test_skel_of_ta;
    ]

