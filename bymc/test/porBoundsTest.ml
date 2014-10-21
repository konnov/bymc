open OUnit
open Batteries
open BatPrintf

open Accums
open Debug
open PorBounds
open Smt
open Spin
open SpinIr
open SymbSkel

(* overload operators for convenience *)
let (>=.) l r = BinEx (GE, Var l, Var r)

let (<.) l r = BinEx (LT, Var l, Var r)

let (=.) l e = BinEx (EQ, UnEx (NEXT, Var l), e)

let keep x = BinEx (EQ, UnEx (NEXT, Var x), Var x)

let (+.) v i = BinEx (PLUS, Var v, IntConst i)

let tru = IntConst 1

let mk_rule src dst guard act = { Sk.src; Sk.dst; Sk.guard; Sk.act }

let str_of_ints is = List.map string_of_int is |> str_join ", "


let solver = ref (new lib2_smt "z3" [| "-smt2"; "-in"|])
let is_started = ref false

let setup _ =
    initialize_debug {
        Options.empty with
          Options.plugin_opts = (StringMap.singleton "trace.mods" "cmd")
    };
    if not !is_started
    then begin
        (!solver)#start;
        is_started := true;
    end

let teardown _ =
    ignore (!solver#reset)

let shutdown _ =
    ignore (!solver#stop)


let prepare () =
    let opts = Options.empty in
    let caches = new Infra.pass_caches opts (new Infra.analysis_cache) in
    let rt = new Runtime.runtime_t !(solver) caches in
    let tt = new data_type_tab in
    let pc = new_var "pc" in
    tt#set_type pc (mk_int_range 0 4);
    let x, y, n, t = new_var "x", new_var "y", new_var "n", new_var "t" in
    n#set_symbolic; t#set_symbolic;
    List.iter
        (fun v -> tt#set_type v (new data_type SpinTypes.TUNSIGNED))
        [x; y; n; t];
    let add_loc map i =
        let loc = new_var (sprintf "loc%d" i) in
        IntMap.add i loc map
    in
    let loc_map = List.fold_left add_loc IntMap.empty (range 0 4) in
    rt, tt, loc_map, pc, x, y, n, t


let test_make_schema_tree_unlocking _ =
    let rt, tt, loc_map, pc, x, y, n, t = prepare () in
    let mk_eq loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    rt#solver#append_var_def n (tt#get_type n);
    rt#solver#append_var_def t (tt#get_type t);
    ignore (rt#solver#append_expr
        (BinEx (GT, Var n, BinEx (MULT, IntConst 2, Var t))));

    (*

    The control flow is as follows:

        r0 = 0 -> 1 ? x > t: x = x; y' = y + 1;;
        r1 = 0 -> 1 ? true:  x' = x + 1; y' = y;
        r2 = 1 -> 2 ? y > t: x' = x; y' = y;
        r3 = 2 -> 3 ? true:  x' = x; y' = y;

    *)
    let sk = {
        Sk.name = "foo";
        Sk.nlocs = 4; Sk.locs = [ [0]; [1]; [2]; [3] ];
        Sk.locals = [ pc ]; Sk.shared = [ x; y ]; Sk.params = [ n; t ];
        Sk.nrules = 4;
        Sk.rules = [
            mk_rule 0 1 (x >=. t) [ keep x; y =. y +. 1 ];
            mk_rule 0 1 tru     [ keep y; x =. x +. 1 ];
            mk_rule 1 2 (y >=. t) [ keep x; keep y ];
            mk_rule 2 3 tru     [ keep x; keep y ];
        ];
        Sk.inits = [ mk_eq 0 (Var n); mk_eq 1 (IntConst 0);
            mk_eq 2 (IntConst 0); mk_eq 3 (IntConst 0) ];
        Sk.loc_vars = loc_map;
    }
    in
    let tree, _ = PorBounds.make_schema_tree !solver sk in

    (* the show starts here *)
    (* Sk.print stdout sk; *)

    match tree with
        | T.Node (seg1,
            [ { T.cond_after = cond; T.cond_rules = crules;
                T.subtree = T.Leaf seg2 } ] ) ->

            assert_equal [1; 2; 3] seg1
                ~msg:(sprintf "expected first segment to be [1; 2; 3], found [%s]"
                    (str_of_ints seg1));
            assert_equal [0; 1; 2; 3] seg2
                ~msg:(sprintf "expected last segment to be [0; 1; 2; 3], found [%s]"
                    (str_of_ints seg2));
            assert_equal [0] crules
                ~msg:(sprintf "expected conditions [2], found [%s]"
                    (str_of_ints crules));

            let _, _, _, lt = cond in
            assert_equal Unlock lt ~msg:"expected Unlock, found Lock"
                    
        | _ ->
            print_tree stdout tree;
            assert_failure 
                (sprintf "expected 2 segments and one milestone, found the tree as shown above")



let test_make_schema_tree_locking _ =
    let rt, tt, loc_map, pc, x, y, n, t = prepare () in
    let mk_eq loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    rt#solver#append_var_def n (tt#get_type n);
    rt#solver#append_var_def t (tt#get_type t);
    ignore (rt#solver#append_expr
        (BinEx (GT, Var n, BinEx (MULT, IntConst 2, Var t))));

    (*

    The control flow is as follows:

        r0 = 0 -> 1 ? x > t: x = x; y' = y + 1;;
        r1 = 0 -> 1 ? true:  x' = x + 1; y' = y;
        r2 = 1 -> 2 ? y > t: x' = x; y' = y;
        r3 = 2 -> 3 ? true:  x' = x; y' = y;

    *)
    let sk = {
        Sk.name = "foo";
        Sk.nlocs = 4; Sk.locs = [ [0]; [1]; [2]; [3] ];
        Sk.locals = [ pc ]; Sk.shared = [ x; y ]; Sk.params = [ n; t ];
        Sk.nrules = 4;
        Sk.rules = [
            mk_rule 0 1 (x <. t) [ keep x; y =. y +. 1 ];
            mk_rule 0 1 tru     [ keep y; x =. x +. 1 ];
            mk_rule 1 2 (y >=. t) [ keep x; keep y ];
            mk_rule 2 3 tru     [ keep x; keep y ];
        ];
        Sk.inits = [ mk_eq 0 (Var n); mk_eq 1 (IntConst 0);
            mk_eq 2 (IntConst 0); mk_eq 3 (IntConst 0) ];
        Sk.loc_vars = loc_map;
    }
    in
    let tree, _ = PorBounds.make_schema_tree !solver sk in

    (* the show starts here *)
    (* Sk.print stdout sk; *)

    match tree with
        | T.Node (seg1,
            [ { T.cond_after = cond; T.cond_rules = crules;
                T.subtree = T.Leaf seg2 } ] ) ->

            assert_equal [0; 1; 2; 3] seg1
                ~msg:(sprintf "expected first segment to be [0; 1; 2; 3], found [%s]"
                    (str_of_ints seg1));
            assert_equal [1; 2; 3] seg2
                ~msg:(sprintf "expected last segment to be [1; 2; 3], found [%s]"
                    (str_of_ints seg2));
            assert_equal [0] crules
                ~msg:(sprintf "expected conditions [2], found [%s]"
                    (str_of_ints crules));

            let _, _, _, lt = cond in
            assert_equal Lock lt ~msg:"expected Lock, found Unlock"
                    
        | _ ->
            print_tree stdout tree;
            assert_failure 
                (sprintf "expected 2 segments and one milestone, found the tree as shown above")


let test_make_schema_tree_unlocking_no_redundant_milestones _ =
    let rt, tt, loc_map, pc, x, y, n, t = prepare () in
    let mk_eq loc_no e =
        BinEx (EQ, Var (IntMap.find loc_no loc_map), e)
    in
    rt#solver#append_var_def n (tt#get_type n);
    rt#solver#append_var_def t (tt#get_type t);
    ignore (rt#solver#append_expr
        (BinEx (GT, Var n, BinEx (MULT, IntConst 2, Var t))));

    (*

    The control flow is as follows:

        r0 = 0 -> 1 ? x > t: x = x; y' = y + 1;;
        r1 = 0 -> 1 ? true:  x' = x + 1; y' = y;
        r2 = 1 -> 2 ? y > t: x' = x + 1; y' = y;
        r3 = 2 -> 3 ? true:  x' = x + 1; y' = y;

    *)
    let sk = {
        Sk.name = "foo";
        Sk.nlocs = 4; Sk.locs = [ [0]; [1]; [2]; [3] ];
        Sk.locals = [ pc ]; Sk.shared = [ x; y ]; Sk.params = [ n; t ];
        Sk.nrules = 5;
        Sk.rules = [
            mk_rule 0 1 (x >=. t)    [ keep x; y =. y +. 1 ];
            mk_rule 0 1 tru         [ keep y; x =. x +. 1 ];
            mk_rule 1 2 (y >=. t)    [ keep x; keep y ];
            mk_rule 1 2 (x >=. t)    [ keep x; y =. y +. 1 ];
            mk_rule 2 3 (BinEx (AND, x >=. t, y >=. t)) [ keep x; keep y ];
        ];
        Sk.inits = [ mk_eq 0 (Var n); mk_eq 1 (IntConst 0);
            mk_eq 2 (IntConst 0); mk_eq 3 (IntConst 0) ];
        Sk.loc_vars = loc_map;
    }
    in
    let tree, _ = PorBounds.make_schema_tree !solver sk in

    (* the show starts here *)
    (* Sk.print stdout sk; *)

    let assert_segment seg_no expected actual =
        assert_equal expected actual
            ~msg:(sprintf "expected segment %d to be [%s], found [%s]"
                seg_no (str_of_ints expected) (str_of_ints actual))
    in
    let assert_milestone seg_no expected actual =
        assert_equal expected actual
            ~msg:(sprintf "expected milestone %d to be [%s], found [%s]"
                seg_no (str_of_ints expected) (str_of_ints actual))
    in
    match tree with
        | T.Node (seg1,
            [   (* branch 1 *)
                { T.cond_after = _, _, cond1, _; T.cond_rules = crules1;
                T.subtree = T.Node (seg2,
                    [{ T.cond_after = _, _, cond2, _; T.cond_rules = crules2;
                       T.subtree = T.Leaf seg3}])
                };
                (* branch 2 *)
                { T.cond_after = _, _, cond3, _; T.cond_rules = crules3;
                T.subtree = T.Node (seg4,
                    [{ T.cond_after = _, _, cond4, _; T.cond_rules = crules4;
                       T.subtree = T.Leaf seg5}])
                };
            ]) ->

            let seg1, seg2, seg3, seg4, seg5 =
                if ("(y >= t)" <> (SpinIrImp.expr_s cond1))
                then seg1, seg2, seg3, seg4, seg5
                else seg1, seg4, seg5, seg2, seg3
            in
            let crules1, crules2, crules3, crules4 =
                if ("(y >= t)" <> (SpinIrImp.expr_s cond1))
                then crules1, crules2, crules3, crules4
                else crules3, crules4, crules1, crules2
            in

            assert_segment 1 [1] seg1;
            assert_segment 2 [0; 1; 3] seg2;
            assert_segment 3 [0; 1; 3; 2; 4] seg3;
            assert_milestone 1 [0; 3] crules1;
            assert_milestone 2 [2; 4] crules2;

            assert_segment 4 [1; 2] seg4;
            assert_segment 5 [0; 1; 3; 2; 4] seg5;
            assert_milestone 3 [2] crules3;
            assert_milestone 4 [0; 3; 4] crules4;

        | _ ->
            print_tree stdout tree;
            assert_failure 
                (sprintf "expected 3 segments and one milestone, found the tree as shown above")



let suite = "porBounds-suite" >:::
    [
        "test_make_schema_tree_unlocking"
          >:: (bracket setup test_make_schema_tree_unlocking teardown);
        "test_make_schema_tree_unlocking_no_redundant_milestones"
          >:: (bracket setup
            test_make_schema_tree_unlocking_no_redundant_milestones teardown);
        "test_make_schema_tree_locking"
          >:: (bracket setup test_make_schema_tree_locking shutdown); (* clean the room *)
    ]
