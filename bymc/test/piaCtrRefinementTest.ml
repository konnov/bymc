open OUnit
open Printf

open Accums
open Smt
open Spin
open SpinIr
open SpinIrImp

open PiaCtrRefinement

let yices = ref (new yices_smt "yices")
let is_started = ref false

let setup _ =
    if not !is_started
    then begin
        (!yices)#start;
        is_started := true;
    end

let teardown _ =
    ignore (!yices)#reset

let shutdown _ =
    ignore (!yices)#stop

let test_parse_smt_evidence _ =
    (!yices)#set_need_model true;
    let n = new_var "N" in
    let nsnt = new_var "nsnt" in
    let nsnt_in = nsnt#copy "S0_nsnt_IN" in
    let nsnt_out = nsnt#copy "S0_nsnt_OUT" in
    let tt = new data_type_tab in
    let append_def v = 
        let t = mk_int_range 0 10 in
        tt#set_type v t;
        (!yices)#append_var_def v t
    in
    List.iter append_def [n; nsnt_in; nsnt_out];

    let add pile lhs rhs =
        B.append_expr (!yices) pile (BinEx (EQ, Var lhs, Const rhs))
    in
    let pile =
        List.fold_left2 add (B.mk_pile ()) [n; nsnt_in; nsnt_out] (range 1 4)
    in
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;

    let prog = Program.set_type_tab tt Program.empty
        |> Program.set_shared [nsnt]
        |> Program.set_params [n] in

    let tab = parse_smt_evidence prog (!yices) pile in
    let layer0 = Hashtbl.find tab 0 |> List.map expr_s |> str_join "; " in
    let exp0 = [ BinEx (ASGN, Var n, Const 1);
                BinEx (ASGN, Var nsnt, Const 2) ]
        |> List.map expr_s |> str_join "; "
    in
    assert_equal exp0 layer0
        ~msg:(sprintf "[%s] expected, found [%s]" exp0 layer0);

    let layer1 = Hashtbl.find tab 1 |> List.map expr_s |> str_join "; " in
    let exp1 =
        [ BinEx (ASGN, Var nsnt, Const 3) ] |> List.map expr_s |> str_join "; "
    in
    assert_equal exp1 layer1
        ~msg:(sprintf "[%s] expected, found [%s]" exp1 layer1)


let test_parse_smt_evidence_array _ =
    (!yices)#set_need_model true;
    let n = new_var "N" in
    let x = new_var "x" in
    let x_in = x#copy "S0_x_IN" in
    let x_out = x#copy "S0_x_OUT" in
    let tt = new data_type_tab in
    let append_def ~is_arr v = 
        let t = mk_int_range 0 10 in
        if is_arr
        then t#set_nelems 2;
        tt#set_type v t;
        (!yices)#append_var_def v t
    in
    List.iter (append_def ~is_arr:false) [n];
    List.iter (append_def ~is_arr:true) [x_in; x_out];

    let add lhs rhs pile =
        B.append_expr (!yices) pile (BinEx (EQ, Var lhs, Const rhs))
    in
    let arr_acc v i = BinEx (ARR_ACCESS, Var v, Const i) in
    let arr_upd v i j = BinEx (EQ, arr_acc v i, Const j) in
    let add_arr arr ind rhs pile =
        B.append_expr (!yices) pile (arr_upd arr ind rhs)
    in
    let pile =
        add n 1 (B.mk_pile ())
        |> add_arr x_in 0 2
        |> add_arr x_in 1 5
        |> add_arr x_out 0 3
        |> add_arr x_out 1 7
    in
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;

    let prog = Program.set_type_tab tt Program.empty
        |> Program.set_instrumental [x]
        |> Program.set_params [n]
    in
    let tab = parse_smt_evidence prog (!yices) pile in
    let layer0 = Hashtbl.find tab 0 |> List.map expr_s |> str_join "; " in
    let exp0 = [ BinEx (ASGN, arr_acc x 0, Const 2);
                 BinEx (ASGN, arr_acc x 1, Const 5);
                 BinEx (ASGN, Var n, Const 1) ]
        |> List.map expr_s |> str_join "; "
    in
    assert_equal exp0 layer0
        ~msg:(sprintf "expected [%s], found [%s]" exp0 layer0);

    let layer1 = Hashtbl.find tab 1 |> List.map expr_s |> str_join "; " in
    let exp1 =
        [ BinEx (ASGN, arr_acc x 0, Const 3);
          BinEx (ASGN, arr_acc x 1, Const 7) ]
            |> List.map expr_s |> str_join "; "
    in
    assert_equal exp1 layer1
        ~msg:(sprintf "expected [%s], found [%s]" exp1 layer1)


let suite = "smt-suite" >:::
    [
        "test_parse_smt_evidence"
            >:: (bracket setup test_parse_smt_evidence teardown);
        "test_parse_smt_evidence_array"
            >:: (bracket setup test_parse_smt_evidence_array shutdown); (* clean the room *)
    ]

