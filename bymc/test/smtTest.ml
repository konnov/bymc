open OUnit
open Printf

open Accums
open Smt
open Spin
open SpinIr
open SpinIrImp

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

let test_wrong_solver _ =
    let kaboom _ =
        let solver = new yices_smt "solver-from-the-year-2020" in
        solver#start;
        ignore (solver#append_expr (Const 1))
    in
    assert_raises
        (PipeCmd.Comm_error "Process terminated prematurely, see: cmd.log") kaboom


let test_trivial_sat _ =
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true 


let test_trivial_unsat _ =
    ignore ((!yices)#append_expr (BinEx (EQ, Const 1, Const 2)));
    let res = (!yices)#check in
    assert_equal ~msg:"unsat expected" res false 


let test_reset _ =
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    ignore ((!yices)#append_expr (BinEx (EQ, Const 1, Const 2)));
    let res = (!yices)#check in
    assert_equal ~msg:"unsat expected" res false;
    (!yices)#reset;
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected after reset" res true 


let test_comment _ =
    (!yices)#comment "Just a comment";
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true 


let test_append_var_def _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!yices)#append_var_def x t;
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true 


let test_append_expr _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!yices)#append_var_def x t;
    ignore ((!yices)#append_expr
        (BinEx (AND,
            (BinEx (EQ, Var x, Const 1)),
            (BinEx (EQ, Var x, Const 2)))));
    let res = (!yices)#check in
    assert_equal ~msg:"unsat expected" res false 


let test_push_ctx _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!yices)#append_var_def x t;
    (!yices)#push_ctx


let test_pop_ctx _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!yices)#append_var_def x t;
    ignore ((!yices)#append_expr (BinEx (EQ, Var x, Const 1)));
    (!yices)#push_ctx;
    ignore ((!yices)#append_expr (BinEx (EQ, Var x, Const 2)));
    let res = (!yices)#check in
    assert_equal ~msg:"unsat expected" res false;
    (!yices)#pop_ctx;
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true


let test_get_stack_level _ =
    (!yices)#push_ctx;
    assert_equal ~msg:"stack level 1 expected" !(yices)#get_stack_level 1;
    (!yices)#push_ctx;
    assert_equal ~msg:"stack level 2 expected" !(yices)#get_stack_level 2;
    (!yices)#pop_ctx;
    assert_equal ~msg:"stack level 1 expected" !(yices)#get_stack_level 1


let test_get_unsat_cores _ =
    (!yices)#set_need_model true;
    (!yices)#set_collect_asserts true;
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!yices)#append_var_def x t;
    let id = (!yices)#append_expr
        (BinEx (AND,
            (BinEx (EQ, Var x, Const 1)),
            (BinEx (EQ, Var x, Const 2)))) in
    let res = (!yices)#check in
    assert_equal ~msg:"unsat expected" res false;
    let cores = (!yices)#get_unsat_cores in
    if cores <> [id]
    then
        let cores_s = str_join ", " (List.map int_s cores) in
        assert_failure (sprintf "expected [%d], got [%s]" id cores_s)


let test_get_model_one_var _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    let e = BinEx (EQ, Var x, Const 1) in
    ignore ((!yices)#append_expr e);
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    let lookup _ = x in (* here it is that simple *)
    let model = (!yices)#get_model lookup in
    if model <> [ e ]
    then let es_s = str_join "; " (List.map expr_s model) in
        assert_failure (sprintf "expected [%s], found [%s]" (expr_s e) es_s)


let test_get_model_var_with_underscore _ =
    let x = new_var "_x" in
    let t = mk_int_range 0 10 in
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    let e = BinEx (EQ, Var x, Const 1) in
    ignore ((!yices)#append_expr e);
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    let lookup _ = x in (* here it is that simple *)
    let model = (!yices)#get_model lookup in
    if model <> [ e ]
    then let es_s = str_join "; " (List.map expr_s model) in
        assert_failure (sprintf "expected [%s], found [%s]" (expr_s e) es_s)



let test_get_model_array _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    t#set_nelems 3;
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    let arr_upd i j =
        BinEx (EQ, BinEx (ARR_ACCESS, Var x, Const i), Const j) in
    let e1, e2, e3 = arr_upd 0 1, arr_upd 1 2, arr_upd 2 3 in
    ignore ((!yices)#append_expr e1);
    ignore ((!yices)#append_expr e2);
    ignore ((!yices)#append_expr e3);
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    let lookup _ = x in (* here it is that simple *)
    let model = (!yices)#get_model lookup in
    if model <> [ e1; e2; e3 ]
    then let es_s = str_join "; " (List.map expr_s model) in
    assert_failure (sprintf "expected [%s; %s; %s], found [%s]"
        (expr_s e1) (expr_s e2) (expr_s e3) es_s)


let test_get_model_array_copy _ =
    let x = new_var "x" in
    let y = new_var "y" in
    let t = mk_int_range 0 10 in
    t#set_nelems 3;
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    (!yices)#append_var_def y t;
    let arr_upd v i j =
        BinEx (EQ, BinEx (ARR_ACCESS, Var v, Const i), Const j) in
    let e1, e2, e3 = arr_upd x 0 1, arr_upd x 1 2, arr_upd x 2 3 in
    ignore ((!yices)#append_expr e1);
    ignore ((!yices)#append_expr e2);
    ignore ((!yices)#append_expr e3);
    ignore ((!yices)#append_expr (BinEx (EQ, Var x, Var y)));
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    let lookup n = if n = "x" then x else y in
    let model = (!yices)#get_model lookup in
    let e4, e5, e6 = arr_upd y 0 1, arr_upd y 1 2, arr_upd y 2 3 in
    let expected = [e1; e4; e2; e5; e3; e6] in
    if model <> expected
    then let found_s = str_join "; " (List.map expr_s model) in
    let exp_s = str_join "; " (List.map expr_s expected) in
    assert_failure (sprintf "expected [%s], found [%s]" exp_s found_s)


let test_model_query_try_get _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    let e = BinEx (EQ, Var x, Const 1) in
    ignore ((!yices)#append_expr e);
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    
    let query = (!yices)#get_model_new in
    let res = query#try_get (Var x) in
    assert_equal ~msg:"QCached expected" res QCached;

    query#submit;

    let res = query#try_get (Var x) in
    assert_equal ~msg:"QResult (Const 1) expected" res (QResult (Const 1))


let test_model_query_try_get_not_found _ =
    let y = new_var "y" in
    (!yices)#set_need_model true;
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    
    let query = (!yices)#get_model_new in
    let res = query#try_get (Var y) in
    assert_equal ~msg:"QCached expected" res QCached;

    query#submit;

    let res = query#try_get (Var y) in
    assert_equal ~msg:"QNot_found expected" res QNot_found


let suite = "smt-suite" >:::
    [
        "test_wrong_solver" >:: test_trivial_sat;
        "test_trivial_sat" >:: (bracket setup test_trivial_sat teardown);
        "test_trivial_unsat" >:: (bracket setup test_trivial_unsat teardown);
        "test_reset" >:: (bracket setup test_reset teardown);
        "test_comment" >:: (bracket setup test_comment teardown);
        "test_append_var_def" >:: (bracket setup test_append_var_def teardown);
        "test_append_expr" >:: (bracket setup test_append_expr teardown);
        "test_push_ctx" >:: (bracket setup test_push_ctx teardown);
        "test_pop_ctx" >:: (bracket setup test_pop_ctx teardown);
        "test_get_stack_level"
            >:: (bracket setup test_get_stack_level teardown);
        "test_get_unsat_cores"
            >:: (bracket setup test_get_unsat_cores teardown);
        "test_get_model_one_var"
            >:: (bracket setup test_get_model_one_var teardown);
        "test_get_model_array"
            >:: (bracket setup test_get_model_array teardown);
        "test_get_model_array_copy"
            >:: (bracket setup test_get_model_array_copy teardown);
        "test_get_model_var_with_underscore"
            >:: (bracket setup test_get_model_var_with_underscore teardown);
        "test_model_query_try_get"
            >:: (bracket setup test_model_query_try_get teardown);
        "test_model_query_try_get_not_found"
            >:: (bracket setup test_model_query_try_get_not_found shutdown (* clean the room *));
    ]

