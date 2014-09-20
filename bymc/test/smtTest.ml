open OUnit
open Printf

open Smt
open Spin
open SpinIr

let yices = ref (new yices_smt)
let is_started = ref false

let setup _ =
    if not !is_started
    then begin
        (!yices)#start;
        is_started := true;
    end

let teardown _ =
    (!yices)#reset


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
    (!yices)#set_need_evidence true;
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
        let cores_s = Accums.str_join ", " (List.map Accums.int_s cores) in
        assert_failure (sprintf "expected [%d], got [%s]" id cores_s)


let suite = "smt-suite" >:::
    [
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
    ]

