open Batteries
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
        (PipeCmd.Comm_error "exec solver-from-the-year-2020 failed: No such file or directory") kaboom


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
    let query = (!yices)#get_model_query in
    assert_equal Q.Cached (Q.try_get query (Var x)) ~msg:"Cached expected";
    let query = (!yices)#submit_query query in
    let res = Q.try_get query (Var x) in
    assert_equal (Q.Result (Const 1)) res
        ~msg:(sprintf "(Const 1) expected, found %s" (Q.query_result_s res))


let test_get_model_var_with_underscore _ =
    let x = new_var "_x" in
    let t = mk_int_range 0 10 in
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    let e = BinEx (EQ, Var x, Const 1) in
    ignore ((!yices)#append_expr e);
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    let query = (!yices)#get_model_query in
    assert_equal Q.Cached (Q.try_get query (Var x)) ~msg:"Cached expected";
    let query = (!yices)#submit_query query in
    let res = Q.try_get query (Var x) in
    assert_equal (Q.Result (Const 1)) res
        ~msg:(sprintf "(Const 1) expected, found %s" (Q.query_result_s res))


let test_get_model_array _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    t#set_nelems 3;
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    let arr_acc i = BinEx (ARR_ACCESS, Var x, Const i) in
    let arr_upd i j = BinEx (EQ, arr_acc i, Const j) in
    Enum.iter (fun i -> ignore ((!yices)#append_expr (arr_upd i (1 + i)))) (0--2);
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;

    let query = (!yices)#get_model_query in
    let assert_cached i =
        let res = Q.try_get query (arr_acc i) in
        assert_equal Q.Cached res ~msg:(sprintf "Cached expected for %d" i)
    in
    Enum.iter assert_cached (0--2);

    let query = (!yices)#submit_query query in

    let assert_result i =
        let res = Q.try_get query (arr_acc i) in
        let exp = Q.Result (Const (1 + i)) in
        if exp <> res
        then Q.print_contents query;
        assert_equal exp res
            ~msg:(sprintf "%s expected, found %s"
                           (Q.query_result_s exp) (Q.query_result_s res))
    in
    Enum.iter assert_result (0--2)


let test_get_model_array_copy _ =
    let x = new_var "x" in
    let y = new_var "y" in
    let t = mk_int_range 0 10 in
    t#set_nelems 3;
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    (!yices)#append_var_def y t;
    let arr_acc v i = BinEx (ARR_ACCESS, Var v, Const i) in
    let arr_upd v i j = BinEx (EQ, arr_acc v i, Const j) in
    Enum.iter (fun i -> ignore ((!yices)#append_expr (arr_upd x i (1 + i)))) (0--2);
    ignore ((!yices)#append_expr (BinEx (EQ, Var x, Var y)));
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;

    let query = (!yices)#get_model_query in
    let assert_cached v i =
        let res = Q.try_get query (arr_acc v i) in
        assert_equal Q.Cached res ~msg:(sprintf "Cached expected for %d" i)
    in
    Enum.iter (assert_cached x) (0--2);
    Enum.iter (assert_cached y) (0--2);

    let query = (!yices)#submit_query query in

    let assert_result v i =
        let res = Q.try_get query (arr_acc v i) in
        let exp = Q.Result (Const (1 + i)) in
        if exp <> res
        then Q.print_contents query;
        assert_equal exp res
            ~msg:(sprintf "%s expected, found %s"
                    (Q.query_result_s exp) (Q.query_result_s res))
    in
    Enum.iter (assert_result x) (0--2);
    Enum.iter (assert_result y) (0--2)


let test_model_query_try_get _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!yices)#set_need_model true;
    (!yices)#append_var_def x t;
    let e = BinEx (EQ, Var x, Const 1) in
    ignore ((!yices)#append_expr e);
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;
    
    let query = (!yices)#get_model_query in
    let res = Q.try_get query (Var x) in
    assert_equal ~msg:"Q.Cached expected" res Q.Cached;

    let query = (!yices)#submit_query query in

    let res = Q.try_get query (Var x) in
    assert_equal ~msg:"Q.Result (Const 1) expected" res (Q.Result (Const 1))


let test_model_query_try_get_not_found _ =
    (!yices)#set_need_model true;
    let res = (!yices)#check in
    assert_equal ~msg:"sat expected" res true;

    let query = (!yices)#get_model_query in
    (* y was never passed to the solver *)
    let y = new_var "y" in
    let res = Q.try_get query (Var y) in
    assert_equal ~msg:"Q.Cached expected" res Q.Cached;

    let new_query = (!yices)#submit_query query in

    let new_res = Q.try_get new_query (Var y) in
    assert_equal
        ~msg:(sprintf "NoResult expected, found %s"
                (Q.query_result_s new_res))
        new_res Q.NoResult


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
        "test_get_model_one_var"
            >:: (bracket setup test_get_model_one_var teardown);
        "test_get_model_array"
            >:: (bracket setup test_get_model_array teardown);
        "test_get_model_var_with_underscore"
            >:: (bracket setup test_get_model_var_with_underscore teardown);
        "test_get_model_array_copy"
            >:: (bracket setup test_get_model_array_copy teardown);
        "test_model_query_try_get"
            >:: (bracket setup test_model_query_try_get teardown);
        "test_model_query_try_get_not_found"
            >:: (bracket setup test_model_query_try_get_not_found shutdown (* clean the room *));
        "test_wrong_solver" >:: test_wrong_solver;
    ]

