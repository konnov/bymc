open Batteries
open OUnit
open Printf

open Accums
open Smt
open Spin
open SpinIr
open SpinIrImp

let solver = ref (new yices_smt "yices")
let is_started = ref false

let setup_yices _ =
    if not !is_started
    then begin
        solver := new yices_smt "yices";
        (!solver)#start;
        is_started := true;
    end

let reset_yices _ =
    assert (!is_started);
    ignore (!solver)#reset

let shutdown_yices _ =
    ignore (!solver)#stop;
    is_started := false

let setup_smt2 _ =
    if not !is_started
    then begin
        solver := new lib2_smt "z3" [| "-smt2"; "-in"|];
        (!solver)#start;
        is_started := true;
    end

let reset_smt2 _ =
    ignore (!solver)#reset

let shutdown_smt2 _ =
    ignore (!solver)#stop


let test_wrong_solver _ =
    let kaboom _ =
        let solver = new yices_smt "solver-from-the-year-2020" in
        solver#start;
        ignore (solver#append_expr (Const 1))
    in
    assert_raises
        (PipeCmd.Comm_error "exec solver-from-the-year-2020 failed: No such file or directory") kaboom


let test_trivial_sat _ =
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true 


let test_trivial_unsat _ =
    ignore ((!solver)#append_expr (BinEx (EQ, Const 1, Const 2)));
    let res = (!solver)#check in
    assert_equal ~msg:"unsat expected" res false 


let test_reset _ =
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true;
    ignore ((!solver)#append_expr (BinEx (EQ, Const 1, Const 2)));
    let res = (!solver)#check in
    assert_equal ~msg:"unsat expected" res false;
    (!solver)#reset;
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected after reset" res true 


let test_comment _ =
    (!solver)#comment "Just a comment";
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true 


let test_append_var_def _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!solver)#append_var_def x t;
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true 


let test_append_var_def_array _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    t#set_nelems 4;
    (!solver)#append_var_def x t;
    ignore ((!solver)#append_expr
        (BinEx (EQ, BinEx (ARR_ACCESS, Var x, Const 1), Const 43)));
    let res = (!solver)#check in
    assert_equal ~msg:"unsat expected" res false 


let test_append_expr _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!solver)#append_var_def x t;
    ignore ((!solver)#append_expr
        (BinEx (AND,
            (BinEx (EQ, Var x, Const 1)),
            (BinEx (EQ, Var x, Const 2)))));
    let res = (!solver)#check in
    assert_equal ~msg:"unsat expected" res false 


let test_push_ctx _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!solver)#append_var_def x t;
    (!solver)#push_ctx


let test_pop_ctx _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!solver)#append_var_def x t;
    ignore ((!solver)#append_expr (BinEx (EQ, Var x, Const 1)));
    (!solver)#push_ctx;
    ignore ((!solver)#append_expr (BinEx (EQ, Var x, Const 2)));
    let res = (!solver)#check in
    assert_equal ~msg:"unsat expected" res false;
    (!solver)#pop_ctx;
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true


let test_get_stack_level _ =
    let level = !(solver)#get_stack_level in
    (!solver)#push_ctx;
    assert_equal  (1 + level) !(solver)#get_stack_level
        ~msg:"stack level 1 expected";
    (!solver)#push_ctx;
    assert_equal  (2 + level) !(solver)#get_stack_level
        ~msg:"stack level 2 expected";
    (!solver)#pop_ctx;
    assert_equal  (1 + level) !(solver)#get_stack_level
        ~msg:"stack level 1 expected"


let test_get_unsat_cores _ =
    (!solver)#set_need_model true;
    (!solver)#set_collect_asserts true;
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!solver)#append_var_def x t;
    let id1 = (!solver)#append_expr (BinEx (EQ, Var x, Const 1)) in
    let id2 = (!solver)#append_expr (BinEx (EQ, Var x, Const 2)) in
    let res = (!solver)#check in
    assert_equal ~msg:"unsat expected" res false;
    let cores = (!solver)#get_unsat_cores in
    if cores <> [id1; id2]
    then
        let cores_s = str_join ", " (List.map int_s cores) in
        assert_failure (sprintf "expected [%d; %d], got [%s]" id1 id2 cores_s)


let test_get_model_one_var _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!solver)#set_need_model true;
    (!solver)#append_var_def x t;
    let e = BinEx (EQ, Var x, Const 1) in
    ignore ((!solver)#append_expr e);
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true;
    let query = (!solver)#get_model_query in
    assert_equal Q.Cached (Q.try_get query (Var x)) ~msg:"Cached expected";
    let query = (!solver)#submit_query query in
    let res = Q.try_get query (Var x) in
    assert_equal (Q.Result (Const 1)) res
        ~msg:(sprintf "(Const 1) expected, found %s"
                (Q.query_result_s query res))


let test_get_model_var_with_underscore _ =
    let x = new_var "_x" in
    let t = mk_int_range 0 10 in
    (!solver)#set_need_model true;
    (!solver)#append_var_def x t;
    let e = BinEx (EQ, Var x, Const 1) in
    ignore ((!solver)#append_expr e);
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true;
    let query = (!solver)#get_model_query in
    assert_equal Q.Cached (Q.try_get query (Var x)) ~msg:"Cached expected";
    let query = (!solver)#submit_query query in
    let res = Q.try_get query (Var x) in
    assert_equal (Q.Result (Const 1)) res
        ~msg:(sprintf "(Const 1) expected, found %s"
            (Q.query_result_s query res))


let test_get_model_array _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    t#set_nelems 3;
    (!solver)#set_need_model true;
    (!solver)#append_var_def x t;
    let arr_acc i = BinEx (ARR_ACCESS, Var x, Const i) in
    let arr_upd i j = BinEx (EQ, arr_acc i, Const j) in
    Enum.iter (fun i -> ignore ((!solver)#append_expr (arr_upd i (1 + i)))) (0--2);
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true;

    let query = (!solver)#get_model_query in
    let assert_cached i =
        let res = Q.try_get query (arr_acc i) in
        assert_equal Q.Cached res ~msg:(sprintf "Cached expected for %d" i)
    in
    Enum.iter assert_cached (0--2);

    let query = (!solver)#submit_query query in

    let assert_result i =
        let res = Q.try_get query (arr_acc i) in
        let exp = Q.Result (Const (1 + i)) in
        if exp <> res
        then Q.print_contents query;
        assert_equal exp res
            ~msg:(sprintf "%s expected, found %s"
                           (Q.query_result_s query exp)
                           (Q.query_result_s query res))
    in
    Enum.iter assert_result (0--2)


let test_get_model_array_copy _ =
    let x = new_var "x" in
    let y = new_var "y" in
    let t = mk_int_range 0 10 in
    t#set_nelems 3;
    (!solver)#set_need_model true;
    (!solver)#append_var_def x t;
    (!solver)#append_var_def y t;
    let arr_acc v i = BinEx (ARR_ACCESS, Var v, Const i) in
    let arr_upd v i j = BinEx (EQ, arr_acc v i, Const j) in
    Enum.iter (fun i -> ignore ((!solver)#append_expr (arr_upd x i (1 + i)))) (0--2);
    let append_arr i =
        ignore ((!solver)#append_expr (BinEx (EQ, arr_acc x i, arr_acc y i)))
    in
    Enum.iter append_arr (0--2);
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true;

    let query = (!solver)#get_model_query in
    let assert_cached v i =
        let res = Q.try_get query (arr_acc v i) in
        assert_equal Q.Cached res ~msg:(sprintf "Cached expected for %d" i)
    in
    Enum.iter (assert_cached x) (0--2);
    Enum.iter (assert_cached y) (0--2);

    let query = (!solver)#submit_query query in

    let assert_result v i =
        let res = Q.try_get query (arr_acc v i) in
        let exp = Q.Result (Const (1 + i)) in
        if exp <> res
        then Q.print_contents query;
        assert_equal exp res
            ~msg:(sprintf "%s expected, found %s"
                    (Q.query_result_s query exp) (Q.query_result_s query res))
    in
    Enum.iter (assert_result x) (0--2);
    Enum.iter (assert_result y) (0--2)


let test_model_query_try_get _ =
    let x = new_var "x" in
    let t = mk_int_range 0 10 in
    (!solver)#set_need_model true;
    (!solver)#append_var_def x t;
    let e = BinEx (EQ, Var x, Const 1) in
    ignore ((!solver)#append_expr e);
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true;
    
    let query = (!solver)#get_model_query in
    let res = Q.try_get query (Var x) in
    assert_equal ~msg:"Q.Cached expected" res Q.Cached;

    let query = (!solver)#submit_query query in

    let res = Q.try_get query (Var x) in
    assert_equal ~msg:"Q.Result (Const 1) expected" res (Q.Result (Const 1))


let test_model_query_try_get_not_found _ =
    (!solver)#set_need_model true;
    let res = (!solver)#check in
    assert_equal ~msg:"sat expected" res true;

    let query = (!solver)#get_model_query in
    (* y was never passed to the solver *)
    let y = new_var "y" in
    let res = Q.try_get query (Var y) in
    assert_equal ~msg:"Q.Cached expected" res Q.Cached;

    try
        let new_query = (!solver)#submit_query query in
        let _ = Q.try_get new_query (Var y) in
        assert_failure ("expected Smt_error")
    with Smt_error _ ->
        () (* fine *)


let suite = "smt-suite" >:::
    [
        (***************** Yices 1.x **********************)
        "test_trivial_sat_yices"
			>:: (bracket setup_yices test_trivial_sat reset_yices);
        "test_trivial_unsat_yices"
			>:: (bracket setup_yices test_trivial_unsat reset_yices);
        "test_reset_yices"
			>:: (bracket setup_yices test_reset reset_yices);
        "test_comment_yices"
			>:: (bracket setup_yices test_comment reset_yices);
        "test_append_var_def_yices"
			>:: (bracket setup_yices test_append_var_def reset_yices);
        "test_append_var_def_array_yices"
			>:: (bracket setup_yices test_append_var_def_array reset_yices);
        "test_append_expr_yices"
			>:: (bracket setup_yices test_append_expr reset_yices);
        "test_push_ctx_yices"
			>:: (bracket setup_yices test_push_ctx reset_yices);
        "test_pop_ctx_yices"
			>:: (bracket setup_yices test_pop_ctx reset_yices);
        "test_get_stack_level_yices"
            >:: (bracket setup_yices test_get_stack_level reset_yices);
        "test_get_unsat_cores_yices"
            >:: (bracket setup_yices test_get_unsat_cores reset_yices);
        "test_get_model_one_var_yices"
            >:: (bracket setup_yices test_get_model_one_var reset_yices);
        "test_get_model_array_yices"
            >:: (bracket setup_yices test_get_model_array reset_yices);
        "test_get_model_var_with_underscore_yices"
            >:: (bracket setup_yices test_get_model_var_with_underscore reset_yices);
        "test_get_model_array_copy_yices"
            >:: (bracket setup_yices test_get_model_array_copy reset_yices);
        "test_model_query_try_get_yices"
            >:: (bracket setup_yices test_model_query_try_get reset_yices);
        "test_model_query_try_get_not_found_yices"
            >:: (bracket setup_yices test_model_query_try_get_not_found shutdown_yices (* clean the room *));
        "test_wrong_solver_yices"
			>:: test_wrong_solver;

        (***************** Z3 **********************)
        "test_trivial_sat_smt2"
			>:: (bracket setup_smt2 test_trivial_sat reset_smt2);
        "test_trivial_unsat_smt2"
			>:: (bracket setup_smt2 test_trivial_unsat reset_smt2);
        "test_reset_smt2"
			>:: (bracket setup_smt2 test_reset reset_smt2);
        "test_comment_smt2"
			>:: (bracket setup_smt2 test_comment reset_smt2);
        "test_append_var_def_smt2"
			>:: (bracket setup_smt2 test_append_var_def reset_smt2);
        "test_append_var_def_array_smt2"
			>:: (bracket setup_smt2 test_append_var_def_array reset_smt2);
        "test_append_expr_smt2"
			>:: (bracket setup_smt2 test_append_expr reset_smt2);
        "test_push_ctx_smt2"
			>:: (bracket setup_smt2 test_push_ctx reset_smt2);
        "test_pop_ctx_smt2"
			>:: (bracket setup_smt2 test_pop_ctx reset_smt2);
        "test_get_stack_level_smt2"
            >:: (bracket setup_smt2 test_get_stack_level reset_smt2);
        "test_get_unsat_cores_smt2"
            >:: (bracket setup_smt2 test_get_unsat_cores reset_smt2);
        "test_get_model_one_var_smt2"
            >:: (bracket setup_smt2 test_get_model_one_var reset_smt2);
        "test_get_model_array_smt2"
            >:: (bracket setup_yices test_get_model_array reset_yices);
        "test_get_model_var_with_underscore_smt2"
            >:: (bracket setup_yices test_get_model_var_with_underscore reset_yices);
        "test_get_model_array_copy_smt2"
            >:: (bracket setup_yices test_get_model_array_copy reset_yices);
        "test_model_query_try_get_smt2"
            >:: (bracket setup_yices test_model_query_try_get reset_yices);
        "test_model_query_try_get_not_found_smt2"
            >:: (bracket setup_yices test_model_query_try_get_not_found reset_yices);
        (* this test shutdowns the solver! *)
        "test_trivial_sat_smt2"
			>:: (bracket setup_smt2 test_trivial_sat shutdown_smt2);
    ]

