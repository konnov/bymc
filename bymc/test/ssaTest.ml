open OUnit
open Printf

open Accums
open Cfg
open Smt
open Spin
open SpinIr
open SpinIrImp
open Ssa

let marks = Hashtbl.create 10

let mk_var v i =
    try Hashtbl.find marks (v#id, i)
    with Not_found ->
        let nv = v#copy v#get_name in
        nv#set_mark i;
        Hashtbl.replace marks (v#id, i) nv;
        nv

let mk_entry v =
    let bb = new basic_block in
    bb#set_seq [Label (fresh_id (), 0)];
    bb

let mk_bb v lab lhs rhs =
    let phi = Phi (mk_var v lhs, List.map (mk_var v) rhs) in
    let bb = new basic_block in
    bb#set_seq [Label (fresh_id (), lab); Expr (fresh_id (), phi)];
    bb


let setup _ =
    Hashtbl.clear marks


let teardown _ =
    ()


let test_optimize_ssa1 _ =
    let x = new_var "x" in
    let entry = mk_entry x in
    let b1 = mk_bb x 1 4 [1] in
    b1#set_seq (Label (fresh_id (), 1)
        :: [Expr (fresh_id (), BinEx (ASGN, Var (mk_var x 4), Const 1))]);
    let b2 = mk_bb x 2 4 [1] in
    b2#set_seq (Label (fresh_id (), 1)
        :: [Expr (fresh_id (), BinEx (ASGN, Var (mk_var x 4), Const 2))]);
    let b3 = mk_bb x 3 3 [4] in
    let b4 = mk_bb x 4 6 [4] in
    b4#set_seq (b4#get_seq
        @ [Expr (fresh_id (), BinEx (ASGN, Var (mk_var x 3), Const 3))]);
    let b5 = mk_bb x 5 2 [3] in
    let b6 = mk_bb x 6 2 [3] in
    let b7 = mk_bb x 7 5 [2] in
    let b8 = mk_bb x 8 5 [2] in
    let exit = mk_bb x 9 Ssa.mark_out [5] in
    (* connect the blocks *)
    entry#set_succ_sync [b1; b2];
    b1#set_succ_sync [b3; b4];
    b2#set_succ_sync [b3; b4];
    b3#set_succ_sync [b5; b6];
    b4#set_succ_sync [b5; b6];
    b5#set_succ_sync [b7; b8];
    b6#set_succ_sync [b7; b8];
    b7#set_succ_sync [exit];
    b8#set_succ_sync [exit];

    let cfg = new control_flow_graph entry
            [b5; b7; exit; b1; b8; b6; b3; entry; b2; b4]
    in
    ignore (optimize_ssa cfg);
    let expect_no_phi b =
        match b#get_seq with
        | [Label (_, _); Skip _] ->
            () (* ok *)
        | _ -> raise (Failure ("expected no phi"))
    in
    List.iter expect_no_phi [b3; b5; b6; b7; b8];
    let expect_asgn b i =
        match b#get_seq with
        | [Label (_, _); Skip _;
                Expr (_, BinEx (ASGN, Var lhs, Const i))] ->
            assert_equal
                ~msg:(sprintf "expected x_OUT = i, found %d" lhs#mark)
                lhs#mark Ssa.mark_out
        | _ -> raise (Failure ("expected label; skip; assign"))
    in
    expect_asgn b4 3;
    expect_asgn b1 1;
    expect_asgn b2 2


let test_reduce_indices1 _ =
    let x = new_var "x" in
    let entry = mk_entry x in
    let b1 = mk_bb x 1 2 [1] in
    let b2 = mk_bb x 2 3 [1] in
    let exit = mk_bb x 8 Ssa.mark_out [2; 3] in
    (* connect the blocks *)
    entry#set_succ_sync [b1; b2];
    b1#set_succ_sync [exit];
    b2#set_succ_sync [exit];

    let cfg =
        new control_flow_graph entry [b1; entry; exit; b2]
    in
    let bcfg = cfg#as_block_graph in
    ignore (BlockGO.add_transitive_closure ~reflexive:false bcfg);
    let solver = new yices_smt in
    solver#start;
    ignore (reduce_indices solver bcfg x);
    ignore (solver#stop);
    begin
        match b1#get_seq with
        | [Label (_, _); Expr (_, Phi (lhs, rhs))] ->
            assert_equal ~msg:"b1: lhs#mark = 1" lhs#mark 1
        | _ -> raise (Failure ("expected phi"))
    end;
    begin
        match b2#get_seq with
        | [Label (_, _); Expr (_, Phi (lhs, rhs))] ->
            assert_equal ~msg:"b2: lhs#mark = 1" lhs#mark 1
        | _ -> raise (Failure ("expected phi"))
    end;
    begin
        match exit#get_seq with
        | [Label (_, _); Expr (_, Phi (lhs, rhs))] ->
                assert_equal ~msg:"exit: lhs#mark = mark_out"
                    lhs#mark Ssa.mark_out;
                if not ((List.map (fun v -> v#mark) rhs) = [1; 1])
                then printf "exit: rhs = %s\n"
                    (str_join "; "
                        (List.map (fun v -> string_of_int v#mark) rhs));
                assert_equal ~msg:"exit: rhs marks = [1; 1]"
                    (List.map (fun v -> v#mark) rhs) [1; 1];
        | _ -> raise (Failure ("unexpected sequence in exit: "
            ^ (str_join "; " (List.map stmt_s exit#get_seq))))
    end

let suite = "ssa-suite" >:::
    [
        "test_optimize_ssa1"
            >:: (bracket setup test_optimize_ssa1 teardown);
        "test_reduce_indices1"
            >:: (bracket setup test_reduce_indices1 teardown)
    ]

