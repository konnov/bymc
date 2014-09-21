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


let compare_used_vars used_set exp_ios exp_temps =
    let nused = StrSet.cardinal used_set in
    assert_equal ~msg:(sprintf "|used_set| = %d != %d"
        nused (exp_temps + exp_ios))
        (exp_temps + exp_ios) nused;
    let check s (n_io, n_t) =
        if "_IN" = (Str.last_chars s 3) || "_OUT" = (Str.last_chars s 4)
        then (n_io + 1, n_t)
        else (n_io, n_t + 1)
    in
    let n_io, n_t = StrSet.fold check used_set (0, 0) in
    assert_equal ~msg:(sprintf "nr. IN/OUT = %d" exp_ios) exp_ios n_io;
    assert_equal ~msg:(sprintf "nr. temporaries = %d" exp_temps) exp_temps n_t


(* the scary bug I came up with on Nov 28, 2013 *)
let test_optimize_ssa_in_out _ =
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
    ignore (optimize_ssa cfg [x]);

    let expect_no_phi b =
        match b#get_seq with
        | [Label (_, _)] ->
            () (* ok *)
        | _ -> assert_failure
          (sprintf "unexpected sequence in %d: %s" b#label
            (str_join "; " (List.map stmt_s b#get_seq)))
    in
    List.iter expect_no_phi [b5; b6; b7; b8];
    let expect_phi_asgn b expect_lhs expect_rhs =
        match b#get_seq with
        | [Label (_, _);
                Expr (_, BinEx (ASGN, Var lhs, Var rhs))] ->
            assert_equal
                ~msg:(sprintf "expected x_T%d = x_T%d, found %d, %d"
                    expect_lhs expect_rhs lhs#mark rhs#mark)
                expect_lhs lhs#mark;
            assert_equal
                ~msg:(sprintf "expected x_T%d = x_T%d, found %d, %d"
                    expect_lhs expect_rhs lhs#mark rhs#mark)
                expect_rhs rhs#mark
        | _ as seq ->
            assert_failure
                (sprintf "unexpected sequence at %d: %s"
                    b#label (str_join "; " (List.map stmt_s seq)))
    in
    expect_phi_asgn b3 Ssa.mark_out 4;
    let expect_skip_asgn b i =
        match b#get_seq with
        | [Label (_, _);
                Expr (_, BinEx (ASGN, Var lhs, Const i))] ->
            assert_equal
                ~msg:(sprintf "expected x_OUT = i, found %d" lhs#mark)
                lhs#mark Ssa.mark_out
        | _ as seq ->
            assert_failure
                (sprintf "expected label in block %d; assign, found: %s"
                    b#label (str_join "; " (List.map stmt_s seq)))
    in
    expect_skip_asgn b4 3;
    let expect_asgn b i =
        match b#get_seq with
        | [Label (_, _); Expr (_, BinEx (ASGN, Var lhs, Const i))] ->
            assert_bool
                (sprintf "expected x_j = i and j <> OUT, found %d" lhs#mark)
                (lhs#mark <> Ssa.mark_out)
        | _ as seq ->
            assert_failure
                (sprintf "expected label in block %d; assign, found: %s"
                    b#label (str_join "; " (List.map stmt_s seq)))
    in
    expect_asgn b1 1;
    expect_asgn b2 2


(* the coloring works as expected on diamonds *)
let test_reduce_indices_diamond _ =
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
    ignore (reduce_indices solver (Ssa.BlockGasM.make bcfg) x);
    ignore (solver#stop);
    begin
        match b1#get_seq with
        | [Label (_, _); Expr (_, Phi (lhs, rhs))] ->
            assert_equal ~msg:"b1: lhs#mark = 1" lhs#mark 1
        | _ -> assert_failure ("expected phi")
    end;
    begin
        match b2#get_seq with
        | [Label (_, _); Expr (_, Phi (lhs, rhs))] ->
            assert_equal ~msg:"b2: lhs#mark = 1" lhs#mark 1
        | _ -> assert_failure ("expected phi")
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
        | _ -> assert_failure ("unexpected sequence in exit: "
            ^ (str_join "; " (List.map stmt_s exit#get_seq)))
    end


let test_mk_ssa _ =
    let x = new_var "x" in
    let id _ = fresh_id () in
    (* this code is very similar to next_nrcvd in bcast-byz.pml *)
    let code =
        MIf (fresh_id (), [
            MOptGuarded[ MExpr (id(), BinEx (EQ, Var x, Const 0)) ];
            MOptGuarded[ MExpr (id(), BinEx (NE, Var x, Const 1)) ];
        ])
        ::
        MIf (fresh_id (), [
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 0)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 1)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 2)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 3)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 4)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 5)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 6)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 7)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 8)) ];
        ])
        ::
        MIf (fresh_id (), [
            MOptGuarded[
                MExpr (id(), BinEx (EQ, Var x, Const 0));
                MExpr (id(), BinEx (ASGN, Var x, Const 5))
            ];
            MOptGuarded[ MExpr (id(), BinEx (NE, Var x, Const 1)) ];
        ])
        ::
        MIf (fresh_id (), [
            MOptGuarded[ MExpr (id(), BinEx (EQ, Var x, Const 3)) ];
            MOptGuarded[ MExpr (id(), BinEx (EQ, Var x, Const 2)) ];
            MOptGuarded[ MExpr (id(), BinEx (EQ, Var x, Const 1)) ];
        ])
        ::
        MIf (fresh_id (), [
            MOptGuarded[ MExpr (id(), BinEx (EQ, Var x, Const 3)) ];
            MOptGuarded[
                MExpr (id(), BinEx (EQ, Var x, Const 4));
                MIf (fresh_id (), [
                    MOptGuarded [ MSkip (id ()) ];
                    MOptGuarded [ MSkip (id ()) ];
                    MOptGuarded [ MSkip (id ()) ]
                ])
            ];
        ])
        :: []
    in
    let cfg = Cfg.remove_ineffective_blocks (mk_cfg (mir_to_lir code))
    in
    Cfg.write_dot "ssa-test-in.dot" cfg;

    let nst = new symb_tab "" in
    let ntt = new data_type_tab in
    ntt#set_type x (mk_int_range 0 9);
    let solver = new yices_smt in
    solver#start;
    let cfg_ssa = mk_ssa solver false [x] [] nst ntt cfg in
    ignore (solver#stop);
    Cfg.write_dot "ssa-test-out.dot" cfg_ssa;
    let collect us b =
        let used = stmt_list_used_vars b#get_seq in
        List.fold_left (fun s v -> StrSet.add v#get_name s) us used
    in
    let used_set =
        List.fold_left collect StrSet.empty cfg_ssa#block_list
    in
    (* Previously, we had two temporary variables.
       For some reason, now it is one, which is also correct.
    *)
    compare_used_vars used_set 2 1


(* Bugfix on 4.12.13: havoc must always introduce a new variable
   (re-coloring eliminated them somewhere).
 *)
let test_mk_ssa_havoc _ =
    let x = new_var "x" in
    let id _ = fresh_id () in
    (* this code is very similar to next_nrcvd in bcast-byz.pml *)
    let code =
        MIf (fresh_id (), [
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 0)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 1)) ];
        ])
        ::
        MHavoc (fresh_id (), x)
        ::
        MIf (fresh_id (), [
            MOptGuarded[ MExpr (id(), BinEx (EQ, Var x, Const 0)) ];
            MOptGuarded[ MExpr (id(), BinEx (EQ, Var x, Const 1)) ];
        ])
        ::
        MIf (fresh_id (), [
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 2)) ];
            MOptGuarded[ MExpr (id(), BinEx (ASGN, Var x, Const 3)) ];
        ])
        :: []
    in
    let cfg = Cfg.remove_ineffective_blocks (mk_cfg (mir_to_lir code))
    in
    let nst = new symb_tab "" in
    let ntt = new data_type_tab in
    ntt#set_type x (mk_int_range 0 4);
    let solver = new yices_smt in
    solver#start;
    let cfg_ssa = mk_ssa solver false [x] [] nst ntt cfg in
    ignore (solver#stop);
    Cfg.write_dot "ssa-test-havoc.dot" cfg_ssa;
    let collect us b =
        let used = stmt_list_used_vars b#get_seq in
        List.fold_left (fun s v -> StrSet.add v#get_name s) us used
    in
    let used_set =
        List.fold_left collect StrSet.empty cfg_ssa#block_list
    in
    compare_used_vars used_set 1 2


let suite = "ssa-suite" >:::
    [
        "test_optimize_ssa_in_out"
            >:: (bracket setup test_optimize_ssa_in_out teardown);
        "test_reduce_indices_diamond"
            >:: (bracket setup test_reduce_indices_diamond teardown);
        "test_mk_ssa"
            >:: (bracket setup test_mk_ssa teardown);
        "test_mk_ssa_havoc"
            >:: (bracket setup test_mk_ssa_havoc teardown)
    ]

