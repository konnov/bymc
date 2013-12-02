open OUnit
open Printf

open AbsCounter
open Accums
open Cfg
open Debug
open PiaDom
open PiaCtrCtx
open Smt
open Spin
open SpinIr
open SpinIrImp
open Ssa
open VarRole


let solver = ref (new yices_smt)

let setup _ =
    initialize_debug {
        Options.empty with
          Options.plugin_opts = (StringMap.singleton "trace.mods" "cmd")
    };
    !solver#start

let teardown _ =
    ignore (!solver#stop)


let test_trans_proc_decl_two_var _ =
    (* setup *)
    let nsnt = new_var "nsnt"
        and pc = new_var "pc" and npc = new_var "npc"
        and rx = new_var "rx" and nrx = new_var "nrx"
        and spur = new_var "spar" in
    pc#set_proc_name "Proc";
    npc#set_proc_name "Proc";
    rx#set_proc_name "Proc";
    nrx#set_proc_name "Proc";
    (* {0, 1, many}-abstraction *)
    let dom = new pia_domain [Const 0; Const 1; Const 2] in 
    let h = Hashtbl.create 4 in
    Hashtbl.add h pc (BoundedInt (0, 2));
    Hashtbl.add h npc (Scratch(pc));
    Hashtbl.add h rx (LocalUnbounded);
    Hashtbl.add h nrx (Scratch(rx));
    let roles = new var_role_tbl h in

    let proc = new proc "Proc" (Const 10) in
    proc#set_stmts [
        MDecl (1, pc, Const 0);
        MDecl (2, npc, Const 0);
        MDecl (3, rx, Const 0);
        MDecl (4, nrx, Const 0);
        MLabel (10, 1);
        MAtomic (20, [
            MExpr (21, BinEx (ASGN, Var npc, Const 1));
            MExpr (22, BinEx (ASGN, Var pc, Var npc));
            MExpr (23, BinEx (ASGN, Var rx, Var nrx));
            MExpr (24, BinEx (ASGN, Var npc, Const 0));
            MExpr (25, BinEx (ASGN, Var nrx, Const 0));
        ]);
        MGoto (30, 1);
    ];
    let tt = new data_type_tab in
    tt#set_type pc (mk_int_range 0 2);
    tt#set_type npc (mk_int_range 0 2);
    tt#set_type rx (mk_int_range 0 3);
    tt#set_type nrx (mk_int_range 0 3);
    tt#set_type nsnt (mk_int_range 0 3);
    let prog = Program.program_of_units tt
        [
            Stmt (MDecl (fresh_id (), nsnt, Const 0));
            Proc (proc)
        ]
    in
    let pia_ctx = new ctr_abs_ctx dom roles spur proc "P" in
    let pia_ctx_tab = new ctr_abs_ctx_tbl dom roles prog [proc] in

    (* test *)
    let prop = PropSome (BinEx (AND,
        BinEx (EQ, Var pc, Const 2), BinEx (EQ, Var rx, Const 1))) in
    let abs_prop = trans_prop_decl !solver pia_ctx_tab prog prop in
    match abs_prop with
    | PropGlob p ->
        assert_equal
            ~msg:("expected (bymc_kP[7] != 0), found: " ^ (expr_s p))
            "(bymc_kP[7] != 0)" (expr_s p)
    | _ -> assert_failure "expected PropGlob"


let test_trans_proc_decl_three_var _ =
    (* setup *)
    let nsnt = new_var "nsnt"
        and pc = new_var "pc" and npc = new_var "npc"
        and flt = new_var "flt" and nflt = new_var "nflt"
        and rx = new_var "rx" and nrx = new_var "nrx"
        and spur = new_var "spar" in
    pc#set_proc_name "Proc";
    npc#set_proc_name "Proc";
    rx#set_proc_name "Proc";
    nrx#set_proc_name "Proc";
    (* {0, 1, many}-abstraction *)
    let dom = new pia_domain [Const 0; Const 1; Const 2] in 
    let h = Hashtbl.create 4 in
    Hashtbl.add h pc (BoundedInt (0, 2));
    Hashtbl.add h npc (Scratch(pc));
    Hashtbl.add h rx (LocalUnbounded);
    Hashtbl.add h nrx (Scratch(rx));
    Hashtbl.add h flt (BoundedInt (0, 1));
    Hashtbl.add h nflt (Scratch(flt));
    let roles = new var_role_tbl h in

    let proc = new proc "Proc" (Const 10) in
    proc#set_stmts [
        MDecl (1, pc, Const 0);
        MDecl (2, npc, Const 0);
        MDecl (3, rx, Const 0);
        MDecl (4, nrx, Const 0);
        MDecl (5, flt, Const 0);
        MDecl (6, nflt, Const 0);
        MLabel (10, 1);
        MAtomic (20, [
            MExpr (21, BinEx (ASGN, Var npc, Const 1));
            MExpr (22, BinEx (ASGN, Var pc, Var npc));
            MExpr (23, BinEx (ASGN, Var rx, Var nrx));
            MExpr (24, BinEx (ASGN, Var flt, Var nflt));
            MExpr (25, BinEx (ASGN, Var npc, Const 0));
            MExpr (26, BinEx (ASGN, Var nrx, Const 0));
            MExpr (27, BinEx (ASGN, Var nflt, Const 0));
        ]);
        MGoto (30, 1);
    ];
    let tt = new data_type_tab in
    tt#set_type pc (mk_int_range 0 2);
    tt#set_type npc (mk_int_range 0 2);
    tt#set_type rx (mk_int_range 0 3);
    tt#set_type nrx (mk_int_range 0 3);
    tt#set_type flt (mk_int_range 0 2);
    tt#set_type nflt (mk_int_range 0 2);
    tt#set_type nsnt (mk_int_range 0 3);
    let prog = Program.program_of_units tt
        [
            Stmt (MDecl (fresh_id (), nsnt, Const 0));
            Proc (proc)
        ]
    in
    let pia_ctx = new ctr_abs_ctx dom roles spur proc "P" in
    let pia_ctx_tab = new ctr_abs_ctx_tbl dom roles prog [proc] in

    (* test *)
    let prop = PropSome (list_to_binex AND
        [BinEx (EQ, Var pc, Const 2);
         BinEx (EQ, Var rx, Const 1);
         BinEx (EQ, Var flt, Const 1)
    ]) in
    let abs_prop = trans_prop_decl !solver pia_ctx_tab prog prop in
    match abs_prop with
    | PropGlob p ->
        assert_equal
            ~msg:("expected (bymc_kP[16] != 0), found: " ^ (expr_s p))
            "(bymc_kP[16] != 0)" (expr_s p)
    | _ -> assert_failure "expected PropGlob"


let suite = "ssa-suite" >:::
    [
        "test_trans_proc_decl_two_var"
          >:: (bracket setup test_trans_proc_decl_two_var teardown);
        "test_trans_proc_decl_three_var"
          >:: (bracket setup test_trans_proc_decl_three_var teardown);
    ]

