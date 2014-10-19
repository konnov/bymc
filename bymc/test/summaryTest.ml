open OUnit
open Printf

open Accums
open Cfg
open Debug
open PiaDom
open PiaCtrCtx
open Smt
open Spin
open SpinIr
open SpinIrImp
open SymbSkel
open Ssa
open VarRole


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


let parse text =
    let opts = Options.empty in
    let inp = BatIO.input_string text in
    let cin = BatIO.to_input_channel inp in
    let prog, _ = Parse.parse_promela_of_chan opts cin "input" "." in
    let caches = new Infra.pass_caches opts (new Infra.analysis_cache) in
    let rt = new Runtime.runtime_t !(solver) caches in
    let proc = List.hd (Program.get_procs prog) in
    rt#caches#set_struc prog (SkelStruc.compute_struc prog);
    rt#caches#analysis#set_var_roles prog (VarRole.identify_var_roles prog);
    rt, prog, proc


let test_summary _ =
    let text =
        "symbolic int N; int nsnt;\n" ^
        "assume (N > 1);\n" ^
        "active[N] proctype Foo() {\n" ^
        "  byte pc:1 = 0; int nrcvd:2 = 0;\n" ^
        "  byte npc:1 = 0; int nnrcvd:2 = 0;\n" ^
        "  do :: atomic {\n" ^
        "    if :: pc == 0 -> npc = 1;\n" ^
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && nnrcvd == 1 && nsnt >= 2) || (nrcvd == 1 && nnrcvd == 2 && nsnt >= 4));\n" ^
        "       nsnt++;\n" ^ 
        "       :: pc == 1;\n" ^ 
        "    fi;\n" ^
        "    if :: pc == 1 -> npc = 0;\n" ^
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && nnrcvd == 1 && nsnt >= 2) || (nrcvd == 1 && nnrcvd == 2 && nsnt >= 4) || (nrcvd == 2 && nnrcvd == 3 && nsnt >= 6));\n" ^
        "       :: pc == 0;\n" ^ 
        "    fi;\n" ^
        "    nrcvd = nnrcvd; pc = npc;\n" ^
        "    nnrcvd = 0; npc = 0;\n" ^
        "  } od;\n" ^
        "}"
    in
    let rt, prog, proc = parse text in

    (* the show starts here *)
    let sk = Summary.summarize rt prog proc in
    (* Sk.print stdout sk; *)
    assert_equal 7 sk.Sk.nlocs
        ~msg:(sprintf "expected 7 locations, found %d" sk.Sk.nlocs);
    assert_equal 5 sk.Sk.nrules
        ~msg:(sprintf "expected 5 rules, found %d" sk.Sk.nrules);
    let ninits = List.length sk.Sk.inits in
    assert_equal 8 ninits
        ~msg:(sprintf "expected 8 init expression, found %d" ninits)


let test_summary_unfold _ =
    let text =
        "symbolic int N; int nsnt;\n" ^
        "assume (N > 1);\n" ^
        "active[N] proctype Foo() {\n" ^
        "  byte pc:1 = 0; int nrcvd:2 = 0;\n" ^
        "  byte npc:1 = 0; int nnrcvd:2 = 0;\n" ^
        "  do :: atomic {\n" ^
        "    if :: pc == 0 -> npc = 1;\n" ^
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && nnrcvd == 1 && nsnt >= 2));\n" ^
        "       nsnt++;\n" ^ 
        "       :: npc = pc;\n" ^ 
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && nnrcvd == 1 && nsnt >= 2));\n" ^
        "    fi;\n" ^
        "    nrcvd = nnrcvd; pc = npc;\n" ^
        "    nnrcvd = 0; npc = 0;\n" ^
        "  } od;\n" ^
        "}"
    in
    let rt, prog, proc = parse text in

    let t = Program.get_type prog ((proc#lookup "pc")#as_var) in
    let l, r = t#range in
    assert_equal 0 l
        ~msg:(sprintf "expected range [0, 2), found [%d, %d)" l r);
    assert_equal 2 r
        ~msg:(sprintf "expected range [0, 2), found [%d, %d)" l r);

    (* the show starts here *)
    let sk = Summary.summarize rt prog proc in
    (* Sk.print stdout sk; *)
    assert_equal 4 sk.Sk.nlocs
        ~msg:(sprintf "expected 4 locations, found %d" sk.Sk.nlocs);
    assert_equal 3 sk.Sk.nrules
        ~msg:(sprintf "expected 3 rules, found %d" sk.Sk.nrules);
    let ninits = List.length sk.Sk.inits in
    assert_equal 5 ninits
        ~msg:(sprintf "expected 5 init expressions, found %d" ninits)


let test_summary_valid _ =
    let text =
        "symbolic int N; int nsnt;\n" ^
        "assume (N > 1);\n" ^
        "active[N] proctype Foo() {\n" ^
        "  byte pc:1 = 0; int nrcvd:2 = 0;\n" ^
        "  byte npc:1 = 0; int nnrcvd:2 = 0;\n" ^
        "  do :: atomic {\n" ^
        "    if :: pc == 0 -> npc = 1;\n" ^
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && nnrcvd == 1));\n" ^
        "       nsnt++;\n" ^ 
        "       :: npc = pc; nnrcvd = nrcvd;\n" ^ 
        "    fi;\n" ^
        "    nrcvd = nnrcvd; pc = npc;\n" ^
        "    nnrcvd = 0; npc = 0;\n" ^
        "  } od;\n" ^
        "}"
    in
    let rt, prog, proc = parse text in

    (* the show starts here *)
    let sk = Summary.summarize rt prog proc in
    (*
    Sk.print stdout sk;
    *)
    assert_equal 8 sk.Sk.nlocs
        ~msg:(sprintf "expected 7 locations, found %d" sk.Sk.nlocs);
    assert_equal 9 sk.Sk.nrules
        ~msg:(sprintf "expected 9 rules, found %d" sk.Sk.nrules);
    let nsnt = (proc#lookup "nsnt")#as_var in
    let exp_inc =
        BinEx (EQ,
            UnEx (NEXT, Var nsnt),
            BinEx (PLUS, Var nsnt, IntConst 1))
    in
    let exp_keep = BinEx (EQ, UnEx (NEXT, Var nsnt), Var nsnt)
    in
    let check_rule r =
        assert_bool ("expected 1, found " ^ (expr_s r.Sk.guard))
                    (is_c_true r.Sk.guard);
        if [ exp_inc ] <> r.Sk.act && [ exp_keep ] <> r.Sk.act
        then
        assert_failure
            (sprintf "expected action [%s] or [%s], found [%s]"
                  (expr_s exp_inc) (expr_s exp_keep)
                  (List.map expr_s r.Sk.act |> str_join "; "));
    in
    List.iter check_rule sk.Sk.rules;

    let ninits = List.length sk.Sk.inits in
    assert_equal 9 ninits
        ~msg:(sprintf "expected 9 init expression, found %d" ninits)


let test_summary_reachable _ =
    let text =
        "symbolic int N; int nsnt;\n" ^
        "assume (N > 1);\n" ^
        "active[N] proctype Foo() {\n" ^
        "  byte pc:1 = 0; int nrcvd:2 = 0;\n" ^
        "  byte npc:1 = 0; int nnrcvd:2 = 0;\n" ^
        "  do :: atomic {\n" ^
        "    if :: pc == 1 -> npc = 0;\n" ^
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && nnrcvd == 1));\n" ^
        "       nsnt++;\n" ^ 
        "       :: npc = pc;\n" ^ 
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && (nnrcvd == 0 || nnrcvd == 1)));\n" ^
        "    fi;\n" ^
        "    nrcvd = nnrcvd; pc = npc;\n" ^
        "    nnrcvd = 0; npc = 0;\n" ^
        "  } od;\n" ^
        "}"
    in
    let rt, prog, proc = parse text in

    (* the show starts here *)
    let sk = Summary.summarize rt prog proc in
    let sk = SymbSkel.keep_reachable sk in
    (*Sk.print stdout sk;*)
    assert_equal 2 sk.Sk.nlocs
        ~msg:(sprintf "expected 2 reachable location, found %d" sk.Sk.nlocs);
    assert_equal 2 (List.length sk.Sk.locs)
        ~msg:(sprintf "expected 2 reachable location, found %d"
            (List.length sk.Sk.locs));
    assert_equal 2 sk.Sk.nrules
        ~msg:(sprintf "expected 2 reachable rule, found %d" sk.Sk.nrules);
    assert_equal 2 (List.length sk.Sk.rules)
        ~msg:(sprintf "expected 2 reachable rule, found %d"
            (List.length sk.Sk.rules));
    assert_equal 2 (IntMap.cardinal sk.Sk.loc_vars)
        ~msg:(sprintf "expected 2 mapped locations, found %d"
            (IntMap.cardinal sk.Sk.loc_vars));
    assert_bool "expected 0 to be in loc_vars" (IntMap.mem 0 sk.Sk.loc_vars);
    assert_bool "expected 1 to be in loc_vars" (IntMap.mem 1 sk.Sk.loc_vars);
    let ninits = List.length sk.Sk.inits in
    assert_equal 3 ninits
        ~msg:(sprintf "expected 3 init expression, found %d" ninits)


let test_summary_inc _ =
    let text =
        "symbolic int N; int nsnt;\n" ^
        "assume (N > 1);\n" ^
        "active[N] proctype Foo() {\n" ^
        "  byte pc:1 = 0; int nrcvd:2 = 0;\n" ^
        "  byte npc:1 = 0; int nnrcvd:2 = 0;\n" ^
        "  do :: atomic {\n" ^
        "    if :: pc == 0 -> npc = 1;\n" ^
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && nnrcvd == 1));\n" ^
        "       nsnt++;\n" ^ 
        "    fi;\n" ^
        "    nrcvd = nnrcvd; pc = npc;\n" ^
        "    nnrcvd = 0; npc = 0;\n" ^
        "  } od;\n" ^
        "}"
    in
    let rt, prog, proc = parse text in
    let nsnt = (proc#lookup "nsnt")#as_var in

    (* the show starts here *)
    let sk = Summary.summarize rt prog proc in
    let sk = SymbSkel.keep_reachable sk in
    (*Sk.print stdout sk;*)
    assert_equal 2 sk.Sk.nlocs
        ~msg:(sprintf "expected 2 reachable location, found %d" sk.Sk.nlocs);
    assert_equal 2 (List.length sk.Sk.locs)
        ~msg:(sprintf "expected 2 reachable location, found %d"
            (List.length sk.Sk.locs));
    assert_equal 1 sk.Sk.nrules
        ~msg:(sprintf "expected 1 reachable rule, found %d" sk.Sk.nrules);
    assert_equal 1 (List.length sk.Sk.rules)
        ~msg:(sprintf "expected 1 reachable rule, found %d"
            (List.length sk.Sk.rules));
    let r = List.hd sk.Sk.rules in
    let exp =
        BinEx (EQ,
            UnEx (NEXT, Var nsnt),
            BinEx (PLUS, Var nsnt, IntConst 1))
    in
    assert_equal [exp] r.Sk.act
        ~msg:(sprintf "expected action [%s], found [%s]"
            (expr_s exp) (List.map expr_s r.Sk.act |> str_join "; "))


let test_summary_keep _ =
    let text =
        "symbolic int N; int nsnt;\n" ^
        "assume (N > 1);\n" ^
        "active[N] proctype Foo() {\n" ^
        "  byte pc:1 = 0; int nrcvd:2 = 0;\n" ^
        "  byte npc:1 = 0; int nnrcvd:2 = 0;\n" ^
        "  do :: atomic {\n" ^
        "    if :: pc == 0 -> npc = 0;\n" ^
        "       havoc(nnrcvd);\n" ^
        "       assume((nrcvd == 0 && nnrcvd == 1));\n" ^
        "       :: pc == 1 -> npc = 1;\n" ^
        "       nnrcvd = nrcvd;\n" ^
        "       nsnt++;\n" ^
        "    fi;\n" ^
        "    nrcvd = nnrcvd; pc = npc;\n" ^
        "    nnrcvd = 0; npc = 0;\n" ^
        "  } od;\n" ^
        "}"
    in
    let rt, prog, proc = parse text in
    let nsnt = (proc#lookup "nsnt")#as_var in

    (* the show starts here *)
    let sk = Summary.summarize rt prog proc in
    let sk = SymbSkel.keep_reachable sk in
    (*Sk.print stdout sk;*)
    assert_equal 2 sk.Sk.nlocs
        ~msg:(sprintf "expected 2 reachable location, found %d" sk.Sk.nlocs);
    assert_equal 2 (List.length sk.Sk.locs)
        ~msg:(sprintf "expected 2 reachable location, found %d"
            (List.length sk.Sk.locs));
    assert_equal 1 sk.Sk.nrules
        ~msg:(sprintf "expected 1 reachable rule, found %d" sk.Sk.nrules);
    assert_equal 1 (List.length sk.Sk.rules)
        ~msg:(sprintf "expected 1 reachable rule, found %d"
            (List.length sk.Sk.rules));
    let r = List.hd sk.Sk.rules in
    let exp = BinEx (EQ, UnEx (NEXT, Var nsnt), Var nsnt)
    in
    assert_equal [exp] r.Sk.act
        ~msg:(sprintf "expected action [%s], found [%s]"
            (expr_s exp) (List.map expr_s r.Sk.act |> str_join "; "))



let suite = "summary-suite" >:::
    [
        "test_summary"
          >:: (bracket setup test_summary teardown);
        "test_summary_unfold"
          >:: (bracket setup test_summary_unfold teardown);
        "test_summary_reachable"
          >:: (bracket setup test_summary_reachable teardown);
        "test_summary_inc"
          >:: (bracket setup test_summary_inc teardown);
        "test_summary_keep"
          >:: (bracket setup test_summary_keep teardown);
        "test_summary_valid"
          >:: (bracket setup test_summary_valid shutdown); (* clean the room *)
    ]

