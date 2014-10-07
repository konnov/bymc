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


let solver = ref (new yices_smt "yices")
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
    let opts = Options.empty in
    let inp = BatIO.input_string text in
    let cin = BatIO.to_input_channel inp in
    let prog, _ = Parse.parse_promela_of_chan opts cin "input" "." in
    let caches = new Infra.pass_caches opts (new Infra.analysis_cache) in
    let rt = new Runtime.runtime_t !(solver) caches in
    let proc = List.hd (Program.get_procs prog) in
    rt#caches#set_struc prog (SkelStruc.compute_struc prog);
    rt#caches#analysis#set_var_roles prog (VarRole.identify_var_roles prog);

    (* the show starts here *)
    let sk, _ = Summary.summarize rt prog proc in
    (* Sk.print stdout sk; *)
    assert_equal 7 sk.Sk.nlocs
        ~msg:(sprintf "expected 7 locations, found %d" sk.Sk.nlocs);
    assert_equal 5 sk.Sk.nrules
        ~msg:(sprintf "expected 5 rules, found %d" sk.Sk.nrules);
    let ninits = List.length sk.Sk.inits in
    assert_equal 8 ninits
        ~msg:(sprintf "expected 8 init expression, found %d" ninits);

    assert_failure "nothing implemented"


let suite = "summary-suite" >:::
    [
        "test_summary"
          >:: (bracket setup test_summary shutdown); (* clean the room *)
    ]

