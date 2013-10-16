
open Printf

open Accums
open AbsInterval
open AbsCounter
open Infra
open Ltl
open NusmvCmd
open PiaDataCtx
open PiaCtrCtx
open Plugin
open Program
open Refinement
open Runtime
open Simplif
open Smt
open Spin
open SpinCmd
open SpinIr
open SpinIrImp
open VarRole
open Writer

open NusmvPass
open NusmvCounterClusterPass

open Debug

(* the file where the state is saved to *)
let serialization_filename = "bymc.ser"

let load_game rt =
    log INFO "loading game...";
    let cin = open_in_bin serialization_filename in
    let (seq_id: int) = Marshal.from_channel cin in
    let (chain: plugin_chain_t) = Marshal.from_channel cin in
    close_in cin;
    SpinIr.uniq_id_next := seq_id; (* unique id sequence used everywhere *)
    chain#update_runtime rt;
    chain

let save_game chain =
    log INFO "saving game...";
    let cout = open_out_bin serialization_filename in
    Marshal.to_channel cout !SpinIr.uniq_id_next []; (* keep the id sequence *)
    Marshal.to_channel cout chain [Marshal.Closures];
    close_out cout

(* units -> interval abstraction -> counter abstraction *)
let do_abstraction rt =
    rt#solver#push_ctx;
    rt#solver#comment "do_abstraction";
    let chain = new plugin_chain_t in
    chain#add_plugin
        (new PromelaParserPlugin.promela_parser_plugin_t "promelaParser");
    chain#add_plugin (new VarRolePlugin.var_role_plugin_t "varRoles");
    chain#add_plugin (new PiaDomPlugin.pia_dom_plugin_t "piaDom");
    let pia_data_p = new PiaDataPlugin.pia_data_plugin_t "piaData" in
    chain#add_plugin pia_data_p;
    chain#add_plugin (new NusmvPlugin.nusmv_plugin_t "nusmv" "main-int");
    chain#add_plugin (new PiaCounterPlugin.pia_counter_plugin_t
        "piaCounter" pia_data_p);
    chain#add_plugin (new NusmvCtrClusterPlugin.nusmv_ctr_cluster_plugin_t
            "nusmvCounter" "main" pia_data_p);
    chain#add_plugin (new SpinPlugin.spin_plugin_t "spin" "abs-counter");
    let _ = chain#transform rt Program.empty in
    rt#solver#pop_ctx;
    save_game chain;
    chain#get_output


let new_refine rt =
    let chain = load_game rt in
    let (status, _) = chain#refine rt ([], []) in
    save_game chain;
    log INFO (if status
        then "(status trace-refined)"
        else "(status trace-no-refinement)")

