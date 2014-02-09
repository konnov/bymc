(* This is the place where the different plugin chains are created and executed.
  There is no reason anymore why it is called abstract.ml.

  TODO: rename it to pipeline.ml?

  Igor Konnov, 2012-2014

*)

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
open PiaCtrRefinement
open Runtime
open Simplif
open Smt
open Spin
open SpinIrImp
open VarRole
open Writer

open NusmvPass
open NusmvCounterClusterPass

open Debug

let serialization_filename = "bymc.ser"

let load_game (filename: string) (rt: Runtime.runtime_t)
        : plugin_chain_t =
    log INFO (sprintf "loading game from %s..." filename);
    let cin = open_in_bin filename in
    let m = "\nERROR: The saved state seems to be incompatible."
        ^ " Did you recompile the tool?\n\n" in
    let (seq_id: int) = Marshal.from_channel cin in
    let (chain: plugin_chain_t) =
        try Marshal.from_channel cin
        with Failure e -> fprintf stderr "%s" m; raise (Failure e)
    in
    close_in cin;
    SpinIr.uniq_id_next := seq_id; (* unique id sequence used everywhere *)
    chain#update_runtime rt;
    chain


let save_game (filename: string) (chain: plugin_chain_t) =
    log INFO (sprintf "saving game to %s..." filename);
    let cout = open_out_bin filename in
    Marshal.to_channel cout !SpinIr.uniq_id_next []; (* keep the id sequence *)
    Marshal.to_channel cout chain [Marshal.Closures];
    close_out cout


(* transform the input as prescribed by the chain *)
let do_abstraction rt chain =
    rt#solver#push_ctx;
    rt#solver#comment "do_abstraction";
    begin
        try ignore (chain#transform rt Program.empty)
        with InputRequired s ->
            printf "InputRequired: %s\n" s;
            printf "(create the required input and continue)\n"
    end;
    rt#solver#pop_ctx;
    save_game serialization_filename chain;
    chain#get_output


(* counter abstraction refinement *)
let do_refine rt =
    let chain = load_game serialization_filename rt in
    let (status, _) = chain#refine rt ([], []) in
    save_game serialization_filename chain;
    log INFO (if status
        then "(status trace-refined)"
        else "(status trace-no-refinement)")

