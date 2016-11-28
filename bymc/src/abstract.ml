(* This is the place where the different plugin chains are created and executed.
  There is no reason anymore why it is called abstract.ml.

  TODO: rename it to pipeline.ml?

  Igor Konnov, 2012-2016

*)

open Printf

open Accums
open AbsInterval
open AbsCounter
open Infra
open Ltl
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

open Debug

let serialization_filename = "bymc.ser"

let load_game (filename: string) (rt: Runtime.runtime_t)
        : plugin_chain_t =
    log INFO (sprintf "loading game from %s..." filename);
    let cin = open_in_bin filename in
    let m = "\nERROR: The saved state seems to be incompatible."
        ^ " Did you recompile the tool?\n\n" in
    SpinIr.load_internal_globals cin;
    let (chain: plugin_chain_t) =
        try Marshal.from_channel cin
        with Failure e -> fprintf stderr "%s" m; raise (Failure e)
    in
    close_in cin;
    chain#update_runtime rt;
    chain


let save_game (filename: string) (chain: plugin_chain_t) =
    log INFO (sprintf "saving game to %s..." filename);
    let cout = open_out_bin filename in
    SpinIr.save_internal_globals cout;
    Marshal.to_channel cout chain [Marshal.Closures];
    close_out cout


(**
  Transform the input as prescribed by the chain.
  This function is intented for use with an external verification tool,
  e.g., Spin or NuSMV. After the translation has been done, the bymc context
  is serialized into a file, which can be read later by do_refine.

  See also abstract_refine_light
 *)
let do_verification rt chain =
    rt#solver#push_ctx;
    rt#solver#comment "do_verification";
    begin
        try ignore (chain#transform rt Program.empty)
        with InputRequired s ->
            printf "InputRequired: %s\n" s;
            printf "(create the required input and continue)\n"
    end;
    rt#solver#pop_ctx;
    save_game serialization_filename chain;
    chain#get_output


(**
  Try to refine the current abstraction by using a counterexample found
  by do_verification, or, more precisely, by an external verification tool.
  As the case with do_verification, this function is intended to work with
  an external verification tool.

  See also abstract_refine_light
 *)
let do_refine rt =
    let chain = load_game serialization_filename rt in
    let (status, _) = chain#refine rt ([], []) in
    save_game serialization_filename chain;
    log INFO (if status
        then "(status trace-refined)"
        else "(status trace-no-refinement)")


(**
  A lightweight abstraction-verification-refinement loop that does not invoke
  an external verification tool.

  See also do_verificaion and do_refine
  *)
let abstract_verify_refine_light rt chain =
    (* XXX: this loop is calling the whole chain every time and thus is parsing
       the whole program every time
       *)
    let rec loop _ =
        log INFO " > VERIFY";
        rt#solver#push_ctx;
        let out = chain#transform rt Program.empty in
        rt#solver#pop_ctx;
        if not (Program.has_bug out)
        then log INFO " > ABSTRACTION/REFINEMENT LOOP FINISHED. DONE."
        else begin
            log INFO " > BUG FOUND. REFINING.";
            rt#solver#push_ctx;
            chain#update_runtime rt;
            let (status, _) = chain#refine rt ([], []) in
            rt#solver#pop_ctx;
            if not status
            then log INFO " > NO REFINEMENT. GIVING UP..."
            else loop ()
        end
    in
    loop ();
    chain#get_output

