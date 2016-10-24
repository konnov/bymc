(* Here is the place where the standard chains are created.
 *
 * Igor Konnov, 2014
 *)

open Printf

open Options
open Plugin
open Runtime

(*
  Every chain should come with its own module. As the plugins in one
  chain are usually connected, the module has to provide access to
  the plugins. This is the least painful way I have found so far.
 *)


(** FMCAD'13: data + counter abstractions. *)
module Pia = struct
    type plugins_t = {
        pp: PromelaParserPlugin.pp_plugin_t;
        vr: VarRolePlugin.vr_plugin_t;
        pdom: PiaDomPlugin.pia_dom_plugin_t;
        pdg: PiaDataPlugin.pd_plugin_t;
        pd: PiaDataPlugin.pd_plugin_t;
        opt: OptPlugin.opt_plugin_t;
        pc: PiaCounterPlugin.pc_plugin_t;
        nv: NusmvSsaPlugin.nusmv_ssa_plugin_t;
        sn: SpinPlugin.spin_plugin_t;
    }

    let mk_plugins () =
        let pp = new PromelaParserPlugin.pp_plugin_t "promelaParser" in
        let vr = new VarRolePlugin.vr_plugin_t "varRoles" in
        let pdom = new PiaDomPlugin.pia_dom_plugin_t "piaDom" in
        let pdg =
            new PiaDataPlugin.pd_plugin_t ~keep_shared:true "piaDataShared" in
        let pd = new PiaDataPlugin.pd_plugin_t ~keep_shared:false "piaData" in
        let opt = new OptPlugin.opt_plugin_t "opt" in
        let pc = new PiaCounterPlugin.pc_plugin_t "piaCounter" in
        let nv = new NusmvSsaPlugin.nusmv_ssa_plugin_t "nusmvCounter" "main" in
        let sn = new SpinPlugin.spin_plugin_t "spin" "abs-counter" in
        { pp; opt; vr; pdom; pdg; pd; pc; nv; sn }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.pp OutOfPred;
        chain#add_plugin plugins.vr OutOfPred;
        chain#add_plugin plugins.pdom OutOfPred;
        chain#add_plugin plugins.pdg OutOfPred;
        chain#add_plugin plugins.pd (OutOfPlugin "piaDom");
        chain#add_plugin plugins.opt OutOfPred;
        chain#add_plugin plugins.pc (OutOfPlugins ["piaData"; "piaDataShared"]);
        chain#add_plugin plugins.nv (OutOfPlugins ["piaCounter"; "opt"]);
        chain#add_plugin plugins.sn (OutOfPlugin "piaCounter");
        chain
end


(** Just fixing the parameters and checking finite-state systems. *)
module Conc = struct
    type plugins_t = {
        pp: PromelaParserPlugin.pp_plugin_t;
        inst: InstantiationPlugin.instantiation_plugin_t;
    }

    let mk_plugins () =
        let pp = new PromelaParserPlugin.pp_plugin_t "promelaParser" in
        let inst = new InstantiationPlugin.instantiation_plugin_t
            "inst" in
        { pp; inst }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.pp OutOfPred;
        chain#add_plugin plugins.inst OutOfPred;
        chain
end


(** CONCUR'14: computing the diameter bound for bounded model checking *)
module PiaBounds = struct
    type plugins_t = {
        pia: Pia.plugins_t;
        sk: SymbSkelPlugin.symb_skel_plugin_t;
        pb: PorBoundsPlugin.por_bounds_plugin_t;
        ssn: SymbSkelNusmvPlugin.skel_nusmv_plugin_t;
    }

    let mk_plugins () =
        let pia = Pia.mk_plugins () in
        let sk = new SymbSkelPlugin.symb_skel_plugin_t "symbSkel" in
        let pb =
            new PorBoundsPlugin.por_bounds_plugin_t "porBounds" sk in
        let module SSN = SymbSkelNusmvPlugin in
        let ssn = new SSN.skel_nusmv_plugin_t "skelNusmv" "main" in
        { pia; sk; pb; ssn; }

    let mk_chain plugins =
        let chain = Pia.mk_chain plugins.pia in
        chain#add_plugin plugins.sk (OutOfPlugin "piaDataShared");
        chain#add_plugin plugins.pb OutOfPred;
        chain#add_plugin plugins.ssn (* XXX: why is it here after all??? *)
            (OutOfPlugins ["piaCounter"; "piaData"]);
        chain
end


(**
  CONCUR'14: Constructing threshold automata using data abstraction
             and translating to the FAST input format.
 *)
module PiaFast = struct
    type plugins_t = {
        pp: PromelaParserPlugin.pp_plugin_t;
        vr: VarRolePlugin.vr_plugin_t;
        pdom: PiaDomPlugin.pia_dom_plugin_t;
        pdg: PiaDataPlugin.pd_plugin_t;
        fp: FastPlugin.fast_plugin_t;
    }

    let mk_plugins () =
        let pp = new PromelaParserPlugin.pp_plugin_t "promelaParser" in
        let vr = new VarRolePlugin.vr_plugin_t "varRoles" in
        let pdom = new PiaDomPlugin.pia_dom_plugin_t "piaDom" in
        let pdg =
            new PiaDataPlugin.pd_plugin_t ~keep_shared:true "piaDataShared" in
        let fp = new FastPlugin.fast_plugin_t "fast" in
        { pp; vr; pdom; pdg; fp }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.pp OutOfPred;
        chain#add_plugin plugins.vr OutOfPred;
        chain#add_plugin plugins.pdom OutOfPred;
        chain#add_plugin plugins.pdg OutOfPred;
        chain#add_plugin plugins.fp OutOfPred;
        chain
end


(**
  Constructing threshold automata in a complicated way using NuSMV and BDDs.

  @deprecated: this chain will be removed in the future. 
 *)
module PiaSkelSmv = struct
    type plugins_t = {
        pia: Pia.plugins_t;
        ssn: SymbSkelNusmvPlugin.skel_nusmv_plugin_t;
    }

    let mk_plugins () =
        let pia = Pia.mk_plugins () in
        let module SSN = SymbSkelNusmvPlugin in
        let ssn = new SSN.skel_nusmv_plugin_t "skelNusmv" "main" in
        { pia; ssn }

    let mk_chain plugins =
        let chain = Pia.mk_chain plugins.pia in
        chain#add_plugin plugins.ssn (OutOfPlugins ["piaCounter"; "piaData"]);
        chain
end


(**
  CAV'15 and POPL'17: perform SMT-based bounded model checking by:
      (1) constructing threshold automata using data abstraction, and
      (2) running SMT-based bounded model checking using schemas.

  This is the most efficient technique that we have so far.
  *)
module PiaPost = struct
    type plugins_t = {
        pp: PromelaParserPlugin.pp_plugin_t;
        vr: VarRolePlugin.vr_plugin_t;
        pdom: PiaDomPlugin.pia_dom_plugin_t;
        pdg: PiaDataPlugin.pd_plugin_t;
        pttp: PromelaToTaPlugin.promela_to_ta_plugin_t;
        slps: SchemaCheckerPlugin.slps_checker_plugin_t;
    }

    let mk_plugins () =
        let pp = new PromelaParserPlugin.pp_plugin_t "promelaParser" in
        let vr = new VarRolePlugin.vr_plugin_t "varRoles" in
        let pdom = new PiaDomPlugin.pia_dom_plugin_t "piaDom" in
        let pdg =
            new PiaDataPlugin.pd_plugin_t ~keep_shared:true "piaDataShared" in
        let pttp = new PromelaToTaPlugin.promela_to_ta_plugin_t "pttp" in
        let slps = new SchemaCheckerPlugin.slps_checker_plugin_t
            "slps" (pttp :> TaSource.ta_source_t)
        in
        { pp; vr; pdom; pdg; pttp; slps }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.pp OutOfPred;
        chain#add_plugin plugins.vr OutOfPred;
        chain#add_plugin plugins.pdom OutOfPred;
        chain#add_plugin plugins.pdg OutOfPred;
        chain#add_plugin plugins.pttp (OutOfPlugin "piaDataShared");
        chain#add_plugin plugins.slps (OutOfPlugin "piaDataShared");
        chain
end

(**
  This is a modification of PiaPost that takes a threshold automaton as its input,
  without parsing Promela code.
  *)
module TaPost = struct
    type plugins_t = {
        tapp: TaParserPlugin.ta_parser_plugin_t;
        slps: SchemaCheckerPlugin.slps_checker_plugin_t;
    }

    let mk_plugins () =
        let tapp = new TaParserPlugin.ta_parser_plugin_t "tapp" in
        let slps =
            new SchemaCheckerPlugin.slps_checker_plugin_t
                "slps" (tapp :> TaSource.ta_source_t)
        in
        { tapp; slps }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.tapp OutOfPred;
        chain#add_plugin plugins.slps OutOfPred;
        chain
end


let create_chain input chain_name =
    match (input, chain_name) with
    (* FMCAD'13: data + counter abstractions *)
    | InputPromela, "piaDataCtr" -> Pia.mk_chain (Pia.mk_plugins ())
    (* just fixing the parameters and checking finite-state systems *)
    | InputPromela, "concrete" -> Conc.mk_chain (Conc.mk_plugins ())
    (* CONCUR'14: computing the diameter bound for bounded model checking *)
    | InputPromela, "bounds" -> PiaBounds.mk_chain (PiaBounds.mk_plugins ())
    (* CONCUR'14: translating into the FAST input format *)
    | InputPromela, "fast" -> PiaFast.mk_chain (PiaFast.mk_plugins ())
    (* constructing threshold automata using BDDS, too complicated *)
    (* TODO: deprecated, remove skelSmv *)
    | InputPromela, "skelSmv" -> PiaSkelSmv.mk_chain (PiaSkelSmv.mk_plugins ())
    (* CAV'15 and POPL'17: using schemas and SMT-based bounded model checking *)
    | InputPromela, "post" -> PiaPost.mk_chain (PiaPost.mk_plugins ())
    (* same thing but using TA as input directly *)
    | InputTa, "post" -> TaPost.mk_chain (TaPost.mk_plugins ())

    | input, chain_name ->
        let inp_s = Options.input_s input in
        raise (Failure (sprintf "Unknown input/chain: %s and %s" inp_s chain_name))

