(* Here is the place where the standard chains are created.
 *
 * Igor Konnov, 2014
 *)

open Plugin
open Runtime

(*
  Every chain should come with its own module. As the plugins in one
  chain are usually connected, the module has to provide access to
  the plugins. This is the least painful way I have found so far.
 *)
module Pia = struct
    type plugins_t = {
        pp: PromelaParserPlugin.pp_plugin_t;
        vr: VarRolePlugin.vr_plugin_t;
        pdom: PiaDomPlugin.pia_dom_plugin_t;
        pdg: PiaDataPlugin.pd_plugin_t;
        pd: PiaDataPlugin.pd_plugin_t;
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
        let pc = new PiaCounterPlugin.pc_plugin_t "piaCounter" in
        let nv = new NusmvSsaPlugin.nusmv_ssa_plugin_t "nusmvCounter" "main" in
        let sn = new SpinPlugin.spin_plugin_t "spin" "abs-counter" in
        { pp = pp; vr = vr; pdom = pdom; pdg = pdg; pd = pd;
            pc = pc; nv = nv; sn = sn }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.pp OutOfPred;
        chain#add_plugin plugins.vr OutOfPred;
        chain#add_plugin plugins.pdom OutOfPred;
        chain#add_plugin plugins.pdg OutOfPred;
        chain#add_plugin plugins.pd (OutOfPlugin "piaDom");
        chain#add_plugin plugins.pc (OutOfPlugins ["piaData"; "piaDataShared"]);
        chain#add_plugin plugins.nv (OutOfPlugins ["piaCounter"; "piaData"]);
        chain#add_plugin plugins.sn (OutOfPlugin "piaCounter");
        chain
end

module Conc = struct
    type plugins_t = {
        pp: PromelaParserPlugin.pp_plugin_t;
        inst: InstantiationPlugin.instantiation_plugin_t;
    }

    let mk_plugins () =
        let pp = new PromelaParserPlugin.pp_plugin_t
            "promelaParser" in
        let inst = new InstantiationPlugin.instantiation_plugin_t
            "inst" in
        { pp = pp; inst = inst }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.pp OutOfPred;
        chain#add_plugin plugins.inst OutOfPred;
        chain
end


module PiaSymb = struct
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
        let ssn = new SSN.skel_nusmv_plugin_t "skelNusmv" "main" sk in
        { pia = pia; sk = sk; pb = pb; ssn = ssn }

    let mk_chain plugins =
        let chain = Pia.mk_chain plugins.pia in
        chain#add_plugin plugins.sk (OutOfPlugin "piaDataShared");
        chain#add_plugin plugins.pb OutOfPred;
        chain#add_plugin plugins.ssn
            (OutOfPlugins ["piaCounter"; "piaData"]);
        chain
end


let mk_pia_data_counter_chain () =
    Pia.mk_chain (Pia.mk_plugins ())

let mk_concrete_chain () =
    Conc.mk_chain (Conc.mk_plugins ())

let mk_bounds_chain () =
    PiaSymb.mk_chain (PiaSymb.mk_plugins ())

let create_chain = function
    | "piaDataCtr" -> mk_pia_data_counter_chain ()
    | "concrete" -> mk_concrete_chain ()
    | "bounds" -> mk_bounds_chain ()
    | _ as n -> raise (Failure ("Unknown chain: " ^ n))

