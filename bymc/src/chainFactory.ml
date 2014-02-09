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
        pp: PromelaParserPlugin.promela_parser_plugin_t;
        vr: VarRolePlugin.var_role_plugin_t;
        pdom: PiaDomPlugin.pia_dom_plugin_t;
        pd: PiaDataPlugin.pia_data_plugin_t;
        pc: PiaCounterPlugin.pia_counter_plugin_t;
        nv: NusmvCtrClusterPlugin.nusmv_ctr_cluster_plugin_t;
        sn: SpinPlugin.spin_plugin_t;
    }

    let mk_plugins () =
        let pp = new PromelaParserPlugin.promela_parser_plugin_t "promelaParser"
        in
        let vr = new VarRolePlugin.var_role_plugin_t "varRoles" in
        let pdom = new PiaDomPlugin.pia_dom_plugin_t "piaDom" in
        let pd = new PiaDataPlugin.pia_data_plugin_t "piaData" in
        let pc = new PiaCounterPlugin.pia_counter_plugin_t "piaCounter" pd in
        let nv =
            new NusmvCtrClusterPlugin.nusmv_ctr_cluster_plugin_t
                "nusmvCounter" "main" pd in
        let sn = new SpinPlugin.spin_plugin_t "spin" "abs-counter" in
        { pp = pp; vr = vr; pdom = pdom; pd = pd; pc = pc; nv = nv; sn = sn }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.pp;
        chain#add_plugin plugins.vr;
        chain#add_plugin plugins.pdom;
        chain#add_plugin plugins.pd;
        chain#add_plugin plugins.pc;
        chain#add_plugin plugins.nv;
        chain#add_plugin plugins.sn;
        chain
end

module Conc = struct
    type plugins_t = {
        pp: PromelaParserPlugin.promela_parser_plugin_t;
        inst: InstantiationPlugin.instantiation_plugin_t;
    }

    let mk_plugins () =
        let pp = new PromelaParserPlugin.promela_parser_plugin_t
            "promelaParser" in
        let inst = new InstantiationPlugin.instantiation_plugin_t
            "inst" in
        { pp = pp; inst = inst }

    let mk_chain plugins =
        let chain = new plugin_chain_t in
        chain#add_plugin plugins.pp;
        chain#add_plugin plugins.inst;
        chain
end


module PiaSymb = struct
    type plugins_t = {
        pia: Pia.plugins_t;
        sk: SymbSkelPlugin.symb_skel_plugin_t;
    }

    let mk_plugins () =
        let pia = Pia.mk_plugins () in
        let sk = new SymbSkelPlugin.symb_skel_plugin_t
            "symbSkel" pia.Pia.pc in
        { pia = pia; sk = sk }

    let mk_chain plugins =
        let chain = Pia.mk_chain plugins.pia in
        chain#add_plugin plugins.sk;
        chain
end


let mk_pia_data_counter_chain () =
    Pia.mk_chain (Pia.mk_plugins ())

let mk_concrete_chain () =
    Conc.mk_chain (Conc.mk_plugins ())

let mk_bound_chain () =
    PiaSymb.mk_chain (PiaSymb.mk_plugins ())

let create_chain = function
    | "piaDataCtr" -> mk_pia_data_counter_chain ()
    | "concrete" -> mk_concrete_chain ()
    | "bound" -> mk_bound_chain ()
    | _ as n -> raise (Failure ("Unknown chain: " ^ n))

