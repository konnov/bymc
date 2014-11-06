(* Extract a symbolic skeleton from a process description, i.e.,
  the transition relation between local states with the edges labeled
  by conditions and actions

  @deprecated: just use Summary

  Igor Konnov, 2014
 *)

open Printf
open Unix

open Accums
open Debug
open Plugin
open SkelStruc
open SpinIr
open SpinIrImp

open SymbSkel

class symb_skel_plugin_t (plugin_name: string) =
    object(self)
        inherit analysis_plugin_t plugin_name

        val mutable m_skels: Sk.skel_t list = [];
        val mutable m_abs_skels: Sk.skel_t list = [];

        method skels = m_skels
        (* TODO: decouple skeleton abstraction from
            the skeleton construction *)
        method abs_skels = m_abs_skels

        method transform rt =
            log WARN "*******************************************";
            log WARN "* SymbSkelPlugin is outdated, use Summary *";
            log WARN "*******************************************";
            let sprog = self#get_input0 in
            rt#caches#set_struc sprog (compute_struc sprog);
            let each_proc (skels, askels, prog) proc =
                let sk, new_prog = self#extract_proc rt prog proc in
                let roles = rt#caches#analysis#get_var_roles sprog in
                let ask = self#abstract_skel rt new_prog roles sk in
                Sk.to_file (sprintf "skel-int-%s.sk" proc#get_name) ask;
                (sk :: skels, ask :: askels, new_prog)
            in
            let skels, askels, new_prog =
                List.fold_left each_proc ([], [], sprog) (Program.get_procs sprog)
            in
            m_skels <- skels;
            m_abs_skels <- askels;
            new_prog

        method test_input filename =
            try access filename [F_OK]
            with Unix_error _ ->
                raise (InputRequired ("local transitions in " ^ filename))

        method read_transitions prev_next filename =
            let each_line a l =
                let segs = Str.split (Str.regexp_string ",") l in
                let vals = List.map str_i segs in
                let vv = List.combine prev_next vals in 
                (* the even values are the values before,
                   and the odd ones are the values after *)
                let is_even (i, _) = (i mod 2) = 0 in
                let pvals, nvals = List.partition is_even (lst_enum vv)
                in
                (List.map snd pvals, List.map snd nvals) :: a
            in
            List.rev (fold_file each_line [] filename)

        method write_vars tt prev_next filename =
            let fout = open_out filename in
            let write v =
                let t = tt#get_type v in
                fprintf fout "%s:%d\n" v#mangled_name t#range_len
            in
            List.iter write prev_next;
            close_out fout

        method abstract_skel rt new_prog roles sk =
            let ctx = rt#caches#analysis#get_pia_data_ctx in
            let dom = rt#caches#analysis#get_pia_dom in
            let tt = (Program.get_type_tab new_prog)#copy in
            let roles = roles#copy in
            ctx#set_roles roles; (* XXX: must piaDataPlugin do that? *)
            let module AI = AbsInterval in
            let is_shadow = function
                | UnEx (Spin.NEXT, _) -> true
                | _ -> false
            in
            let add_def v =
                rt#solver#append_var_def v (tt#get_type v) in
            let afun e =
                (* hide next(x) under a temporary variable *)
                let se, shadows, unshadow_f = AI.shadow_expr is_shadow e in
                let register v =
                    roles#add v VarRole.SharedUnbounded;
                    tt#set_type v (new data_type SpinTypes.TINT);
                    add_def v
                in
                List.iter register shadows;
                (* abstract *)
                let ae =
                    if se <> IntConst 1
                    then AI.translate_expr ctx dom rt#solver AbsBasics.ExistAbs se
                    else IntConst 1
                in
                (* unhide next(x) *)
                unshadow_f ae
            in
            let each_rule r =
                let new_guard = afun r.Sk.guard in
                let new_act = List.map afun r.Sk.act in
                { r with Sk.guard = new_guard; Sk.act = new_act }
            in
            rt#solver#push_ctx;
            List.iter add_def (Program.get_shared new_prog);
            let new_rules = List.map each_rule sk.Sk.rules in
            let new_inits = List.map afun sk.Sk.inits in
            rt#solver#pop_ctx;
            { sk with Sk.rules = new_rules; Sk.inits = new_inits }

        method extract_proc rt prog proc =
            let reg_tbl = (rt#caches#find_struc prog)#get_regions proc#get_name in
            let loop_sig = SkelStruc.extract_loop_sig prog reg_tbl proc in
            let prev_next_pairs = SkelStruc.get_prev_next loop_sig in
            let tt = Program.get_type_tab prog in
            let unpair l (p, n) = n :: p :: l in
            let prev_next = List.rev (List.fold_left unpair [] prev_next_pairs) in 
            self#write_vars tt prev_next
                (sprintf "vis-%s.txt" proc#get_name);
            let filename = sprintf "local-tr-%s.txt" proc#get_name in
            self#test_input filename;
            let trs = self#read_transitions prev_next filename in
            let sk = SymbSkel.state_pairs_to_rules rt prog proc trs in
            let loc_vars = IntMap.values sk.Sk.loc_vars in

            Sk.to_file (sprintf "skel-%s.sk" proc#get_name) sk;
            let ntt = (Program.get_type_tab prog)#copy in
            let set_type v = ntt#set_type v (new data_type SpinTypes.TUNSIGNED)
            in
            BatEnum.iter set_type loc_vars;
            let new_prog =
                Program.set_type_tab ntt prog
                    |> Program.set_shared
                        ((Program.get_shared prog) @ (BatList.of_enum loc_vars))
            in
            sk, new_prog

        method update_runtime rt =
            ()
    end

