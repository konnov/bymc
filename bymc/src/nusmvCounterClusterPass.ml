(*
  An optimized encoding of counter representation that represent each
  counter as a module. This allows nusmv to use clusters, which are much
  more efficient for large models.

  Igor Konnov, 2013
 *)

open Printf

open Accums

let create_proc_counters caches out proc =
    let ctr_ctx =
        caches#analysis#get_pia_ctr_ctx_tbl#get_ctx proc#get_name in
    let create_module idx =
        let valtab = ctr_ctx#unpack_from_const idx in
        (* XXX: fix params, they should include next *)
        let params = str_join ", "
            (List.map (fun v -> v#get_name) (hashtbl_keys valtab)) in
        let next_name v =
            let next = ctr_ctx#get_next v in
            next#get_name in
        let next_params = str_join ", "
            (List.map next_name (hashtbl_keys valtab)) in
        fprintf out "MODULE ktr_%d(%s, %s, myval, oval)\n"
            idx params next_params;
        fprintf out " ASSIGN\n";
        fprintf out " next(myval) =\n";
        fprintf out "  case\n";
        (* TODO: collect all possible outcomes for one input value *)
        fprintf out "  esac\n";
    in
    let all_indices = ctr_ctx#all_indices_for (fun _ -> true) in
    List.iter create_module all_indices

let transform caches out_name prog =
    let out = open_out (out_name ^ ".smv") in
    List.iter (create_proc_counters caches out) (Program.get_procs prog);
    close_out out

