(*
 Analysis and transformation infrastructure.
 
 The analysis results can be used across different modules and plugins.
 The caches are not persistent in the sense that at some point of time ---
 e.g., when restoring from disk --- the system may reset the caches and
 then fill them in with the help of the plugins.

 The plugins MUST NOT overwrite the caches provided by the other plugins.

 Igor Konnov, 2012
 *)

open Options
open Printf

open Accums
open PiaDataCtx
open PiaDom
open PiaCtrCtx
open Program
open Regions
open SkelStruc
open SpinIr
open VarRole

exception CacheStateError of string

(*
  All analysis and transformation passes have an access to this cache.
  Every pass may update the attributes of this cache. If a pass corrupts certain
  cached data, then the pass must reset this data.
 *)
class analysis_cache =
    object(self)
        val mutable m_var_roles: var_role_tbl IntMap.t = IntMap.empty
        val mutable m_pia_dom: pia_domain option = None
        val mutable m_pia_data_ctx: pia_data_ctx option = None
        val mutable m_pia_ctr_ctx_tbl: ctr_abs_ctx_tbl option = None
        
        method get_var_roles prog =
            let pid = prog_uid prog in
            try IntMap.find pid m_var_roles
            with Not_found ->
                raise (CacheStateError
                    (sprintf "No var_roles for program id %d" pid))

        method set_var_roles prog r =
            m_var_roles <- IntMap.add (prog_uid prog) r m_var_roles

        method get_pia_dom =
            match m_pia_dom with
            | None -> raise (CacheStateError "pia_dom is not set")
            | Some d -> d

        method set_pia_dom d =
            m_pia_dom <- Some d

        method get_pia_data_ctx =
            match m_pia_data_ctx with
            | None -> raise (CacheStateError "pia_data_ctx is not set")
            | Some c -> c

        method set_pia_data_ctx c =
            m_pia_data_ctx <- Some c

        method get_pia_ctr_ctx_tbl =
            match m_pia_ctr_ctx_tbl with
            | None -> raise (CacheStateError "pia_ctr_ctx is not set")
            | Some c -> c

        method set_pia_ctr_ctx_tbl c =
            m_pia_ctr_ctx_tbl <- Some c
    end



class pass_caches (i_options: options_t) (i_analysis: analysis_cache) =
    object(self)
        val mutable m_struc_tab:
            (int, proc_struc) Hashtbl.t = Hashtbl.create 1

        method options = i_options
        method analysis = i_analysis

        method find_struc prog =
            let uid = Program.prog_uid prog in
            try Hashtbl.find m_struc_tab uid
            with Not_found ->
                let pick_max m x =
                    if m > x && m <= uid then m else x in
                let max_id =
                    List.fold_left pick_max (-1) (hashtbl_keys m_struc_tab) in
                if max_id = (-1)
                then raise
                    (Failure ("No matching structure found for the program"))
                else Hashtbl.find m_struc_tab max_id

        method set_struc prog s =
            Hashtbl.replace m_struc_tab (Program.prog_uid prog) s
    end


(* deprecated *)
type analysis_fun =
    pass_caches -> program_t -> pass_caches

type translation_fun =
    pass_caches -> program_t -> (pass_caches * program_t)

