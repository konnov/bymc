(*
 Analysis and transformation infrastructure.

 Igor Konnov, 2012
 *)

open VarRole
open PiaDataCtx
open PiaDom
open PiaCtrCtx
open Regions

exception CacheStateError of string

(*
  All analysis and transformation passes have an access to this cache.
  Every pass may update the attributes of this cache. If a pass corrupts certain
  cached data, then the pass must reset this data.
 *)
class analysis_cache =
    object(self)
        val mutable m_var_roles: var_role_tbl option = None
        val mutable m_pia_dom: pia_domain option = None
        val mutable m_pia_data_ctx: pia_data_ctx option = None
        val mutable m_pia_ctr_ctx_tbl: ctr_abs_ctx_tbl option = None
        
        method get_var_roles =
            match m_var_roles with
            | None -> raise (CacheStateError "var_roles is not set")
            | Some r -> r

        method set_var_roles r =
            m_var_roles <- Some r

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

(*
  All analysis and transformation passes have an access to this cache,
  and every pass may update the attributes of this cache. The purpose of the
  cache is to collect the structural information about control flow and data
  flow. If a pass corrupts certain cached data, then the pass must reset this
  data.
 *)

class proc_struc_cache =
    object(self)
        val mutable m_reg_tbl: (string, region_tbl) Hashtbl.t = Hashtbl.create 1

        method get_regions proc_name =
            try Hashtbl.find m_reg_tbl proc_name
            with Not_found ->
                raise (CacheStateError "regions is not set")

        method set_regions proc_name proc_regs =
            Hashtbl.replace m_reg_tbl proc_name proc_regs
    end


class pass_caches (i_analysis: analysis_cache) (i_struc: proc_struc_cache) =
    object(self)
        method get_analysis = i_analysis
        method get_struc = i_struc
    end


type analysis_fun =
    pass_caches -> Program.program -> pass_caches

type translation_fun =
    pass_caches -> Program.program -> (pass_caches * Program.program)

