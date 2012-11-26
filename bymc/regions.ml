(* Keeping info about regions of a control flow graph.
 *
 * Igor Konnov, 2012
 *)

open Spin
open SpinIr

exception Region_error of string

class region_tbl =
    object
        val mutable m_regions: (string, Spin.token mir_stmt list) Hashtbl.t =
            Hashtbl.create 5

        method add name stmts =
            Hashtbl.replace m_regions name stmts

        method get name =
            try Hashtbl.find m_regions name
            with Not_found -> raise (Region_error name)
    end

