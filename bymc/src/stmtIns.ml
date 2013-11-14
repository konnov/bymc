(* This is a high-level interface to insert statements into the process code.
   Use it in case if you do not want to rewrite the process body completely,
   but only to insert a couple of statements in the middle.

   This module takes care of updating analysis caches, e.g., regions.
   That is why it is not recommended to use it in global rewrites.

   Igor Konnov, 2013
 *)

open Printf

open Accums
open Infra
open Program
open SkelStruc
open Spin
open SpinIr

type st = token mir_stmt

(*
  Insert statement s after statement anchor,
  extend all anchor's regions to include s.
 *)
let insert_after (struc: proc_struc) (p: token proc)
        (anchor: st) (elems: st list) =
    let sub_fun s =
        if (m_stmt_id anchor) = (m_stmt_id s)
        then (true, s :: elems)
        else (false, [])
    in
    let reg_tab = struc#get_regions p#get_name in
    reg_tab#extend_after anchor elems;
    proc_replace_body p (sub_stmt_with_list sub_fun p#get_stmts)

(*
  Insert statement s before statement anchor,
  extend all anchor's regions to include s.
 *)
let insert_before (struc: proc_struc) (p: token proc)
        (anchor: st) (elems: st list) =
    let sub_fun s =
        if (m_stmt_id anchor) = (m_stmt_id s)
        then (true, elems @ [s])
        else (false, [])
    in
    let reg_tab = struc#get_regions p#get_name in
    reg_tab#extend_before anchor elems;
    proc_replace_body p (sub_stmt_with_list sub_fun p#get_stmts)

