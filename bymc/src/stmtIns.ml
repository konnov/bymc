(* This is a high-level interface to insert statements into the process code.
   Use it in case if you do not want to rewrite the process body completely,
   but only to insert a couple of statements in the middle.

   This module takes care of updating analysis caches, e.g., regions.
   That is why it is not recommended to use it in global rewrites.

   Igor Konnov, 2013
 *)

open Printf

open Accums
open Program
open Runtime
open Spin
open SpinIr

type st = token mir_stmt

(*
  Insert statement s after statement anchor,
  extend all anchor's regions to include s.
 *)
let insert_after (rt: runtime_t) (p: token proc) (anchor: st) (elem: st) =
    let aid = m_stmt_id anchor in
    let rec sub rs s =
        if aid = (m_stmt_id s)
        then elem :: s :: rs
        else match s with
            | MIf (id, opts) ->
                (MIf (id, List.map sub_opt opts)) :: rs

            | MAtomic (id, body) ->
                (MAtomic (id, List.rev (List.fold_left sub [] body))) :: rs

            | MD_step (id, body) ->
                (MD_step (id, List.rev (List.fold_left sub [] body))) :: rs

            | _ as s -> s :: rs

    and sub_opt = function
    | MOptGuarded body ->
        MOptGuarded (List.rev (List.fold_left sub [] body))

    | MOptElse body ->
        MOptElse (List.rev (List.fold_left sub [] body))
    in

    proc_replace_body p (List.rev (List.fold_left sub [] p#get_stmts))
    
    (* TODO: update regions
let reg_tab = rt#caches#struc#get_regions proc#get_name in
    *)
    
