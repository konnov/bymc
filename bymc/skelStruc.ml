(* 
   Specific code to extract process skeleton structure:
   init section, main loop, etc.
 *)

open Spin_ir;;
open SpinIrImp;;
open Cfg;;

type 't skel_struc = {
    decl: 't mir_stmt list;
    init: 't mir_stmt list;
    loop_prefix: 't mir_stmt list;
    comp: 't mir_stmt list;
    update: 't mir_stmt list
};;

exception Skel_error of string;;

(*
  Here we check that a process body has the following structure:
 
  declarations;
  init_statements;
  loop_prefix;
  main:
  if
    :: atomic {
        computation;
        updates;
      }
  fi;
  goto main;

  The mentioned sections are extracted from the sequence.
  This is to be generalized in the future.
 *)
let extract_skel proc_body =
    let decls, non_decls = List.partition is_mdecl proc_body in
    let cfg = Cfg.mk_cfg (mir_to_lir proc_body) in
    let loop = match (comp_sccs cfg#entry) with
    | [] -> raise (Skel_error "Skeleton does not have the main loop")
    | [one_scc] -> one_scc
    | _ as sccs ->
        List.iter
            (fun scc ->
                Printf.printf " *** SCC ***\n";
                List.iter (fun b -> Printf.printf "  %s\n" b#str) scc
            ) sccs;
        raise (Skel_error "Skeleton has more than one loop inside")
    in
    (* the last elem of the first block is supposed to be 'if' *)
    let if_id = match (List.hd (List.rev (List.hd loop)#get_seq)) with
    | If (id, _, _) -> id
    | _ ->
        Printf.printf " *** LOOP ***\n";
        List.iter (fun b -> Printf.printf "  %s\n" b#str) loop;
        raise (Skel_error "The main loop does not start with 'if'")
    in
    let init_s, if_s, rest_s =
        Accums.list_cut (fun s -> (m_stmt_id s) = if_id) non_decls
    in
    let init_s, prefix_s = collect_final_labs init_s in
    let opt_body = match if_s with
    | [MIf (_, [MOptGuarded seq])] -> seq
    | _ -> raise (Skel_error "The main loop must be guarded by the only option")
    in
    let atomic_body = match opt_body with
    | [MAtomic (_, atomic_body)] -> atomic_body
    | _ -> raise (Skel_error "The computation must be protected by atomic")
    in
    let assumps, el, tl =
        Accums.list_cut_ignore (* collect finalizing assumptions *)
            (function | MAssume (_, _) -> false | _ -> true)
            (List.rev atomic_body)
    in
    let hd, el, tl =
        Accums.list_cut_ignore (* collect finalizing expressions + assumps *)
            (function
                | MExpr (_, _) -> false
                | MAssume (_, _) -> false
                | _ -> true)
            (el @ tl)
    in
    let update = (List.rev hd) @ (List.rev assumps) in
    let comp = List.rev (el @ tl) in
    { decl = decls; init = init_s;
      loop_prefix = prefix_s; comp = comp; update = update }
;;

