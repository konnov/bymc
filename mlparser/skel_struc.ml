(* 
   Specific code to extract process skeleton structure:
   init section, main loop, etc.
 *)

open Spin_ir;;
open Cfg;;

type 't skel_struc = {
    decl: 't mir_stmt list;
    init: 't mir_stmt list;
    guard: 't mir_stmt;
    comp: 't mir_stmt list;
    update: 't mir_stmt list
};;

exception Skel_error of string;;

(*
  Here we check that a process body has the following structure:
 
  declarations;
  init_statements;
  main:
  if
    :: guard ->
      atomic {
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
    List.iter
        (fun s -> Printf.printf "  %s\n" (Spin_ir_imp.stmt_s s))
        (mir_to_lir proc_body);
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
    let (*guard, *) opt_body = match if_s with
    | [MIf (_, [MOptGuarded seq])] ->
            seq (* List.hd seq, List.tl seq *)
    | _ -> raise (Skel_error "The main loop must be guarded by the only option")
    in
    let atomic_body = match opt_body with
    | [MAtomic (_, atomic_body)] -> atomic_body
    | _ -> raise (Skel_error "The computation must be protected by atomic")
    in
    let hd, el, tl =
        Accums.list_cut_ignore (* cut it by the first non-expression *)
            (function
                | MExpr (_, _) -> false
                | _ -> true
            ) (List.rev atomic_body)
    in
    let update = List.rev hd in
    let comp = List.rev (el @ tl) in
    { decl = decls; init = init_s;
      guard = MExpr (-1, Nop) (*guard*); comp = comp; update = update }
;;

