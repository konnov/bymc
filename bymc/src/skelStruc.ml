(* 
   Specific code to extract process skeleton structure:
   init section, main loop, etc.
 *)

open Accums
open Cfg
open Printf
open Regions
open Spin
open SpinIr
open SpinIrImp


exception Skel_error of string

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

  alternatively, it can have the structure:
  declarations;
  init_statements;
  loop_prefix;
  main:
  atomic {
      computation;
      updates;
  }
  goto main;


  The mentioned sections are extracted from the sequence.
  This is to be generalized in the future.
 *)
let extract_skel proc_body =
    (* declarations come first *)
    let decls, non_decls = List.partition is_mdecl proc_body in
    (* whatever is before the loop is considered to be initialization *)
    let is_label = function
        | MLabel (_, _) -> true
        | _ -> false
    in
    let inits, rests = Accums.list_div is_label non_decls in
    let not_label s = not (is_label s) in
    (* the labels form the loop prefix *)
    let loop_prefix, loop_body = Accums.list_div not_label rests in
    (* the loop body can be written EITHER AS:
        lab:
        atomic { ... }
        goto lab

        OR (goto-haters, we care of your feelings) 
        
        do
            :: atomic { ... }
        od
    *)
    let atomic_body = match loop_body with
    | (MAtomic (_, atomic_body)) :: _ -> atomic_body
    | (MIf (_, [MOptGuarded [MAtomic (_, atomic_body)]])) :: _ -> atomic_body
    | _ ->
         printf "loop_body:\n";
         List.iter (fun s -> printf "%s\n" (mir_stmt_s s)) loop_body;
         raise (Skel_error "The loop body must be protected with atomic")
    in
    let not_update = function
        | MExpr (_, Nop _) -> false
        | MExpr (_, BinEx (ASGN, _, _)) -> false
        | MPrint (_, _, _) -> false (* ignore *)
        | MAssume (_, _) -> false   (* ignore *)
        | MSkip _ -> false          (* ignore *)
        | _ -> true
    in
    let rupdates, rcomp = Accums.list_div not_update (List.rev atomic_body) in
    let updates = List.rev rupdates
    and comp = List.rev rcomp in
    
    let reg_tbl = new region_tbl in
    reg_tbl#add "decl" decls;
    reg_tbl#add "init" inits;
    reg_tbl#add "loop_prefix" loop_prefix;
    reg_tbl#add "comp" comp;
    reg_tbl#add "update" updates;
    reg_tbl#add "loop_body" loop_body;
    reg_tbl


let pass caches prog =
    let cache_skel proc =
        let reg_tab = extract_skel proc#get_stmts in
        caches#struc#set_regions proc#get_name reg_tab
    in
    List.iter cache_skel (Program.get_procs prog);
    prog

