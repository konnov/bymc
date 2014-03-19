(* 
   Specific code to extract process skeleton structure:
   init section, main loop, etc.
 *)

open Accums
open Printf
open Regions
open Spin
open SpinIr
open SpinIrImp


exception Skel_error of string
exception Struc_error of string

type loop_sig = {
    (* relate the variables entering the loop to the variables leaving the loop,
       e.g., ('pc', 'next_pc')
     *)
    prev_next: (var * var) list
}

let empty_loop_sig =
    { prev_next = [] }


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


let extract_loop_sig prog reg_tbl proc =
    let update = mir_to_lir (reg_tbl#get "update" proc#get_stmts) in
    let prev_next = hashtbl_as_list (Analysis.find_copy_pairs update) in
    let pn = (List.map fst prev_next) @ (List.map snd prev_next) in
    if (List.length pn) <> (List.length proc#get_locals)
    then begin
        let missing = List.filter (fun v -> not (List.mem v pn)) proc#get_locals in
        let missing_s = str_join ", " (List.map (fun v -> v#get_name) missing) in
        raise (Skel_error
            (sprintf "No `next' variables found for the variables of %s: %s"
            proc#get_name missing_s))
    end;
    { prev_next = prev_next }


let get_prev_next loop_sig = loop_sig.prev_next


let get_loop_next loop_sig prev =
    try snd (List.find (fun (p, n) -> p#id = prev#id) loop_sig.prev_next)
    with Not_found -> raise (Failure ("no next var for " ^ prev#qual_name))


(*
  The structural information of the control flow and data
  flow. The structure is bound to a program id. If there is no
  last version of the cache, then the last one before the
  given program version is used.
 *)

class proc_struc =
    object(self)
        val mutable m_reg_tbl:
            (string, region_tbl) Hashtbl.t = Hashtbl.create 1
        val mutable m_loop_sig_tbl:
            (string, loop_sig) Hashtbl.t = Hashtbl.create 1

        method get_regions proc_name =
            try Hashtbl.find m_reg_tbl proc_name
            with Not_found ->
                raise (Struc_error ("No regions for " ^ proc_name))

        method set_regions proc_name proc_regs =
            Hashtbl.replace m_reg_tbl proc_name proc_regs

        method get_loop_sig proc_name =
            try Hashtbl.find m_loop_sig_tbl proc_name
            with Not_found ->
                raise (Struc_error ("No loop signature for " ^ proc_name))

        method set_loop_sig proc_name lsig =
            Hashtbl.replace m_loop_sig_tbl proc_name lsig

        method get_annotations =
            let main_tab = Hashtbl.create 10 in
            let add_proc proc_name tab =
                let add id = function
                    | AnnotBefore text ->
                        Hashtbl.replace main_tab 
                            id (AnnotBefore (sprintf "%s::%s" proc_name text))

                    | AnnotAfter text ->
                        Hashtbl.replace main_tab 
                            id (AnnotAfter (sprintf "%s::%s" proc_name text))
                in
                Hashtbl.iter add (tab#get_annotations)
            in
            Hashtbl.iter add_proc m_reg_tbl;
            main_tab

    end


let empty_proc_struc () = new proc_struc


let compute_struc prog = 
    let struc = empty_proc_struc () in
    let extract_reg proc =
        let reg_tab = extract_skel proc#get_stmts in
        struc#set_regions proc#get_name reg_tab;
        (*
        let loop_sig = extract_loop_sig proc reg_tab proc in
        struc#set_loop_sig proc#get_name loop_sig
        *)
    in
    List.iter extract_reg (Program.get_procs prog);
    struc

