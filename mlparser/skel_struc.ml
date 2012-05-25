(* 
   Specific code to extract process skeleton structure:
   init section, main loop, etc.
 *)

open Spin_ir;;
open Cfg;;

type region = RegInit | RegGuard | RegAtomic | RegEnd;;

(*
    Here we check that a control flow graph has the following structure:

    RegInit{ }

    RegGuard{
main:
    if
        :: guard } -> RegAtomic{
            ...
        }
    fi;

    RegEnd{
    goto main
    }

    This can be done by performing structural analysis (see Muchnik),
    but here we do a simple check up and extraction of the regions.
 *)
let extract_skel cfg =
    let regtbl = Hashtbl.create (Hashtbl.length cfg) in
    Hashtbl.iter (fun _ bb -> bb#set_visit_flag false) cfg;
    let rec search prev_reg bb =
        let exists f = List.exists f bb#get_seq in
        if not bb#get_visit_flag
        then bb#set_visit_flag true; 
            let my_reg, next_reg = match prev_reg with
            | RegInit ->
                if (List.length bb#get_pred) > 1
                    && exists (function If (_, _) -> true | _ -> false)
                then RegGuard, RegGuard
                else RegInit, RegInit

            | RegGuard ->
                if exists (function Atomic_beg -> true | _ -> false)
                then RegAtomic, RegAtomic
                else RegGuard, RegGuard

            | RegAtomic ->
                if exists (function Atomic_end -> true | _ -> false)
                then RegAtomic, RegEnd
                else RegAtomic, RegAtomic
            
            | RegEnd -> RegEnd, RegEnd
            in
            Hashtbl.add regtbl bb my_reg;
            List.iter (search next_reg) bb#get_succ
    in
    search RegInit (Hashtbl.find cfg 0);
    regtbl
;;
