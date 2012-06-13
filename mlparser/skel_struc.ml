(* 
   Specific code to extract process skeleton structure:
   init section, main loop, etc.
 *)

open Spin_ir;;
open Cfg;;

type region = RegInit | RegGuard | RegCompute | RegUpdate | RegEnd;;

let region_s = function
    | RegInit -> "init"
    | RegGuard -> "guard"
    | RegCompute -> "compute"
    | RegUpdate -> "update"
    | RegEnd -> "end"
;;

(*
    Here we check that a control flow graph has the following structure:

    RegInit[ ]

    RegGuard[
main:
    if
        :: guard ] ->
            atomic {
                RegCompute[
                ...
                ]
                RegUpdate[
                ...
                ]
            }
    fi;

    RegEnd[
    goto main
    ]

    This can be done by performing structural analysis (see Muchnik),
    but here we do a simple check up and extraction of the regions.
 *)
let extract_skel cfg =
    let regtbl = Hashtbl.create (Hashtbl.length cfg) in
    Hashtbl.iter (fun _ bb -> bb#set_visit_flag false) cfg;
    let rec search prev_reg bb =
        let exists f = List.exists f bb#get_seq in
        if not bb#get_visit_flag
        then begin
            bb#set_visit_flag true; 
            let my_reg, next_reg = match prev_reg with
            | RegInit ->
                if (List.length bb#get_pred) > 1
                    && exists (function If (_, _, _) -> true | _ -> false)
                then RegGuard, RegGuard
                else RegInit, RegInit

            | RegGuard ->
                if exists (function Atomic_beg _ -> true | _ -> false)
                then RegCompute, RegCompute
                else RegGuard, RegGuard

            | RegCompute ->
                if exists (function Atomic_end _ -> true | _ -> false)
                then RegUpdate, RegEnd
                else RegCompute, RegCompute

            | RegUpdate -> raise (Failure "There must be one update region")
            
            | RegEnd -> RegEnd, RegEnd
            in
            Hashtbl.add regtbl bb#get_lead_lab my_reg;
            List.iter (search next_reg) bb#get_succ
        end
    in
    search RegInit (Hashtbl.find cfg 0);
    regtbl
;;
