(* Analysis based on abstract interpretation *)

open Cfg;;

(* general analysis *)
let visit_basic_block transfer_fun bb in_vals =
    List.fold_left (fun res stmt -> transfer_fun stmt res) in_vals bb#get_seq
;;

let visit_cfg visit_bb_fun join_fun cfg entry_vals =
    let bb_vals = Hashtbl.create 10 in
    Hashtbl.add bb_vals 0 entry_vals;
    let rec visit_once = function
        | [] -> []
        | hd :: tl ->
            let id = hd#get_lead_lab in
            let old_vals = Hashtbl.find bb_vals id in
            let new_vals = join_fun old_vals (visit_bb_fun hd old_vals) in
            if old_vals <> new_vals
            then begin
                Hashtbl.add bb_vals id old_vals;
                List.append tl hd#get_succ
            end
            else tl
    in
    visit_once (Hashtbl.find cfg 0)
;;

(* special kind of analysis *)
type int_role = IntervalInt of int * int | UnboundedInt;;

let join_int_roles lhs rhs = lhs
;;
