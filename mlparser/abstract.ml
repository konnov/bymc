
open AbsInterval;;
open AbsCounter;;
open Spin_ir;;
open Writer;;
open Debug;;

let do_abstraction units =
    let procs, other_units = List.fold_left
        (fun (lp, lo) u -> match u with
            | Proc p -> (p :: lp, lo)
            | _ -> (lp, u :: lo)
        ) ([], []) units
    in
    let ctx = mk_context units in
    let solver = ctx#run_solver in
    let dom = mk_domain solver ctx procs in
    if may_log INFO then dom#print;
    let new_procs = do_interval_abstraction ctx dom solver procs in
    (* debug output *)
    let fo = open_out "abs-interval.prm" in
    List.iter (write_unit fo 0) (List.append other_units new_procs);
    close_out fo;
    (* end of debug output *)
    let new_units = do_counter_abstraction ctx dom solver
        (List.append other_units new_procs) in
    let _ = solver#stop in
    new_units
;;
