
open AbsInterval;;
open AbsCounter;;
open Spin_ir;;
open Writer;;
open Debug;;

let do_abstraction units =
    let ctx = mk_context units in
    let solver = ctx#run_solver in
    let dom = mk_domain solver ctx units in

    if may_log INFO then dom#print;
    let new_units = do_interval_abstraction ctx dom solver units in
    (* debug output *)
    let fo = open_out "abs-interval.prm" in
    List.iter (write_unit fo 0) new_units;
    close_out fo;
    (* end of debug output *)
    let ctr_ctx = new ctr_abs_ctx dom ctx in
    let funcs = new abs_ctr_funcs dom ctx ctr_ctx solver in
    let new_units2 = do_counter_abstraction ctx dom solver ctr_ctx funcs new_units in
    let _ = solver#stop in
    new_units2
;;
