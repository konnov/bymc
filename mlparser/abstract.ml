
open AbsInterval;;
open AbsCounter;;

open Spin_ir;;
open Writer;;
open Debug;;

let write_to_file name units =
    let fo = open_out name in
    List.iter (write_unit fo 0) units;
    close_out fo
;;

let do_abstraction units =
    let ctx = mk_context units in
    let solver = ctx#run_solver in
    let dom = mk_domain solver ctx units in

    if may_log INFO then dom#print;
    let new_units = do_interval_abstraction ctx dom solver units in
    write_to_file "abs-interval.prm" new_units;
    let ctr_ctx = new ctr_abs_ctx dom ctx in
    let vass_funcs = new vass_funcs dom ctx ctr_ctx solver in
    let vass_units =
        do_counter_abstraction ctx dom solver ctr_ctx vass_funcs new_units in
    write_to_file "abs-vass.prm" vass_units;
    let funcs = new abs_ctr_funcs dom ctx ctr_ctx solver in
    let new_units2 = do_counter_abstraction ctx dom solver ctr_ctx funcs new_units in
    let _ = solver#stop in
    new_units2
;;
