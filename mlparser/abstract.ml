
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

(* units -> interval abstraction -> counter abstraction *)
let do_abstraction units =
    let ctx = mk_context units in
    let solver = ctx#run_solver in
    let dom = mk_domain solver ctx units in

    if may_log INFO then dom#print;
    log INFO "> Constructing interval abstraction";
    let intabs_units = do_interval_abstraction ctx dom solver units in
    write_to_file "abs-interval.prm" intabs_units;
    log INFO "[DONE]";
    log INFO "> Constructing counter abstraction";
    let ctr_ctx = new ctr_abs_ctx dom ctx in
    let funcs = new abs_ctr_funcs dom ctx ctr_ctx solver in
    let ctrabs_units, _ =
        do_counter_abstraction ctx dom solver ctr_ctx funcs intabs_units in
    write_to_file "abs-counter.prm" ctrabs_units;
    log INFO "[DONE]";
    let _ = solver#stop in
    ctrabs_units
;;

(* units -> interval abstraction -> vector addition state systems *)
let do_refinement units =
   let ctx = mk_context units in
    let solver = ctx#run_solver in
    let dom = mk_domain solver ctx units in
    log INFO "> Constructing interval abstraction";
    let intabs_units = do_interval_abstraction ctx dom solver units in
    log INFO "[DONE]";
    log INFO "> Constructing VASS and transducers";
    let ctr_ctx = new ctr_abs_ctx dom ctx in
    let vass_funcs = new vass_funcs dom ctx ctr_ctx solver in
    let vass_units, transducers =
        do_counter_abstraction ctx dom solver ctr_ctx vass_funcs intabs_units
    in
    log INFO " [DONE]";
    write_to_file "abs-vass.prm" vass_units;
    let _ = solver#stop in ()
;;
