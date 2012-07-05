
open Printf;;

open AbsInterval;;
open AbsCounter;;
open Refinement;;
open Smt;;

open Spin_ir;;
open Spin_ir_imp;;
open Writer;;
open Accums;;
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
let do_refinement trail_filename units =
   let ctx = mk_context units in
    let solver = ctx#run_solver in
    let dom = mk_domain solver ctx units in
    log INFO "> Constructing interval abstraction...";
    let intabs_units = do_interval_abstraction ctx dom solver units in
    log INFO "[DONE]";
    log INFO "> Constructing VASS and transducers...";
    let ctr_ctx = new ctr_abs_ctx dom ctx in
    let vass_funcs = new vass_funcs dom ctx ctr_ctx solver in
    let vass_units, xducers =
        do_counter_abstraction ctx dom solver ctr_ctx vass_funcs intabs_units
    in
    write_to_file "abs-vass.prm" vass_units;
    log INFO " [DONE]";
    log INFO "> Reading trail...";
    let trail_asserts = parse_spin_trail trail_filename dom ctx ctr_ctx in
    let num_layers = (List.length trail_asserts) in
    let print_row i exprs =
        Printf.printf "  %d. " i;
        List.iter (fun e -> Printf.printf "%s " (expr_s e)) exprs;
        Printf.printf "\n"
    in
    List.iter2 print_row (range 0 (List.length trail_asserts)) trail_asserts;
    log INFO " [DONE]";
    log INFO "> Simulating counter example in VASS...";
    assert (1 = (Hashtbl.length xducers));
    let proc_xducer = List.hd (hashtbl_vals xducers) in
    let asserts = create_path ctx#get_shared proc_xducer num_layers in
    let decls = expr_list_used_vars asserts in
    List.iter (fun e -> Printf.printf "%s\n" (var_to_smt e)) decls;
    List.iter (fun e -> Printf.printf "(assert %s)\n" (expr_to_smt e)) asserts;
    log INFO " [DONE]";
    let _ = solver#stop in ()
;;
