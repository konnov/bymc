
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
    log INFO "  [DONE]";
    log INFO "> Constructing VASS and transducers...";
    let ctr_ctx = new ctr_abs_ctx dom ctx in
    let vass_funcs = new vass_funcs dom ctx ctr_ctx solver in
    let vass_units, xducers =
        do_counter_abstraction ctx dom solver ctr_ctx vass_funcs intabs_units
    in
    write_to_file "abs-vass.prm" vass_units;
    log INFO "  [DONE]";
    log INFO "> Reading trail...";
    let trail_asserts = parse_spin_trail trail_filename dom ctx ctr_ctx in
    log INFO (sprintf "  %d step(s)" ((List.length trail_asserts) - 1));
    log INFO "  [DONE]";
    log INFO "> Simulating counter example in VASS...";
    assert (1 = (Hashtbl.length xducers));
    let sim_prefix n_steps =
        if simulate_in_smt solver ctx ctr_ctx xducers trail_asserts n_steps
        then begin
            log INFO (sprintf "  %d step(s). OK" n_steps);
            flush stdout;
            false
        end else begin
            log INFO
            (sprintf "  %d step(s). The path 0:%d is spurious." n_steps n_steps);
            true
        end
    in
    begin
        solver#set_need_evidence true;
        let num_states = (List.length trail_asserts) in
        try
            (* check the path first *)
            if not (sim_prefix (num_states - 1))
            then raise Not_found;
            log INFO "  Trying to find the shortest spurious path...";
            (* then check its prefixes, from the shortest to the longest *)
            let spurious_len = List.find sim_prefix (range 1 num_states) in
            let step_asserts = list_sub trail_asserts (spurious_len - 1) 2 in
            solver#set_collect_asserts true;
            if not (simulate_in_smt solver ctx ctr_ctx xducers step_asserts 1)
            then begin
                log INFO
                    (sprintf "  The transition %d -> %d is spurious."
                        (spurious_len - 1) spurious_len)
            end else begin
                log INFO
                    (sprintf "  The transition %d -> %d is NOT spurious."
                        (spurious_len - 1) spurious_len);
                log INFO "Sorry, I am afraid I cannot do that, Dave.";
                log INFO "I need a human assistance to find an invariant."
            end;
            solver#set_collect_asserts false;
        with Not_found ->
        begin
            log INFO "  The counter-example is not spurious!";
            let vals = parse_smt_evidence solver in
            let print_st i =
                printf "%d: " i;
                pretty_print_exprs (Hashtbl.find vals i);
                printf "\n";
            in
            List.iter (print_st) (range 0 num_states)
        end
    end;
    log INFO "  [DONE]";
    let _ = solver#stop in ()
;;
