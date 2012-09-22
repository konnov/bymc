
open Printf;;

open AbsInterval;;
open AbsCounter;;
open Refinement;;
open Smt;;

open Spin;;
open SpinIr;;
open SpinIrImp;;
open Ltl;;
open Writer;;
open Accums;;
open Debug;;

let write_to_file name units =
    let fo = open_out name in
    List.iter (write_unit fo 0) units;
    close_out fo
;;

(* units -> interval abstraction -> counter abstraction *)
let do_abstraction is_first_run units =
    if is_first_run
    then begin 
        (* wipe the files left from other refinement sessions *)
        close_out (open_out "cegar_decl.inc");
        close_out (open_out "cegar_pre.inc");
        close_out (open_out "cegar_post.inc")
    end;
    let ctx = mk_context units in
    let solver = ctx#run_solver in
    let dom = mk_domain solver ctx units in

    log INFO "> Constructing interval abstraction";
    let intabs_units = do_interval_abstraction ctx dom solver units in
    write_to_file "abs-interval.prm" intabs_units;
    log INFO "[DONE]";
    log INFO "> Constructing counter abstraction";
    let ctr_ctx = new ctr_abs_ctx dom ctx in
    let funcs = new abs_ctr_funcs dom ctx ctr_ctx solver in
    let ctrabs_units, _, _, _ =
        do_counter_abstraction ctx dom solver ctr_ctx funcs intabs_units in
    write_to_file "abs-counter.prm" ctrabs_units;
    log INFO "[DONE]";
    let _ = solver#stop in
    ctrabs_units
;;

let construct_vass units =
    let ctx = mk_context units in
    ctx#set_hack_shared true; (* XXX: hack mode on *)
    let solver = ctx#run_solver in

    let dom = mk_domain solver ctx units in
    log INFO "> Constructing interval abstraction...";
    let intabs_units = do_interval_abstraction ctx dom solver units in
    log INFO "  [DONE]";
    log INFO "> Constructing VASS and transducers...";
    let ctr_ctx = new ctr_abs_ctx dom ctx in
    let vass_funcs = new vass_funcs dom ctx ctr_ctx solver in
    let vass_units, xducers, atomic_props, ltl_forms =
        do_counter_abstraction ctx dom solver ctr_ctx vass_funcs intabs_units
    in
    write_to_file "abs-vass.prm" vass_units;
    log INFO "  [DONE]"; flush stdout;

    (ctx, solver, dom, ctr_ctx, xducers, atomic_props, ltl_forms)
;;

let print_vass_trace t_ctx solver num_states = 
    printf "Here is a CONCRETE trace in VASS violating the property.\n";
    printf "See concrete values of parameters at the state 0.\n\n";
    let vals = parse_smt_evidence t_ctx solver in
    let print_st i =
        printf "%d: " i;
        pretty_print_exprs (Hashtbl.find vals i);
        printf "\n";
    in
    List.iter (print_st) (range 0 num_states)
;;

let check_invariant inv_name units =
    let (ctx, solver, dom, ctr_ctx, xducers, aprops, ltl_forms)
        = construct_vass units in
    let inv_expr =
        try
            match Hashtbl.find aprops inv_name with
            | PropGlob e -> e
            | _ -> raise (Failure (sprintf "Invariant %s is not a global property" inv_name))
        with Not_found ->
            raise (Failure (sprintf "No atomic proposition %s" inv_name))
    in
    printf "The invariant candidate to check:\n %s\n\n" (expr_s inv_expr);
    let inv, not_inv = inv_expr, UnEx (NEG, inv_expr) in
    let step_asserts = [[Expr (0, inv)]; [Expr (1, not_inv)]] in
    let rev_map = Hashtbl.create 10 in
    Hashtbl.add rev_map 0 (0, inv); Hashtbl.add rev_map 1 (1, not_inv);
    solver#set_collect_asserts true;
    solver#set_need_evidence true;
    let res, smt_rev_map =
        (simulate_in_smt solver ctx ctr_ctx xducers step_asserts rev_map 1) in
    if not res
    then printf "The invariant holds!\n\n"
    else begin
        printf "The invariant is violated!\n\nHere is an example:\n";
        print_vass_trace ctx solver 2
    end;
    solver#set_collect_asserts false;
;;

(* FIXME: refactor it, the decisions must be clear and separated *)
(* units -> interval abstraction -> vector addition state systems *)
let do_refinement trail_filename units =
    let (ctx, solver, dom, ctr_ctx, xducers, aprops, ltls) = construct_vass units in
    let fairness = find_fairness_assertion aprops ltls in
    let inv_forms = find_invariants aprops in
    log INFO "> Reading trail...";
    let trail_asserts, loop_asserts, rev_map =
        parse_spin_trail trail_filename dom ctx ctr_ctx in
    log INFO (sprintf "  %d step(s)" ((List.length trail_asserts) - 1));
    (* FIXME: deal somehow with this stupid message *)
    if (List.length trail_asserts) <= 1
    then raise (Failure "The system loops forever at the initial state");
    log INFO "  [DONE]"; flush stdout;
    log INFO "> Simulating counter example in VASS..."; flush stdout;
    assert (1 = (Hashtbl.length xducers));
    let sim_prefix n_steps =
        solver#append (sprintf ";; Checking the path 0:%d" n_steps);
        let res, _ = simulate_in_smt
                solver ctx ctr_ctx xducers trail_asserts rev_map n_steps in
        if res
        then begin
            log INFO (sprintf "  %d step(s). OK" n_steps);
            flush stdout;
            false
        end else begin
            log INFO
            (sprintf "  %d step(s). The path 0:%d is spurious." n_steps n_steps);
            flush stdout;
            true
        end
    in
    let check_trans st = 
        let step_asserts = list_sub trail_asserts st 2 in
        solver#append
            (sprintf ";; Checking the transition %d -> %d" st (st + 1));
        solver#set_collect_asserts true;
        let res, smt_rev_map =
            (simulate_in_smt solver ctx ctr_ctx xducers step_asserts rev_map 1)
        in
        solver#set_collect_asserts false;
        if not res
        then begin
            log INFO (sprintf "  The transition %d -> %d is spurious."
                    st (st + 1));
            flush stdout;
            refine_spurious_step solver smt_rev_map st;
            true
        end else begin
            log INFO
                (sprintf "  The transition %d -> %d is OK." st (st + 1));
            flush stdout;
            (*print_vass_trace ctx solver 2;*)
            false
        end
    in
    let num_states = (List.length trail_asserts) in
    solver#set_need_evidence true;
    (* check the path first *)
    if not (sim_prefix (num_states - 1))
    then begin
        log INFO "  The counter-example is not spurious!";
        print_vass_trace ctx solver num_states
    end else begin
        log INFO "  Trying to find a spurious transition...";
        flush stdout;
        let sp_st =
            try List.find check_trans (range 0 (num_states - 1))
            with Not_found -> -1
        in
        if sp_st = -1
        then begin
            let spur_loop =
                check_loop_unfair solver rev_map fairness inv_forms loop_asserts in
            if spur_loop
            then log INFO "The loop is unfair. Refined."
            else begin
                log INFO "The loop is okay";

                log INFO "Sorry, I am afraid I cannot do that, Dave.";
                log INFO "I need a human assistance to find an invariant.";
                log INFO "  Trying to find the shortest spurious path for you...";
                (* then check its prefixes, from the shortest to the longest *)
                let short_len = List.find sim_prefix (range 1 num_states) in
                log INFO (sprintf "  The shortest path is 0:%d" short_len);
                flush stdout;
            end
        end
    end;
    log INFO "  [DONE]";
    log INFO "  Regenerating the counter abstraction";
    (* formulas must be regenerated *)
    let _ = do_abstraction false units in
    let _ = solver#stop in ()
;;
