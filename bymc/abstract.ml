
open Printf

open Accums
open AbsInterval
open AbsCounter
open Infra
open Ltl
open PiaDataCtx
open PiaCtrCtx
open Program
open Refinement
open Smt
open Spin
open SpinIr
open SpinIrImp
open VarRole
open Writer

open BddPass

open Debug

let write_to_file externalize_ltl name units type_tab =
    let fo = open_out name in
    let save_unit = function
        | Ltl (form_name, form) as u->
            (* Spin 6.2 supports inline formulas no longer than 1024 chars.
               It produces arbitrary compilation errors for those longer than
               its authors expected. We thus put the formula into a file. *)
            if externalize_ltl
            then begin
                let out = open_out (sprintf "%s.ltl" form_name) in
                fprintf out "%s\n" (expr_s form);
                close_out out
            end else
                write_unit type_tab fo 0 u
        | _ as u -> write_unit type_tab fo 0 u
    in
    List.iter save_unit units;
    close_out fo


(* units -> interval abstraction -> counter abstraction *)
let do_abstraction solver is_first_run bdd_pass prog =
    solver#push_ctx;
    solver#comment "do_abstraction";
    if is_first_run
    then begin 
        (* wipe out the files left from previous refinement sessions *)
        close_out (open_out "cegar_decl.inc");
        close_out (open_out "cegar_pre.inc");
        close_out (open_out "cegar_post.inc")
    end;
    let analysis = new analysis_cache in
    let roles = identify_var_roles prog in
    analysis#set_var_roles roles;
    let dom = PiaDom.create solver roles prog in
    analysis#set_pia_dom dom;
    let pia_data = new pia_data_ctx roles in
    analysis#set_pia_data_ctx pia_data;
    let caches = new pass_caches analysis (new proc_struc_cache) in

    log INFO "> Constructing interval abstraction";
    let intabs_prog = do_interval_abstraction solver caches prog in
    write_to_file false "abs-interval.prm"
        (units_of_program intabs_prog) (get_type_tab intabs_prog);
    log INFO "[DONE]";
    if bdd_pass then begin
        log INFO "> Constructing BDDs...";
        let _ = SkelStruc.pass caches intabs_prog in
        let xducer_prog = SmtXducerPass.do_xducers caches intabs_prog in
        BddPass.transform_to_bdd solver caches xducer_prog;
        log INFO "[DONE]";
    end;
    log INFO "> Constructing counter abstraction";
    analysis#set_pia_ctr_ctx_tbl (new ctr_abs_ctx_tbl dom roles intabs_prog);
    let funcs = new abs_ctr_funcs dom intabs_prog solver in
    let ctrabs_prog = do_counter_abstraction funcs solver caches intabs_prog in
    write_to_file true "abs-counter.prm"
        (units_of_program ctrabs_prog) (get_type_tab ctrabs_prog);
    log INFO "[DONE]";
    solver#pop_ctx;
    ctrabs_prog


let make_vass_xducers solver embed_inv prog =
    solver#push_ctx;
    solver#comment "make_vass_xducers";
    let analysis = new analysis_cache in
    let roles = identify_var_roles prog in
    analysis#set_var_roles roles;
    let dom = PiaDom.create solver roles prog in
    analysis#set_pia_dom dom;
    let pia_data = new pia_data_ctx roles in
    pia_data#set_hack_shared true;
    analysis#set_pia_data_ctx pia_data;
    let caches = new pass_caches analysis (new proc_struc_cache) in

    log INFO "> Constructing interval abstraction...";
    let intabs_prog = do_interval_abstraction solver caches prog in
    write_to_file false "abs-interval.prm"
        (units_of_program intabs_prog) (get_type_tab intabs_prog);
    log INFO "  [DONE]";
    log INFO "> Constructing VASS...";
    analysis#set_pia_ctr_ctx_tbl (new ctr_abs_ctx_tbl dom roles intabs_prog);
    let vass_funcs = new vass_funcs dom intabs_prog solver in
    vass_funcs#set_embed_inv embed_inv;
    let vass_prog =
        do_counter_abstraction vass_funcs solver caches intabs_prog in
    write_to_file false "abs-vass.prm"
        (units_of_program vass_prog) (get_type_tab vass_prog);
    log INFO "> Constructing SMT transducers...";
    let xducer_prog = SmtXducerPass.do_xducers caches vass_prog in
    write_to_file false "abs-xducers.prm"
        (units_of_program xducer_prog) (get_type_tab xducer_prog);
    log INFO "  [DONE]"; flush stdout;
    solver#pop_ctx;
    (caches, xducer_prog)


let check_invariant solver prog inv_name =
    let (caches, xducers_prog) = make_vass_xducers solver false prog in
    let ctr_ctx_tbl = caches#get_analysis#get_pia_ctr_ctx_tbl in
    let aprops = (Program.get_atomics xducers_prog) in
    let inv_expr = match Program.StringMap.find inv_name aprops with
    | PropGlob e -> e
    | _ -> raise (Failure ("Invariant must be a global expression: " ^ inv_name))
    in
    printf "Check the invariant candidate:\n %s\n\n" (expr_s inv_expr);
    let inv, not_inv = inv_expr, UnEx (NEG, inv_expr) in
    let check_proc_step proctype (* for a step by each proctype *) =
        let step_asserts =
            [(proctype, [Expr (0, inv)]); (proctype, [Expr (1, not_inv)])] in
        let rev_map = Hashtbl.create 10 in
        Hashtbl.add rev_map 0 (0, inv); Hashtbl.add rev_map 1 (1, not_inv);
        solver#set_collect_asserts true;
        solver#set_need_evidence true;
        let res, smt_rev_map =
            (simulate_in_smt solver xducers_prog ctr_ctx_tbl step_asserts rev_map 1) in
        solver#set_collect_asserts false;
        if res then begin
            printf "Expression %s is not an invariant!\n\n" inv_name;
            printf "Here is an example:\n";
            print_vass_trace xducers_prog solver 2;
            raise (Failure (sprintf "Expression %s is not an invariant!" inv_name))
        end
    in
    List.iter check_proc_step
        (List.map (fun c -> c#abbrev_name) ctr_ctx_tbl#all_ctxs)


let check_all_invariants solver prog =
    let fold_invs name ae lst =
        if is_invariant_atomic name then name :: lst else lst
    in
    let invs = Program.StringMap.fold fold_invs (Program.get_atomics prog) [] in
    solver#push_ctx;
    solver#comment "check_all_invariants";
    List.iter (check_invariant solver prog) invs;
    solver#pop_ctx

let filter_good_fairness type_tab aprops fair_forms =
    let err_fun f =
        printf "Fairness formula not supported by refinement (ignored): %s\n" 
            (expr_s f);
        Nop ""
    in
    let fair_atoms = List.map (find_fair_atoms err_fun type_tab aprops) fair_forms in
    let filtered = List.filter not_nop fair_atoms in
    printf "added %d fairness constraints\n" (List.length filtered);
    filtered


(* FIXME: refactor it, the decisions must be clear and separated *)
(* units -> interval abstraction -> vector addition state systems *)
let do_refinement solver trail_filename prog =
    solver#push_ctx;
    solver#comment "do_refinement";
    let (caches, xducers_prog) = make_vass_xducers solver true prog in
    let type_tab = Program.get_type_tab xducers_prog in
    let ctx = caches#get_analysis#get_pia_data_ctx in (* TODO: move further *)
    let dom = caches#get_analysis#get_pia_dom in (* TODO: move further *)
    let ctr_ctx_tbl = caches#get_analysis#get_pia_ctr_ctx_tbl in
    let aprops = (Program.get_atomics xducers_prog) in
    let ltl_forms = (Program.get_ltl_forms_as_hash xducers_prog) in
    let inv_forms = find_invariants aprops in
    log INFO "> Reading trail...";
    let trail_asserts, loop_asserts, rev_map =
        parse_spin_trail trail_filename dom ctx ctr_ctx_tbl xducers_prog in
    let total_steps = (List.length trail_asserts) - 1 in
    log INFO (sprintf "  %d step(s)" total_steps);
    (* FIXME: deal somehow with this stupid message *)
    if (List.length trail_asserts) <= 1
    then raise (Failure
        "All processes can do idle steps and stay forever at the initial state");
    log INFO "  [DONE]"; flush stdout;
    log INFO "> Simulating counter example in VASS..."; flush stdout;

    let sim_prefix n_steps =
        solver#append (sprintf ";; Checking the path 0:%d" n_steps);
        let res, _ = simulate_in_smt
                solver xducers_prog ctr_ctx_tbl trail_asserts rev_map n_steps in
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
            (simulate_in_smt solver xducers_prog ctr_ctx_tbl step_asserts rev_map 1)
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
            log INFO (sprintf "  The transition %d -> %d (of %d) is OK."
                    st (st + 1) total_steps);
            flush stdout;
            (*print_vass_trace ctx solver 2;*)
            false
        end
    in
    let num_states = (List.length trail_asserts) in
    solver#set_need_evidence true;
    let refined = ref false in
    (* Try to detect spurious transitions and unfair paths
       (discussed in the TACAS paper) *)
    log INFO "  Trying to find a spurious transition...";
    flush stdout;
    let sp_st =
        try List.find check_trans (range 0 (num_states - 1))
        with Not_found -> -1 in
    if sp_st <> -1
    then begin
        log INFO "(status trace-refined)";
        refined := true
    end else begin
        let fairness =
            filter_good_fairness type_tab aprops (collect_fairness_forms ltl_forms) in
        let spur_loop =
            check_loop_unfair solver xducers_prog ctr_ctx_tbl
                rev_map fairness inv_forms loop_asserts in
        if spur_loop
        then begin
            log INFO "The loop is unfair. Refined.";
            log INFO "(status trace-refined)";
            refined := true;
        end else begin
            log INFO "The loop is fair";

            log INFO "This counterexample does not have spurious transitions or states.";
            log INFO "If it does not show a real problem, provide me with an invariant.";
            log INFO "(status trace-no-refinement)";
            (* this is an experimental feature! *)
            (* then check its prefixes, from the shortest to the longest *)
            if not (sim_prefix (num_states - 1))
            then begin
                log INFO "The path is not spurious.";
                print_vass_trace xducers_prog solver num_states;
                log INFO "(status trace-concrete-example)";
            end else begin
                let short_len = List.find sim_prefix (range 1 num_states) in
                log INFO
                    (sprintf "  The shortest spurious path is 0:%d" short_len);
                flush stdout;
            end
        end
    end;
    log INFO "  [DONE]";
    solver#pop_ctx;
    if !refined
    then begin
        log INFO "  Regenerating the counter abstraction";
        (* formulas must be regenerated *)
        let _ = do_abstraction solver false false prog in ()
    end
