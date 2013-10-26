open Printf

open Accums
open Debug
open Ltl
open Program
open PiaCtrRefinement
open Runtime
open Spin
open SpinIr
open SpinIrImp

let check_invariant rtm xducers_prog inv_name =
    let solver = rtm#solver and caches = rtm#caches in
    let ctr_ctx_tbl = caches#analysis#get_pia_ctr_ctx_tbl in
    let aprops = Program.get_atomics xducers_prog in
    let inv_expr =
        match Accums.StringMap.find inv_name aprops with
        | PropGlob e -> e
        | _ -> raise (Failure
            ("Invariant must be a global expression: " ^ inv_name))
    in
    log INFO (sprintf "Check the invariant candidate:\n %s\n\n"
        (expr_s inv_expr));
    let inv, not_inv = inv_expr, UnEx (NEG, inv_expr) in
    let check_proc_step proctype (* for a step by each proctype *) =
        let step_asserts =
            [([inv], [], (StringMap.singleton "proc" proctype));
             ([not_inv], [], StringMap.empty)] in
        solver#set_collect_asserts true;
        solver#set_need_evidence true;
        solver#push_ctx;
        simulate_in_smt solver xducers_prog ctr_ctx_tbl 1;
        let res, smt_rev_map = check_trail_asserts solver step_asserts 1 in
        solver#pop_ctx;
        solver#set_collect_asserts false;
        if res then begin
            printf "Expression %s is not an invariant!\n\n" inv_name;
            printf "Here is an example:\n";
            print_vass_trace xducers_prog solver 2;
            raise (Failure (sprintf "Expression %s is not an invariant!" inv_name))
        end
    in
    List.iter check_proc_step
        (List.map (fun c -> c#proctype_name) ctr_ctx_tbl#all_ctxs)


let check_all_invariants rtm prog =
    (* the atomic must be taken from the original program
        before the abstraction *)
    let fold_invs name ae lst =
        if is_invariant_atomic name then name :: lst else lst
    in
    let invs = Accums.StringMap.fold fold_invs (Program.get_atomics prog) []
    in
    rtm#solver#push_ctx;
    rtm#solver#comment "check_all_invariants";
    List.iter (check_invariant rtm prog) invs;
    rtm#solver#pop_ctx

