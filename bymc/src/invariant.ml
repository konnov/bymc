open Printf

open Debug
open Ltl
open Refinement
open Runtime
open Spin
open SpinIr
open SpinIrImp

let check_invariant rtm xducers_prog inv_name =
    let solver = rtm#solver and caches = rtm#caches in
    let ctr_ctx_tbl = caches#analysis#get_pia_ctr_ctx_tbl in
    let aprops = Program.get_atomics xducers_prog in
    let inv_expr = match Program.StringMap.find inv_name aprops with
    | PropGlob e -> e
    | _ -> raise (Failure ("Invariant must be a global expression: " ^ inv_name))
    in
    log INFO (sprintf "Check the invariant candidate:\n %s\n\n"
        (expr_s inv_expr));
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


let check_all_invariants rtm prog =
    (* the atomic must be taken from the original program
        before the abstraction *)
    let fold_invs name ae lst =
        if is_invariant_atomic name then name :: lst else lst
    in
    let invs = Program.StringMap.fold fold_invs (Program.get_atomics prog) []
    in
    rtm#solver#push_ctx;
    rtm#solver#comment "check_all_invariants";
    List.iter (check_invariant rtm prog) invs;
    rtm#solver#pop_ctx

