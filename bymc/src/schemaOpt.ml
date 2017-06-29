
module F = struct
    (** is the incremental mode enabled *)
    let incremental = ref true

    (** is the control flow optimization enabled *)
    let flow_opt_enabled = ref true
    (** is the reachability optimization enabled *)
    let reach_opt_enabled = ref true
    (** is the adaptive reachability optimization enabled *)
    let ada_reach_opt_enabled = ref true
    (** how often to try to switch between the reachability
        and non-reachability optimizations (in the adaptive mode) *)
    let ada_reach_adapt_after = ref 3
    (** do we introduce predicates for each guard when switching context? *)
    let use_guard_predicates = ref true
end

let is_incremental _ =
    !F.incremental

let set_incremental b =
    F.incremental := b

let is_flow_opt_enabled _ =
    !F.flow_opt_enabled

let set_flow_opt enabled =
    F.flow_opt_enabled := enabled

let is_reach_opt_enabled _ =
    !F.reach_opt_enabled

let set_reach_opt enabled =
    F.reach_opt_enabled := enabled

let is_adaptive_reach_opt_enabled _ =
    !F.ada_reach_opt_enabled

let set_adaptive_reach_opt enabled =
    F.ada_reach_opt_enabled := enabled

let get_ada_reach_adapt_after _ =
    !F.ada_reach_adapt_after

let set_ada_reach_adapt_after n =
    F.ada_reach_adapt_after := n

let use_guard_predicates _ =
    !F.use_guard_predicates

let set_use_guard_predicates b =
    F.use_guard_predicates := b

