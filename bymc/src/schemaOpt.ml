
(** is the control flow optimization enabled *)
let flow_opt_enabled = ref true
(** is the reachability optimization enabled *)
let reach_opt_enabled = ref true
(** is the adaptive reachability optimization enabled *)
let ada_reach_opt_enabled = ref true
(** how often to try to switch between the reachability
    and non-reachability optimizations (in the adaptive mode) *)
let ada_reach_adapt_after = ref 3

let is_flow_opt_enabled _ = !flow_opt_enabled
let set_flow_opt enabled = flow_opt_enabled := enabled

let is_reach_opt_enabled _ = !reach_opt_enabled
let set_reach_opt enabled = reach_opt_enabled := enabled

let is_adaptive_reach_opt_enabled _ = !ada_reach_opt_enabled
let set_adaptive_reach_opt enabled = ada_reach_opt_enabled := enabled

let get_ada_reach_adapt_after _ = !ada_reach_adapt_after
let set_ada_reach_adapt_after n = ada_reach_adapt_after := n

