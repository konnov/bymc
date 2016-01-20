
(** is the control flow optimization enabled *)
let flow_opt_enabled = ref true
(** is the reachability implementation enabled *)
let reach_opt_enabled = ref true

let is_flow_opt_enabled _ = !flow_opt_enabled
let set_flow_opt enabled = flow_opt_enabled := enabled

let is_reach_opt_enabled _ = !reach_opt_enabled
let set_reach_opt enabled = reach_opt_enabled := enabled

