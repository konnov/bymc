(**
 Various options that control the behaviour of schema checkers.

 Igor Konnov, 2016
 *)

(** is the control flow optimization enabled? *)
val is_flow_opt_enabled: unit -> bool
(** is the reachability implementation enabled *)
val is_reach_opt_enabled: unit -> bool

(** enable/disable the control flow optimization *)
val set_flow_opt: bool -> unit
(** enable/disable the reachability *)
val set_reach_opt: bool ->unit

