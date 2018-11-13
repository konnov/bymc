(**
 Various options that control the behaviour of schema checkers.

 Igor Konnov, 2016
 *)

(** is the solver working in the incremental mode? *)
val is_incremental: unit -> bool
(** set the solver to the incremental mode *)
val set_incremental: bool -> unit

(** is the control flow optimization enabled? *)
val is_flow_opt_enabled: unit -> bool
(** is the reachability optimization enabled *)
val is_reach_opt_enabled: unit -> bool
(** is the adaptive reachability optimization enabled *)
val is_adaptive_reach_opt_enabled: unit -> bool

(** enable/disable the control flow optimization *)
val set_flow_opt: bool -> unit
(** enable/disable the reachability optimization *)
val set_reach_opt: bool ->unit
(** enable/disable the reachability optimization *)
val set_adaptive_reach_opt: bool -> unit

(** how often to try to switch between the reachability
    and non-reachability optimizations (in the adaptive mode) *)
val get_ada_reach_adapt_after: unit -> int
(** set the number of rounds to wait before switching reachability on/off *)
val set_ada_reach_adapt_after: int -> unit

(** do we associate a predicate with every guard when switching contexts?
    (see BUGFIX-20160628)
 *)
val use_guard_predicates: unit -> bool
(** associate a predicate with every guard when switching a context *)
val set_use_guard_predicates: bool -> unit

(** is the total number of schemas always computed,
    even if there are too many (default: no) *)
val is_always_compute_nschemas: unit -> bool

(* enable/disable computation of the number of schemas *)
val set_always_compute_nschemas: bool -> unit

