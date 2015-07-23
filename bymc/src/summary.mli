(** Constructing a summary similar to SymbSkel, but by enumerating SMT
    models instead of a call to NuSMV.
 
    Igor Konnov, 2014
 *)

(** construct a summary of a single process *)
val summarize:
    Runtime.runtime_t -> Program.program_t -> Spin.token SpinIr.proc
        -> SymbSkel.Sk.skel_t


(** construct summaries of all processes, find reachable states,
    optimize guards, and merge all summaries into one skeleton
 *)
val summarize_optimize_fuse:
    Runtime.runtime_t -> Program.program_t -> SymbSkel.Sk.skel_t

