open Infra
open Smt

class runtime_t (i_solver: smt_solver) (i_caches: pass_caches) =
    object
        method solver = i_solver

        method caches = i_caches
    end

