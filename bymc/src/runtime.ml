open Smt

class runtime_t (i_solver: yices_smt) =
    object
        method get_solver = i_solver
    end

