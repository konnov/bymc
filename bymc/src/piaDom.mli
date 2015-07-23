open AbsBasics
open Program
open Spin
open SpinIr
open Smt
open VarRole

class pia_domain: Spin.token expr list ->
    object
        method print: unit

        method length: int

        method map_concrete: smt_solver -> Spin.token expr -> Spin.token expr

        method expr_is_concretization: Spin.token expr -> int -> Spin.token expr

        method find_abs_vals:
            abs_type -> smt_solver -> Spin.token expr -> (SpinIr.var * int) list list

        (*
          distribute n abstract values x_i over the abstract domain s.t.
          sum_{i=1}^n \gamma(x_i) = num_active_processes
         *)
        method scatter_abs_vals: smt_solver -> Spin.token expr -> int -> int list list
    end


val create: smt_solver -> var_role_tbl -> program_t -> pia_domain

