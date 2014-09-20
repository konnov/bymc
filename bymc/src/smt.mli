(**
    An interface to SMT, which must be as abstract as possible.
 *)

class yices_smt:
    object
        method start: unit

        method stop: unit

        method comment: string -> unit

        method append_var_def: SpinIr.var -> SpinIr.data_type -> unit

        method append_expr: Spin.token SpinIr.expr -> int

        method push_ctx: unit

        method pop_ctx: unit

        method get_stack_level: int

        method check: bool

        method set_need_evidence: bool -> unit

        method get_need_evidence: bool

        method get_evidence: string list

        method set_collect_asserts: bool -> unit

        method get_collect_asserts: bool

        method get_unsat_cores: int list

        method set_debug: bool -> unit
    end
