(**
    Interface to SMT.

    @author Igor Konnov, 2012-2014
 *)

exception Smt_error of string

(**
    An interface to SMT, which must be as abstract as possible.

    @author Igor Konnov
 *)
class yices_smt:
    object
        (** fork a new process that executes 'yices' *)
        method start: unit

        (** stop the solver process *)
        method stop: unit

        (** reset the solver *)
        method reset: unit

        (** add a comment (free of side effects) *)
        method comment: string -> unit

        (** declare a variable *)
        method append_var_def: SpinIr.var -> SpinIr.data_type -> unit

        (** Add an expression.
            @return an assertion id, if set_collect_asserts was called with true
         *)
        method append_expr: Spin.token SpinIr.expr -> int

        (** push the context *)
        method push_ctx: unit

        (** pop the context *)
        method pop_ctx: unit

        (** get the number of pushes minus number of pops made so far *)
        method get_stack_level: int

        (** check, whether the current context is satisfiable.
            @return true if sat
         *)
        method check: bool

        (** ask the solver to provide a model of sat *)
        method set_need_evidence: bool -> unit

        (** check, whether the solver is going to construct a sat model *)
        method get_need_evidence: bool

        (** get a sat model *)
        method get_evidence: string list

        (** Parse a sat model into expressions.
            @return list of expressions
            @raise Smt_error, if the solver gives something unparseable
        *)
        method get_model:
            (string -> SpinIr.var) (** variable lookup *)
            -> Spin.token SpinIr.expr list

        (** track the assertions, in order to collect unsat cores *)
        method set_collect_asserts: bool -> unit

        (** are the assertions collected *)
        method get_collect_asserts: bool

        (** get an unsat core, which is the list of assertion ids
            that were provided by the solver with append_expr *)
        method get_unsat_cores: int list

        (** indicate, whether debug information is needed *)
        method set_debug: bool -> unit
    end
