open Smt

(**
    A dummy solver that always returns unsat.
    It is used for isolating memory leaks in our code, not in the solver.
    The first argument is the solver name.
    The second argument is a filename that stores a sequence of 0s and 1s
    that is fed to the user as the responses to sat queries.
    As soon as the sequence is over, the solver always returns unsat.

    In order to record a trace from a live execution, run the tool with
    the following SMT options: --smt 'lib2|z3|-in|-smt2' -O smt.log=1
    A trace of sat responses will be recorded into the file smt-sat-trace.num

    @author Igor Konnov
 *)
class dummy_smt: string -> string ->
    object
        inherit smt_solver

        method get_name: string

        (** start the solver *)
        method start: unit

        (** stop the solver process *)
        method stop: unit

        (** reset the solver *)
        method reset: unit

        (** make a copy of the solver object without starting the new copy *)
        method clone_not_started: ?logic:string -> string -> smt_solver

        (**
         Set a theory. In this implementation, the method is doing nothing.

         @param theory name as in the SMTLIB2 standard.
         *)
        method set_logic: string -> unit

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

        (** set incremental mode *)
        method set_incremental_mode: bool -> unit

        (** is the incremental mode on? *)
        method get_incremental_mode: bool

        (** ask the solver to provide a model of sat *)
        method set_need_model: bool -> unit

        (** check, whether the solver is going to construct a sat model *)
        method get_need_model: bool

        (** ask the solver to provide an unsat core *)
        method set_need_unsat_cores: bool -> unit

        (** check, whether the solver is going to produce an unsat core *)
        method get_need_unsat_cores: bool

        method get_model_query: Q.query_t

        method submit_query: Q.query_t -> Q.query_t

        (** track the assertions, in order to collect unsat cores *)
        method set_collect_asserts: bool -> unit

        (** are the assertions collected *)
        method get_collect_asserts: bool

        (** get an unsat core, which is the list of assertion ids
            that were provided by the solver with append_expr *)
        method get_unsat_cores: int list

        (** indicate, whether to log all output to a text file (default: no) *)
        method set_enable_log: bool -> unit

        method get_enable_log: bool

        (** Indicate, whether to wait for response from the solver for each
            expression. It does not have any effect with yices, as it always
            has to be synchronized in a lockstep.
         *)
        method set_enable_lockstep: bool -> unit

        method get_enable_lockstep: bool

        (** indicate, whether debug information is needed *)
        method set_debug: bool -> unit
    end

