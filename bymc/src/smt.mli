(**
    Interface to SMT.

    @author Igor Konnov, 2012-2014
 *)

exception Smt_error of string

module Q: sig
    type query_result_t =
        | Cached    (** the query is cached, once 'submit' is invoked,
                         the result will be available for the same query *)
        | NoResult (** nothing is associated with the query *)
        | Result of (Spin.token SpinIr.expr)
                     (** the result of a previously cached query *)

    type query_t

    val query_result_s: query_result_t -> string

    val try_get: query_t -> Spin.token SpinIr.expr -> query_result_t

    val print_contents: query_t -> unit
end


(* An abstract interface to an SMT solver *)
class virtual smt_solver:
    object
        (** fork a new process that executes 'yices' *)
        method virtual start: unit

        (** stop the solver process *)
        method virtual stop: unit

        (** reset the solver *)
        method virtual reset: unit

        (** add a comment (free of side effects) *)
        method virtual comment: string -> unit

        (** declare a variable *)
        method virtual append_var_def: SpinIr.var -> SpinIr.data_type -> unit

        (** Add an expression.
            @return an assertion id, if set_collect_asserts was called with true
         *)
        method virtual append_expr: Spin.token SpinIr.expr -> int

        (** push the context *)
        method virtual push_ctx: unit

        (** pop the context *)
        method virtual pop_ctx: unit

        (** get the number of pushes minus number of pops made so far *)
        method virtual get_stack_level: int

        (** check, whether the current context is satisfiable.
            @return true if sat
         *)
        method virtual check: bool

        (** ask the solver to provide a model of sat *)
        method virtual set_need_model: bool -> unit

        (** check, whether the solver is going to construct a sat model *)
        method virtual get_need_model: bool

        method virtual get_model_query: Q.query_t

        method virtual submit_query: Q.query_t -> Q.query_t

        (** track the assertions, in order to collect unsat cores *)
        method virtual set_collect_asserts: bool -> unit

        (** are the assertions collected *)
        method virtual get_collect_asserts: bool

        (** get an unsat core, which is the list of assertion ids
            that were provided by the solver with append_expr *)
        method virtual get_unsat_cores: int list

        (** indicate, whether debug information is needed *)
        method virtual set_debug: bool -> unit
    end

(**
    An interface to SMT, which must be as abstract as possible.

    @author Igor Konnov
 *)
class yices_smt: string ->
    object
        inherit smt_solver

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
        method set_need_model: bool -> unit

        (** check, whether the solver is going to construct a sat model *)
        method get_need_model: bool

        method get_model_query: Q.query_t

        method submit_query: Q.query_t -> Q.query_t

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
