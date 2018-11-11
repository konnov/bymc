(**
    A dummy SMT solver that always returns unsat. In zero seconds!

    @author Igor Konnov, 2018
 *)

open SpinIr

class dummy_smt name input_filename =
    object(self)
        val mutable m_input = Scanf.Scanning.stdin
        val mutable m_eof = true

        inherit Smt.smt_solver

        method get_name = name

        method start =
            m_input <- Scanf.Scanning.open_in input_filename;
            m_eof <- false
        
        method stop = ()

        method reset = ()

        method clone_not_started ?logic new_name =
            (* It is crucial to have the only trace of sat responses.
            So return itself.  *)
            (self :> Smt.smt_solver)

        method set_logic (theory: string): unit = ()

        method append_var_def (v: var) (tp: data_type) = ()

        method comment (line: string) = ()

        method append_expr expr = -1

        method push_ctx = ()

        (** Get the current stack level (nr. of pushes). Use for debugging *)
        method get_stack_level = 0

        method pop_ctx = ()

        method private pop_n n = ()

        method check =
            let num = ref 0 in
            if not m_eof
            then begin
                try Scanf.bscanf m_input "%d " (fun i -> num := i);
                with End_of_file ->
                    Scanf.Scanning.close_in m_input;
                    m_eof <- false
            end;
            !num > 0 (* return sat on any positive input *)


        method set_need_model b = ()

        method get_need_model = false

        method set_need_unsat_cores b = ()

        method get_need_unsat_cores = false
            
        method get_model_query = Smt.Q.new_query (fun e -> "dummy")

        method submit_query (query: Smt.Q.query_t) = query

        method get_collect_asserts = false

        method set_collect_asserts b = ()

        method get_unsat_cores = []

        method set_debug flag = ()

        method set_enable_lockstep b = ()

        method get_enable_lockstep = false

        method set_enable_log b = ()

        method get_enable_log = false

        method set_incremental_mode b = ()

        method get_incremental_mode = false
    end


