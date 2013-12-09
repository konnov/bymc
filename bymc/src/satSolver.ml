(*
 An interface to a SAT solver that hides a way we interact
 with the solver.

 Igor Konnov, 2011
 *)

open Printf
open Unix

open Accums
open Dimacs

(*
 An offline solver that supports the DIMACS format.
 It provides a simple interface to fill in the problem.

 It expects that the output of a solver is written
 into the file solver.out
 *)
module DimacsSatSolver =
    struct
        type state = {
            id: string;
            started: bool; n_vars: int; n_clauses: int;
            file_open: bool; file: out_channel ref;
            iter: int;
            model: IntSet.t ref
        }

        type satisfiability = SAT | UNSAT | UNKNOWN
        exception IllegalState of string
        exception SatSolverError of string

        let mk_filename name = name

        let open_file id flags =
            (open_out_gen flags 0o666 (mk_filename "problem.body"))

        let make id =
            { id = id; started = true; n_vars = 0; n_clauses = 0;
              iter = 1;
              model = ref (IntSet.empty);
              file_open = true;
              file = ref (open_file id [Open_trunc; Open_creat; Open_wronly]) }

        let init_if_needed st =
            if st.started
            then if st.file_open
                then st
                else
                    { st with file_open = true;
                      iter = st.iter + 1;
                      file = ref (open_file st.id [Open_append; Open_wronly])
                    }
            else make st.id

        let resume _ _ =
            raise (IllegalState "DimacsSolver.resume is not supported")

        let add_lit st num sign =
            let it_state = init_if_needed st in
            let new_state = { it_state with n_vars = (max num it_state.n_vars) } 
            in
            fprintf !(it_state.file) "%s%s "
                (if sign then "" else "-")
                (string_of_int num);
            new_state

        let flush_clause st =
            let it_state = init_if_needed st in
            fprintf !(it_state.file) " 0\n";
            { it_state with n_clauses = it_state.n_clauses + 1 }

        let solve st =
            if not st.started
            then raise (IllegalState "The solver is not started");
            if not st.file_open
            then raise (IllegalState "No variables or clauses have been added");

            close_out !(st.file);
            let head_f = open_out (mk_filename "problem.head") in
            assert (st.n_vars > 0);
            assert (st.n_clauses > 0);
            fprintf head_f "p cnf %d %d\n" st.n_vars st.n_clauses;
            close_out head_f;

            let res_state = { st with file_open = false } in

            flush_all(); (* flush all the output immediately *)
            let cmd = sprintf "picosat -o solver_out %s" st.id in
            let stat = Unix.system cmd in 
            match stat with
              | Unix.WEXITED 127 -> 
                    raise (SatSolverError "Error executing shell command")
              | Unix.WEXITED 10 -> (res_state, SAT)
              | Unix.WEXITED 20 -> (res_state, UNSAT)
              | Unix.WEXITED n ->
                    let msg = sprintf "Error when executing the solver: %d" n
                    in raise (SatSolverError msg)
              | _ ->
                     raise (SatSolverError "The SAT solver was interrupted")


        let read_model state max_id =
            let filename = mk_filename "solver.out" in
            let valuation = Dimacs.read_sat_result filename max_id in
            { state with model = ref (Dimacs.valuation_as_set valuation) }


        let model state var_id = IntSet.mem var_id !(state.model)

        let reset state =
            init_if_needed { state with started = false }
        
        let get_n_clauses state = state.n_clauses

        let get_n_vars state = state.n_vars
    end

