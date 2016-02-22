(**
    Classes to integrate with SMT solvers: SMTLIB2, Yices 1.x, Mathsat.

    @author Igor Konnov, 2012-2016
 *)

open Printf
open Str

open BatEnum
open Sexplib

open Debug
open PipeCmd
open SpinTypes
open Spin
open SpinIr
open SpinIrImp

exception Smt_error of string
exception Smt_undefined of string


module Q = struct
    type query_result_t =
        | Cached    (** the query is cached, once 'submit' is invoked,
                         the result will be available for the same query *)
        | Result of (Spin.token SpinIr.expr)
                     (** the result of a previously cached query *)

    type query_t = {
        expr_to_smt_f: token expr -> string;
        frozen: bool;
        tab: (string, query_result_t) Hashtbl.t
    }

    let query_result_s q = function
        | Cached -> "Cached"
        | Result e -> "Result " ^ (q.expr_to_smt_f e)

    let print_contents (q: query_t) =
        let p s r = printf "   %s <- %s\n" s (query_result_s q r) in
        printf "\n ***** query contents *****\n";
        Hashtbl.iter p q.tab

    let new_query expr_to_smt_f = 
        { frozen = false; expr_to_smt_f; tab = Hashtbl.create 10 }

    let copy (q: query_t): query_t =
        { frozen = q.frozen;
            expr_to_smt_f = q.expr_to_smt_f; tab = Hashtbl.copy q.tab }

    let try_get (q: query_t) (key: token expr) =
        let e_s = q.expr_to_smt_f key in
        try
            let res = Hashtbl.find q.tab e_s in
            if q.frozen && res = Cached
            then raise (Smt_error ("No result for (declared) " ^ e_s ))
            else res
        with Not_found ->
            if q.frozen
            then begin
                print_contents q;
                raise (Smt_error ("No result for (undeclared) " ^ e_s))
            end else begin
                Hashtbl.replace q.tab e_s Cached;
                Cached
            end

    let add_result (q: query_t) (nq: query_t) (key: string) (value: token expr) =
        try begin
            let _ = Hashtbl.find q.tab key in
            Hashtbl.replace nq.tab key (Result value);
            nq
        end with Not_found ->
            nq
                
end


(** An abstract interface to an SMT solver *)
class virtual smt_solver =
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

        (** Set incremental mode. Not supported, always on. *)
        method virtual set_incremental_mode: bool -> unit

        (** Is the incremental mode on? In this implementation always on.*)
        method virtual get_incremental_mode: bool

        (** ask the solver to provide a model of sat *)
        method virtual set_need_model: bool -> unit

        (** check, whether the solver is going to construct a sat model *)
        method virtual get_need_model: bool

        (** ask the solver to provide an unsat core *)
        method virtual set_need_unsat_cores: bool -> unit

        (** check, whether the solver is going to produce an unsat core *)
        method virtual get_need_unsat_cores: bool

        method virtual get_model_query: Q.query_t

        method virtual submit_query: Q.query_t -> Q.query_t

        (** track the assertions, in order to collect unsat cores *)
        method virtual set_collect_asserts: bool -> unit

        (** are the assertions collected *)
        method virtual get_collect_asserts: bool

        (** get an unsat core, which is the list of assertion ids
            that were provided by the solver with append_expr *)
        method virtual get_unsat_cores: int list

        (** indicate, whether to log all output to a text file (default: no) *)
        method virtual set_enable_log: bool -> unit

        method virtual get_enable_log: bool

        (** indicate, whether to wait for response from the solver for each
            expression (default: no)
         *)
        method virtual set_enable_lockstep: bool -> unit

        method virtual get_enable_lockstep: bool

        (** indicate, whether debug information is needed (default: no) *)
        method virtual set_debug: bool -> unit
    end


let rec expr_to_smt = function
    | Nop comment -> sprintf ";; %s\n" comment
    | IntConst i -> string_of_int i
    | Var v -> v#mangled_name

    | UnEx (tok, f) ->
        begin match tok with
        | UMIN -> sprintf "(- %s)" (expr_to_smt f)
        | NEG  -> sprintf "(not %s)" (expr_to_smt f)
        | _ ->
            raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
        end

    | BinEx (tok, l, r) ->
        begin match tok with
        | PLUS  -> sprintf "(+ %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MINUS -> sprintf "(- %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MULT  -> sprintf "(* %s %s)" (expr_to_smt l) (expr_to_smt r)
        | DIV   -> sprintf "(div %s %s)" (expr_to_smt l) (expr_to_smt r)
        | MOD   -> sprintf "(mod %s %s)" (expr_to_smt l) (expr_to_smt r)
        | GT    -> sprintf "(> %s %s)" (expr_to_smt l) (expr_to_smt r)
        | LT    -> sprintf "(< %s %s)" (expr_to_smt l) (expr_to_smt r)
        | GE    -> sprintf "(>= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | LE    -> sprintf "(<= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | EQ    -> sprintf "(= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | NE    -> sprintf "(/= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | AND   -> sprintf "(and %s %s)" (expr_to_smt l) (expr_to_smt r)
        | OR    -> sprintf "(or %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | EQUIV -> sprintf "(= %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | IMPLIES -> sprintf "(=> %s %s)"  (expr_to_smt l) (expr_to_smt r)
        | ARR_ACCESS -> sprintf "(%s %s)" (expr_to_smt l) (expr_to_smt r)
        | _ -> raise (Failure
                (sprintf "No idea how to translate '%s' to SMT" (token_s tok)))
        end

    | Phi (lhs, rhs) ->
            raise (Failure "Phi to SMT is not supported")

    | LabelRef (proc_name, lab_name) ->
            raise (Failure "LabelRef to SMT is not supported")


let rec expr_to_smt2 = function
    | Nop comment -> sprintf ";; %s\n" comment
    | IntConst i -> string_of_int i
    | Var v -> v#mangled_name

    | UnEx (tok, f) ->
        begin match tok with
        | UMIN -> sprintf "(- %s)" (expr_to_smt2 f)
        | NEG  -> sprintf "(not %s)" (expr_to_smt2 f)
        | _ ->
            raise (Failure
                (sprintf "No idea how to translate %s to SMT" (token_s tok)))
        end

    | BinEx (tok, l, r) ->
        begin match tok with
        | PLUS  -> sprintf "(+ %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | MINUS -> sprintf "(- %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | MULT  -> sprintf "(* %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | DIV   -> sprintf "(div %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | MOD   -> sprintf "(mod %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | GT    -> sprintf "(> %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | LT    -> sprintf "(< %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | GE    -> sprintf "(>= %s %s)"  (expr_to_smt2 l) (expr_to_smt2 r)
        | LE    -> sprintf "(<= %s %s)"  (expr_to_smt2 l) (expr_to_smt2 r)
        | EQ    -> sprintf "(= %s %s)"  (expr_to_smt2 l) (expr_to_smt2 r)
        | NE    -> sprintf "(not (= %s %s))"  (expr_to_smt2 l) (expr_to_smt2 r)
        | AND   -> sprintf "(and %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | OR    -> sprintf "(or %s %s)"  (expr_to_smt2 l) (expr_to_smt2 r)
        | EQUIV -> sprintf "(= %s %s)"  (expr_to_smt2 l) (expr_to_smt2 r)
        | IMPLIES -> sprintf "(=> %s %s)"  (expr_to_smt2 l) (expr_to_smt2 r)
        | ARR_ACCESS -> sprintf "(select %s %s)" (expr_to_smt2 l) (expr_to_smt2 r)
        | _ -> raise (Failure
                (sprintf "No idea how to translate '%s' to SMT" (token_s tok)))
        end

    | Phi (lhs, rhs) ->
            raise (Failure "Phi to SMT is not supported")

    | LabelRef (proc_name, lab_name) ->
            raise (Failure "LabelRef to SMT is not supported")


let var_to_smt_yices var tp =
    let base_type = match tp#basetype with
    | TBIT -> "bool"
    | TBYTE -> "int"
    | TSHORT -> "int"
    | TINT -> "int"
    | TUNSIGNED -> "nat"
    | TCHAN -> raise (Failure "Type chan is not supported")
    | TMTYPE -> raise (Failure "Type mtype is not supported")
    | TPROPOSITION -> raise (Failure "Type proposition is not supported")
    | TUNDEF -> raise (Failure "Undefined type met")
    in
    let complex_type =
        let subtype =
            if tp#has_range
            then let l, r = tp#range in
                sprintf "(subrange %d %d)" l (r - 1)
            else base_type
        in
        if tp#is_array
        then sprintf "(-> (subrange 0 %d) %s)" (tp#nelems - 1) subtype
        else subtype
    in
    sprintf "(define %s :: %s)" var#mangled_name complex_type


let var_to_smtlib2 var tp =
    let l, r = tp#range in
    let rng e = [ BinEx (GE, e, IntConst l); BinEx (LT, e, IntConst r) ] in
    let base_type, cons_f = match tp#basetype with
    | TBIT -> "Bool",
        fun _ -> []

    | TBYTE -> "Int",
        (fun e ->
            if tp#has_range
            then rng e
            else [ BinEx (AND,
                BinEx (GE, e, IntConst 0),
                BinEx (LE, e, IntConst 255))
            ])

    | TSHORT -> "Int", (* TODO: what is the range of short? *)
        (fun e -> if tp#has_range then rng e else [])

    | TINT -> "Int",
        (fun e -> if tp#has_range then rng e else [])

    | TUNSIGNED -> "Int",
        (fun e -> if tp#has_range then rng e else [ BinEx (GE, e, IntConst 0) ])

    | TCHAN -> raise (Failure "Type chan is not supported")
    | TMTYPE -> raise (Failure "Type mtype is not supported")
    | TPROPOSITION -> raise (Failure "Type proposition is not supported")
    | TUNDEF -> raise (Failure "Undefined type met")
    in
    let decl =
        if tp#is_array
        then sprintf "(declare-fun %s () (Array Int %s))" var#mangled_name base_type
        else sprintf "(declare-fun %s () %s)" var#mangled_name base_type
    in
    let acc i = BinEx (ARR_ACCESS, Var var, IntConst i) in
    let cons =
        if not tp#is_array
        then cons_f (Var var)
        else List.concat
            (List.map (fun i -> cons_f (acc i)) (Accums.range 0 tp#nelems))
    in
    decl :: (List.map (fun e -> sprintf "(assert %s)" (expr_to_smt2 e)) cons)


let parse_smt_model_q query lines =
    let var_re =
        Str.regexp
            "(= \\([_a-zA-Z][_a-zA-Z0-9]*\\) \\([-0-9]+\\|false\\|true\\))"
    in
    let arr_re =
        Str.regexp "(= (\\([_a-zA-Z][_a-zA-Z0-9]*\\) \\([0-9]+\\)) \\([-0-9]+\\))"
    in
    let alias_re =
        Str.regexp ("(= \\([_a-zA-Z][_a-zA-Z0-9]*\\) \\([_a-zA-Z][_a-zA-Z0-9]*\\))")
    in
    let aliases = Hashtbl.create 5 in
    let add_alias origin alias = Hashtbl.add aliases origin alias in
    let get_aliases origin = Hashtbl.find_all aliases origin in

    let parse_val = function
        | "false" -> 0
        | "true" -> 1
        | _ as s -> int_of_string s
    in

    let parse_line newq line =
        if Str.string_match var_re line 0
        then begin
            (* e.g., (= x 1) *)
            let variable = Str.matched_group 1 line in
            (* we support ints only, don't we? *)
            let value = parse_val (Str.matched_group 2 line) in
            Q.add_result query newq variable (IntConst value)
        end
        else if Str.string_match arr_re line 0
        then begin
            (* e.g., (= (x 11) 0) *)
            let name = Str.matched_group 1 line in
            let index = int_of_string (Str.matched_group 2 line) in
            let value = parse_val (Str.matched_group 3 line) in

            let mk_access n i = sprintf "(%s %d)" n i in
            let each_alias q alias =
                Q.add_result query q (mk_access alias index) (IntConst value)
            in
            (* the expression *)
            List.fold_left each_alias newq (name :: (get_aliases name)) 
        end else if Str.string_match alias_re line 0
        then begin
            (* (= alias origin) *)
            let alias = Str.matched_group 1 line in
            let origin = Str.matched_group 2 line in
            add_alias origin alias;
            newq
        end else newq
    in
    let new_query = List.fold_left parse_line (Q.copy query) lines in
    { new_query with Q.frozen = true }


(** The interface to the SMT solver (yices).
   We are using the text interface, as it is way easier to debug. *)
class yices_smt (solver_cmd: string) =
    object(self)
        inherit smt_solver

        (* for how long we wait for output from yices if check is issued *)
        val check_timeout_sec = 3600.0
        (* for how long we wait for output from yices if another command is issued*)
        val timeout_sec = 10.0
        val mutable pid = 0
        val mutable clog = stdout
        val mutable m_pipe_cmd = PipeCmd.null ()
        val mutable debug = false
        val mutable m_enable_log = false
        val mutable m_need_unsat_cores = false
        val mutable m_need_evidence = false
        val mutable collect_asserts = false
        val mutable poll_tm_sec = 10.0
        (** the number of stack pushes executed within consistent context *)
        val mutable m_pushes = 0
        (** the number of stack pushes executed within inconsistent context *)
        val mutable m_inconsistent_pushes = 0

        method start =
            assert(PipeCmd.is_null m_pipe_cmd);
            m_pipe_cmd <- PipeCmd.create solver_cmd [||] "yices.err";
            clog <- open_out "yices.log";
            if not m_enable_log
            then begin
                fprintf clog "Logging is disabled by default. Pass -O smt.log=1 to enable it.\n";
                flush clog
            end;
            ignore (self#check);
            self#append "(set-verbosity! 2)\n" (* to track assert+ *)
        
        method stop =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            close_out clog;
            ignore (PipeCmd.destroy m_pipe_cmd);
            m_pipe_cmd <- PipeCmd.null ()

        method reset =
            self#append "(reset)";
            self#sync;
            m_need_evidence <- false;
            collect_asserts <- false;
            m_pushes <- 0;
            m_inconsistent_pushes <- 0

        method append_var_def (v: var) (tp: data_type) =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append (var_to_smt_yices v tp)

        method comment (line: string) =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append (";; " ^ line)

        method append_expr expr =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            let eid = ref 0 in
            let e_s = expr_to_smt expr in
            let is_comment = (String.length e_s) > 1
                    && e_s.[0] = ';' && e_s.[1] = ';' in
            if not is_comment
            then begin 
                if not collect_asserts
                then self#append (sprintf "(assert %s)" e_s)
                else begin
                    (* XXX: may block if the verbosity level < 2 *)
                    self#sync;
                    self#append (sprintf "(assert+ %s)" e_s);
                    let line = self#read_line in
                    if (Str.string_match (Str.regexp "id: \\([0-9]+\\)") line 0)
                    then
                        let id = int_of_string (Str.matched_group 1 line) in
                        eid := id
                end;
                !eid
            end else -1

        method push_ctx =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#sync;
            self#append "(status)"; (* it can be unsat already *)
            if not (self#is_out_sat ~ignore_errors:true)
            then begin
                self#comment "push in inconsistent context. Ignored.";
                m_inconsistent_pushes <- m_inconsistent_pushes + 1
            end else begin
                m_pushes <- m_pushes + 1;
                self#append "(push)"
            end

        (** Get the current stack level (nr. of pushes). Use for debugging *)
        method get_stack_level =
            m_pushes + m_inconsistent_pushes

        method pop_ctx =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            if m_pushes + m_inconsistent_pushes = 0
            then raise (Failure ("pop: yices stack is empty!"));
            if m_inconsistent_pushes > 0
            then begin
                self#comment "pop from inconsistent context.";
                m_inconsistent_pushes <- m_inconsistent_pushes - 1
            end else begin
                m_pushes <- m_pushes - 1;
                self#append "(pop)"
            end


        method check =
            self#sync;
            self#append "(status)"; (* it can be unsat already *)
            if not (self#is_out_sat ~ignore_errors:true)
            then false
            else begin
                self#sync;
                self#append "(check)";
                let res = self#is_out_sat ~ignore_errors:false in
                res
            end

        (** set incremental mode *)
        method set_incremental_mode (_: bool) = ()

        (** is the incremental mode on? *)
        method get_incremental_mode = true

        method set_need_model b =
            m_need_evidence <- b;
            if b
            then self#append "(set-evidence! true)"
            else self#append "(set-evidence! false)"

        method get_need_model = m_need_evidence

        method set_need_unsat_cores b =
            (* nothing to do in yices *)
            m_need_unsat_cores <- b

        method get_need_unsat_cores = m_need_unsat_cores
            
        method get_model_query = Q.new_query expr_to_smt

        method submit_query (query: Q.query_t) =
            (* same as sync but the lines are collected *)
            let lines = ref [] in
            self#append "(echo \"EOEV\\n\")";
            let stop = ref false in
            while not !stop do
                let line = self#read_line in
                if "EOEV" = line
                then stop := true
                else lines := line :: !lines
            done;
            parse_smt_model_q query (List.rev !lines)

        method get_collect_asserts = collect_asserts

        method set_collect_asserts b = collect_asserts <- b

        method set_enable_lockstep (_: bool) = ()

        method get_enable_lockstep = true

        method set_enable_log b = m_enable_log <- b

        method get_enable_log = m_enable_log

        method get_unsat_cores =
            (* collect unsatisfiable cores *)
            let re = Str.regexp ".*unsat core ids: \\([ 0-9]+\\).*" in
            let cores = ref [] in
            self#append "(echo \"EOI\\n\")\n";
            let stop = ref false in
            while not !stop do
                let line = self#read_line in
                if Str.string_match re line 0
                then begin
                    let id_str = (Str.matched_group 1 line) in
                    let ids_as_str = (Str.split (Str.regexp " ") id_str) in
                    cores := (List.map int_of_string ids_as_str)
                end;

                stop := (line = "EOI")
            done;
            !cores

        method set_debug flag = debug <- flag

        method private is_out_sat ~ignore_errors =
            let l = self#read_line in
            match l with
            | "sat" -> true
            | "ok" -> true
            | "unsat" -> false
            | "unsupported" -> raise (Smt_error "unsupported expression")
            | _ -> if ignore_errors
                then false
                else raise (Smt_error (sprintf "yices: %s" l))

        method private read_line =
            assert (not (PipeCmd.is_null m_pipe_cmd));
            let out = PipeCmd.readline m_pipe_cmd in
            if m_enable_log
            then begin
                fprintf clog ";; READ: %s\n" out; flush clog;
            end;
            trace Trc.smt (fun _ -> sprintf "YICES: ^^^%s$$$\n" out);
            out

        method private append cmd =
            assert (not (PipeCmd.is_null m_pipe_cmd));
            if debug then printf "%s\n" cmd;
            self#write_line (sprintf "%s" cmd);
            if m_enable_log
            then begin
                fprintf clog "%s\n" cmd; flush clog
            end

        method private append_assert s =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append (sprintf "(assert %s)" s)

        method private write_line s =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            writeline m_pipe_cmd s

        method private sync =
            (* the solver can print more messages, thus, sync! *)
            self#append "(echo \"sync\\n\")";
            let stop = ref false in
            while not !stop do
                if "sync" = self#read_line then stop := true
            done
    end


(**
    An interface to a solver supporting SMTLIB2. This class invokes a solver
    and communicates with it via pipes.

    Logging to a file is disabled by default. If you want to enable it,
    pass the argument -O smt.log=1.
*)
class lib2_smt solver_cmd solver_args =
    object(self)
        inherit smt_solver

        (* for how long we wait for output from yices if check is issued *)
        val check_timeout_sec = 3600.0
        (* for how long we wait for output from yices if another command is issued*)
        val timeout_sec = 10.0
        val mutable pid = 0
        val mutable clog = stdout
        val mutable m_pipe_cmd = PipeCmd.null ()
        val mutable debug = false
        val mutable m_enable_log = false
        val mutable m_enable_lockstep = false
        val mutable m_need_evidence = false
        val mutable m_need_unsat_cores = false
        val mutable m_incremental = false
        val mutable collect_asserts = false
        val mutable poll_tm_sec = 10.0
        (** the number of stack pushes executed within consistent context *)
        val mutable m_pushes = 0
        (** the number of stack pushes executed within inconsistent context *)
        val mutable m_inconsistent_pushes = 0
        (** the last id used in the assertions *)
        val mutable m_last_id = 1
        (** the number of times the solver has been started *)
        val mutable m_nstarts = 0

        method start =
            let args_s = BatArray.fold_left (fun a s -> a ^ " " ^ s) "" solver_args in
            Debug.logtm Debug.INFO
                (sprintf "Starting the SMT solver: %s%s" solver_cmd args_s);
            assert(PipeCmd.is_null m_pipe_cmd);
            let errname =
                if m_nstarts = 0 then "smt2.err" else (sprintf "smt2.%d.err" m_nstarts) in
            m_pipe_cmd <- PipeCmd.create solver_cmd solver_args errname;
            let outname =
                if m_nstarts = 0 then "smt2.log" else (sprintf "smt2.%d.log" m_nstarts) in
            clog <- open_out outname;
            if not m_enable_log
            then begin
                fprintf clog "Logging is disabled by default. Pass -O smt.log=1 to enable it.\n";
                flush clog
            end;
            if m_enable_lockstep
            then self#append_and_sync "(set-option :print-success true)\n"
            else self#append_and_sync "(set-option :print-success false)\n";

            (*self#append_and_sync "(set-logic QF_UFLIA)\n";*)

            if m_need_unsat_cores
            then self#append_and_sync "(set-option :produce-unsat-cores true)\n";

            self#append_and_sync "(set-option :produce-models true)";
            (* z3 scoping is incompatible by default with the one of smtlib2:
                http://stackoverflow.com/questions/13473787/z3-with-smtlib2-input
              *)
            if BatString.exists solver_cmd "z3"
            then begin
                self#comment "a Z3 hack follows\n";
                self#append_and_sync "(set-option :global-decls false)\n";
                if not m_incremental
                then self#append_and_sync "(set-option :interactive-mode false)\n"
            end;
            if m_incremental
            then self#push_ctx; (* a backup context to reset *)
            m_nstarts <- m_nstarts + 1

        
        method stop =
            Debug.logtm Debug.INFO ("Stopping the SMT solver...");
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append "(exit)\n";
            self#sync;
            close_out clog;
            ignore (PipeCmd.destroy m_pipe_cmd);
            m_pipe_cmd <- PipeCmd.null ()

        method reset =
            self#comment "***************** RESET *****************\n";
            if m_incremental
            then self#pop_n m_pushes
            else self#append_and_sync "(reset)\n";
            m_need_evidence <- false;
            collect_asserts <- false;
            m_pushes <- 0;
            m_inconsistent_pushes <- 0;
            if m_incremental
            then self#push_ctx

        method append_var_def (v: var) (tp: data_type) =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            let exprs = var_to_smtlib2 v tp in
            List.iter (fun e -> self#append_and_sync e) exprs

        method comment (line: string) =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append (";; " ^ line)

        method append_expr expr =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            let e_s = expr_to_smt2 expr in
            let is_comment =
                (String.length e_s) > 1 && e_s.[0] = ';' && e_s.[1] = ';'
            in
            if not is_comment
            then begin 
                if not collect_asserts
                then begin
                    self#append_and_sync (sprintf "(assert %s)" e_s);
                    -1
                end else begin
                    let id = m_last_id in
                    self#append_and_sync
                        (sprintf "(assert (! %s :named _E%d))" e_s id);
                    m_last_id <- m_last_id + 1;
                    id
                end;
            end else -1

        method push_ctx =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            m_incremental <- true;
            m_pushes <- m_pushes + 1;
            self#append "(push 1)";
            self#sync

        (** Get the current stack level (nr. of pushes). Use for debugging *)
        method get_stack_level =
            m_pushes + m_inconsistent_pushes

        method pop_ctx =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            m_pushes <- m_pushes - 1;
            self#append_and_sync "(pop 1)"

        method private pop_n n =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            m_pushes <- m_pushes - n;
            self#append_and_sync (sprintf "(pop %d)" n)

        method check =
            self#append "(check-sat)";
            let res = self#is_out_sat ~ignore_errors:false in
            res

        method set_need_model b =
            m_need_evidence <- b
            (* the option is set in #start, as many solvers require us to set
               the options before doing anything *)

        method get_need_model = m_need_evidence

        method set_need_unsat_cores b =
            (* the option is set in #start, as many solvers require us to set
               the options before doing anything *)
            m_need_unsat_cores <- b

        method get_need_unsat_cores = m_need_unsat_cores
            
        method get_model_query = Q.new_query expr_to_smt2

        method submit_query (query: Q.query_t) =
            let str = Hashtbl.fold (fun e_s _ s -> s ^ " " ^ e_s) query.Q.tab "" in
            self#append (sprintf "(get-value (%s))" str);
            let new_q = Q.new_query query.Q.expr_to_smt_f in
            let opened, closed = ref 0, ref 0 in
            let buf = ref "" in
            let cnt_braces b s =
                BatString.fold_left (fun n c -> if c = b then n + 1 else n) 0 s
            in
            while !opened = 0 || !opened <> !closed do
                let line = self#read_line in
                opened := !opened + (cnt_braces '(' line);
                closed := !closed + (cnt_braces ')' line);
                buf := !buf ^ line;
            done;

            let parse_val = function
                | "false" -> 0
                | "true" -> 1
                | _ as s -> int_of_string s
            in
            let parse_elem = function
                | Sexp.List [_ as key_sexp; Sexp.Atom val_s] ->
                        let key = Sexp.to_string key_sexp in
                        let value = parse_val val_s in
                        ignore (Q.add_result query new_q key (IntConst value))
                
                | _ as s ->
                        raise (Smt_error
                            ("Unexpected pair: " ^ (Sexp.to_string s)))
            in
            let parse = function
                | Sexp.List l ->
                        List.iter parse_elem l

                | _ -> raise (Smt_error ("Unexpected model: " ^ !buf))
            in
            parse (Sexp.of_string !buf);
            new_q

        method get_collect_asserts = collect_asserts

        method set_collect_asserts b = collect_asserts <- b

        method get_unsat_cores =
            (* collect unsatisfiable cores *)
            let re = Str.regexp "_E\\([0-9]+\\)" in
            let cores = ref [] in
            self#append "(get-unsat-core)\n";
            let stop = ref false in

            while not !stop do
                let line = self#read_line in
                let start = ref 0 in
                begin
                    try
                        while true do
                            let _ = search_forward re line !start in
                            let id = int_of_string (Str.matched_group 1 line) in
                            cores := id :: !cores;
                            start := 1 + (match_end ())
                        done
                    with Not_found -> ()
                end;

                stop := String.contains line ')'
            done;
            !cores

        method set_debug flag = debug <- flag

        method set_enable_lockstep b = m_enable_lockstep <- b

        method get_enable_lockstep = m_enable_lockstep

        method set_enable_log b = m_enable_log <- b

        method get_enable_log = m_enable_log

        method set_incremental_mode b =
            if not (PipeCmd.is_null m_pipe_cmd) && b <> m_incremental
            then begin
                let v = (if b then "true" else "false") in
                self#append_and_sync (sprintf "(set-option :interactive-mode %s)\n" v);
            end;
            m_incremental <- b


        method get_incremental_mode = m_incremental

        method private is_out_sat ~ignore_errors =
            let l = self#read_line in
            (*printf "%s\n" l;*)
            match l with
            | "sat" -> true
            | "unsat" -> false
            | "unknown" -> raise (Smt_error "unknown result")
            | _ -> if ignore_errors
                then false
                else raise (Smt_error (sprintf "solver: %s" l))

        method private read_line =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            let out = PipeCmd.readline m_pipe_cmd in
            if m_enable_log
            then begin
                fprintf clog ";; READ: %s\n" out; flush clog;
            end;
            trace Trc.smt (fun _ -> sprintf "SMT2: ^^^%s$$$\n" out);
            try
                if "(error " = (Str.string_before out 7)
                then raise (Smt_error out)
                else out
            with Invalid_argument _ ->
                out

        method private append cmd =
            assert (not (PipeCmd.is_null m_pipe_cmd));
            self#write_line cmd;
            if debug then printf "%s\n" cmd;
            if m_enable_log
            then begin
                fprintf clog "%s\n" cmd;
                flush clog
            end

        method private append_and_sync cmd =
            self#append cmd;
            self#sync

        method private append_assert s =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            self#append (sprintf "(assert %s)" s)

        method private write_line s =
            assert(not (PipeCmd.is_null m_pipe_cmd));
            writeline m_pipe_cmd s

        method private sync =
            (*
             NOTE: if you want to synchronize with the solver in a lock-step
             *)
            if m_enable_lockstep
            then begin
                let stop = ref false in
                while not !stop do
                    let line = self#read_line in
                    if "success" = line
                    then stop := true;
                    if "unsupported" = line
                    then raise (Failure "got unsupported")
                done
            end
    end


(**
    An interface to Mathsat5 via Mathsat's library.
    This class requires the mathsat4ml plugin compiled in plugins/mathsat4ml

    Logging to a file is disabled by default. If you want to enable it,
    pass the option -O smt.log=1
*)
class mathsat5_smt =
    object(self)
        inherit smt_solver

        val mutable m_instance = -1

        val mutable clog = stdout
        val mutable m_enable_log = false
        val mutable m_need_unsat_cores = false
        (** the number of stack pushes executed within consistent context *)
        val mutable m_pushes = 0

        method start =
            m_instance <- (!Msat.p_create) ();
            clog <- open_out "smt2.log";
            if not m_enable_log
            then begin
                fprintf clog "Logging is disabled by default. Pass -O smt.log=1 to enable it.\n";
                flush clog
            end else begin
                fprintf clog "(set-option :produce-unsat-cores true)\n";
                fprintf clog "(set-option :produce-models true)\n";
            end;
            self#push_ctx (* a backup context to reset *)
        
        method stop =
            ignore ((!Msat.p_destroy) m_instance);
            close_out clog

        method reset =
            (* TODO: it should be implemented differently *)
            self#pop_n m_pushes;
            m_pushes <- 0;
            self#push_ctx

        method append_var_def (v: var) (tp: data_type) =
            if m_enable_log
            then begin
                List.iter (fun s -> fprintf clog "%s\n" s) (var_to_smtlib2 v tp);
                flush clog
            end;
            if tp#is_array
            then raise (Smt_error "Arrays are not supported yet");
            (!Msat.p_declare_int) m_instance v#mangled_name;
            if tp#has_range
            then begin let l, r = tp#range in
                ignore (self#append_expr (BinEx (GE, Var v, IntConst l)));
                ignore (self#append_expr (BinEx (LT, Var v, IntConst r)));
            end else
                match tp#basetype with
                | SpinTypes.TINT ->
                    ()

                | SpinTypes.TUNSIGNED ->
                    ignore (self#append_expr (BinEx (GE, Var v, IntConst 0)))

                | SpinTypes.TBYTE ->
                    ignore (self#append_expr (BinEx (GE, Var v, IntConst 0)));
                    ignore (self#append_expr (BinEx (LT, Var v, IntConst 256)))

                | _ as t ->
                    raise (Smt_error
                        ((SpinTypes.var_type_s t) ^ " is not supported"))

        method comment (line: string) =
            if m_enable_log
            then begin
                fprintf clog ";; %s\n" line;
                flush clog
            end

        method append_expr expr =
            let exp_s = expr_to_smt2 expr in
            if m_enable_log
            then begin
                fprintf clog "(assert %s)\n" exp_s;
                flush clog
            end;
            (!Msat.p_assert) m_instance exp_s

        method push_ctx =
            if m_enable_log
            then begin
                fprintf clog "(push 1)\n";
                flush clog
            end;
            m_pushes <- m_pushes + 1;
            (!Msat.p_push) m_instance;

        (** Get the current stack level (nr. of pushes). Use for debugging *)
        method get_stack_level =
            m_pushes

        method pop_ctx =
            assert (m_pushes > 0);
            if m_enable_log
            then begin
                fprintf clog "(pop 1)\n";
                flush clog
            end;
            m_pushes <- m_pushes - 1;
            (!Msat.p_pop) m_instance

        method private pop_n n =
            BatEnum.iter (fun _ -> self#pop_ctx) (0--^n)

        method check =
            if m_enable_log
            then begin
                fprintf clog "(check-sat)\n";
                flush clog
            end;
            match (!Msat.p_solve) m_instance with
            | 0 -> false
            | 1 -> true
            | _ -> raise (Smt_error "Smt solver returned unknown")

        method set_need_model _ = ()

        method get_need_model = true

        method set_need_unsat_cores b =
            (* nothing to do *)
            m_need_unsat_cores <- b

        method get_need_unsat_cores = m_need_unsat_cores
            
        method get_model_query = Q.new_query expr_to_smt2

        method submit_query (query: Q.query_t) =
            let new_q = Q.new_query query.Q.expr_to_smt_f in
            let each_exp exp_s _ =
                if m_enable_log
                then begin
                    fprintf clog "(get-value (%s))\n" exp_s;
                    flush clog
                end;
                let val_s = (!Msat.p_get_model_value) m_instance exp_s in
                if m_enable_log
                then begin
                    fprintf clog ";; %s\n" val_s;
                    flush clog
                end;
                let value = 
                    try int_of_string val_s
                    with Failure _ ->
                        raise (Failure (sprintf "Cannot convert %s to int" val_s))
                in
                ignore (Q.add_result query new_q exp_s (IntConst value))
            in
            Hashtbl.iter each_exp query.Q.tab;
            new_q

        method get_collect_asserts = true

        method set_collect_asserts _ = ()

        method get_unsat_cores =
            raise (Failure "get_unsat_cores is not implemented yet")

        method set_debug flag = ()

        method set_enable_lockstep _ = ()

        method get_enable_lockstep = false

        method set_enable_log b = m_enable_log <- b

        method get_enable_log = m_enable_log

        method set_incremental_mode (_: bool) = ()

        method get_incremental_mode = true
    end

